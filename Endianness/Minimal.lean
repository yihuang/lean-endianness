import Endianness.ByteArray

/-!
# Endianness.Minimal

Minimal-length big-endian encoding: the shortest byte string that decodes back
to `n`, as opposed to the fixed-width codecs of `Endianness.Core`.

This is the convention used for EVM/ABI integer encoding, where `0` is
represented by a single zero byte rather than the empty string.

* `minBytes n` — the width, `Nat.log2 n / 8 + 1` (and `1` at `n = 0`)
* `encodeBEMin` / `encodeBEMinU` / `encodeBEMinBytes` — the three layers
* `minBytes_spec` — minimality: `minBytes n` is the LEAST positive width
  that fits `n`
* `decodeBE_encodeBEMin` and friends — roundtrips at each layer

Everything is built on the fixed-width codecs at width `minBytes n`, so the
fixed-width theory applies verbatim. Core library only — no mathlib.
-/

namespace Endianness

/-! ## The minimal width -/

/-- Bytes needed for the minimal big-endian encoding of `n`.

    `0` takes one byte, matching the EVM convention that the zero word encodes
    as a single `0x00` rather than the empty byte string. -/
def minBytes : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1).log2 / 8 + 1

theorem minBytes_pos (n : Nat) : 0 < minBytes n := by
  cases n with
  | zero => decide
  | succ k => simp [minBytes]

/-- `n` fits in `minBytes n` bytes — the defining upper bound. -/
theorem lt_pow_minBytes (n : Nat) : n < 256 ^ minBytes n := by
  cases n with
  | zero => decide
  | succ k =>
    have hne : k + 1 ≠ 0 := by omega
    have hlt2 : k + 1 < 2 ^ ((k + 1).log2 + 1) := (Nat.log2_lt hne).mp (by omega)
    have hmono : (2 : Nat) ^ ((k + 1).log2 + 1) ≤ 2 ^ (8 * ((k + 1).log2 / 8 + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h256 : (256 : Nat) ^ ((k + 1).log2 / 8 + 1) = 2 ^ (8 * ((k + 1).log2 / 8 + 1)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    show k + 1 < 256 ^ ((k + 1).log2 / 8 + 1)
    rw [h256]; omega

/-- `minBytes n` is at most any positive width that fits `n`. -/
theorem minBytes_le_of_lt {n len : Nat} (h : n < 256 ^ len) (hlen : 0 < len) :
    minBytes n ≤ len := by
  cases n with
  | zero => show 1 ≤ len; omega
  | succ k =>
    have hne : k + 1 ≠ 0 := by omega
    have h2 : k + 1 < 2 ^ (8 * len) := by
      rwa [show (256 : Nat) ^ len = 2 ^ (8 * len) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]] at h
    have hlog : (k + 1).log2 < 8 * len := (Nat.log2_lt hne).mpr h2
    have : (k + 1).log2 / 8 < len := Nat.div_lt_of_lt_mul (by omega)
    show (k + 1).log2 / 8 + 1 ≤ len
    omega

/-- **Minimality**: `minBytes n` is the LEAST positive width that fits `n`.

    Together with `lt_pow_minBytes` (the width works) this pins `minBytes`
    down completely: it is exactly the least `len > 0` with `n < 256 ^ len`. -/
theorem minBytes_spec {n len : Nat} (hlen : 0 < len) : n < 256 ^ len ↔ minBytes n ≤ len := by
  constructor
  · intro h; exact minBytes_le_of_lt h hlen
  · intro h
    exact Nat.lt_of_lt_of_le (lt_pow_minBytes n) (Nat.pow_le_pow_right (by omega) h)

/-- The exact width of `n` from a two-sided bit-length bound. -/
theorem minBytes_eq_of_range {n k : Nat} (hk : 0 < k)
    (hlo : 2 ^ (k * 8 - 1) ≤ n) (hhi : n < 2 ^ (k * 8)) : minBytes n = k := by
  have hup : minBytes n ≤ k :=
    minBytes_le_of_lt (by rwa [show (256 : Nat) ^ k = 2 ^ (k * 8) by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.mul_comm]]) hk
  rcases Nat.lt_or_ge (minBytes n) k with hlt | hge
  · exfalso
    have h1 : n < 256 ^ minBytes n := lt_pow_minBytes n
    have h2 : (256 : Nat) ^ minBytes n ≤ 2 ^ (k * 8 - 1) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · omega

/-- `minBytes` obeys the base-256 recursion — derived from the minimality spec above,
    with no `log2` reasoning. This is the shape a caller's own recursive width function
    will have, so it is what lets such a function be identified with `minBytes`. -/
theorem minBytes_div {n : Nat} (h : 256 ≤ n) : minBytes n = minBytes (n / 256) + 1 := by
  have hdpos : 0 < minBytes (n / 256) := minBytes_pos _
  apply Nat.le_antisymm
  · have h1 : n / 256 < 256 ^ minBytes (n / 256) := lt_pow_minBytes _
    have hp : (256 : Nat) ^ (minBytes (n / 256) + 1) = 256 * 256 ^ minBytes (n / 256) := by
      rw [Nat.pow_succ]; omega
    have hgoal : n < 256 ^ (minBytes (n / 256) + 1) := by omega
    exact minBytes_le_of_lt hgoal (by omega)
  · have hlt : n < 256 ^ minBytes n := lt_pow_minBytes n
    have hpos := minBytes_pos n
    have hk : 2 ≤ minBytes n := by
      rcases Nat.lt_or_ge (minBytes n) 2 with hc | hc
      · exfalso
        have h1 : minBytes n = 1 := by omega
        rw [h1, Nat.pow_one] at hlt
        omega
      · exact hc
    obtain ⟨j, hj⟩ : ∃ j, minBytes n = j + 1 := ⟨minBytes n - 1, by omega⟩
    rw [hj] at hlt
    have hp : (256 : Nat) ^ (j + 1) = 256 * 256 ^ j := by rw [Nat.pow_succ]; omega
    have hdiv : n / 256 < 256 ^ j := by omega
    have hle := minBytes_le_of_lt hdiv (by omega)
    omega

/-- Below 256, one byte suffices — the recursion's base case. -/
theorem minBytes_eq_one {n : Nat} (h : n < 256) : minBytes n = 1 := by
  have hpos := minBytes_pos n
  rcases Nat.lt_or_ge (minBytes n) 2 with hc | hc
  · omega
  · exfalso
    have := minBytes_le_of_lt (show n < 256 ^ 1 by rw [Nat.pow_one]; omega) (by omega)
    omega

/-! ## The codecs -/

/-- Minimal-length big-endian encoding over `List Nat`. -/
def encodeBEMin (n : Nat) : List Nat := encodeBE (minBytes n) n

/-- Minimal-length big-endian encoding over `List UInt8`. -/
def encodeBEMinU (n : Nat) : List UInt8 := encodeBEU (minBytes n) n

/-- Minimal-length big-endian encoding over `ByteArray`. -/
def encodeBEMinBytes (n : Nat) : ByteArray := encodeBEBytes (minBytes n) n

/-! ## Lengths -/

@[simp] theorem length_encodeBEMin (n : Nat) : (encodeBEMin n).length = minBytes n := by
  simp [encodeBEMin]

@[simp] theorem length_encodeBEMinU (n : Nat) : (encodeBEMinU n).length = minBytes n := by
  simp [encodeBEMinU]

@[simp] theorem size_encodeBEMinBytes (n : Nat) : (encodeBEMinBytes n).size = minBytes n := by
  simp [encodeBEMinBytes]

/-- The minimal encoding is a valid byte string. -/
theorem isBytes_encodeBEMin (n : Nat) : IsBytes (encodeBEMin n) := isBytes_encodeBE

/-! ## Roundtrips -/

/-- **Roundtrip (`List Nat`)**: the minimal encoding decodes back — no side
    condition, unlike the fixed-width codec, since the width is chosen to fit. -/
theorem decodeBE_encodeBEMin (n : Nat) : decodeBE (encodeBEMin n) = n :=
  decodeBE_encodeBE (lt_pow_minBytes n)

/-- **Roundtrip (`List UInt8`)**. -/
theorem decodeBEU_encodeBEMinU (n : Nat) : decodeBEU (encodeBEMinU n) = n :=
  decodeBEU_encodeBEU (lt_pow_minBytes n)

/-- **Roundtrip (`ByteArray`)**. -/
theorem decodeBEBytes_encodeBEMinBytes (n : Nat) : decodeBEBytes (encodeBEMinBytes n) = n :=
  decodeBEBytes_encodeBEBytes (lt_pow_minBytes n)

/-- The minimal encoding is injective. -/
theorem encodeBEMin_injective {m n : Nat} (h : encodeBEMin m = encodeBEMin n) : m = n := by
  have := congrArg decodeBE h
  rwa [decodeBE_encodeBEMin, decodeBE_encodeBEMin] at this

end Endianness
