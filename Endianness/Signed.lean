import Endianness.ByteArray

/-!
# Endianness.Signed

Two's-complement big-endian codecs — the signed counterpart to `Endianness.Core`'s
unsigned fixed-width ones, and the convention EVM/ABI signed integers use.

* `twosRep len v` — the unsigned representative of `v` in `len`-byte two's complement
* `InTwosRange len v` — representability: `-256^len ≤ 2v < 256^len`, i.e. the usual
  `[-2^(8len-1), 2^(8len-1))` stated without a truncating `- 1` in the exponent
* `encodeTwosBE` / `encodeTwosBEU` / `encodeTwosBEBytes` — the three layers
* `decodeTwosBE` / `decodeTwosBEU` / `decodeTwosBEBytes` — likewise
* `decodeTwosBE_encodeTwosBE` and friends — roundtrips, given `InTwosRange`

The encoding is the fixed-width unsigned one applied to `twosRep`, so the unsigned
theory carries over. `InTwosRange` is genuinely required: out of range the encoding
wraps (`decodeTwosBE (encodeTwosBE 1 129) = -127`), so it is not a decorative
hypothesis.

Core library only — no mathlib. The `Int` arithmetic is discharged by `omega` over
`Int.toNat_of_nonneg`.
-/

namespace Endianness

/-! ## Representative and range -/

/-- The unsigned representative of `v` in `len`-byte two's complement:
    non-negative values as themselves, negative ones offset by `256^len`. -/
def twosRep (len : Nat) (v : Int) : Nat :=
  if 0 ≤ v then v.toNat else ((256 ^ len : Nat) + v).toNat

/-- `v` is representable in `len`-byte two's complement. Equivalent to the usual
    `-2^(8len-1) ≤ v < 2^(8len-1)`, but stated as `-256^len ≤ 2v < 256^len` so that
    no truncating subtraction appears in an exponent. -/
def InTwosRange (len : Nat) (v : Int) : Prop :=
  -((256 ^ len : Nat) : Int) ≤ 2 * v ∧ 2 * v < ((256 ^ len : Nat) : Int)

/-- Representability is decidable, so callers can discharge the roundtrips'
    hypothesis with `by decide` on concrete values rather than building the
    conjunction by hand. -/
instance (len : Nat) (v : Int) : Decidable (InTwosRange len v) := by
  unfold InTwosRange; infer_instance

/-- In range, the representative fits in `len` bytes — what makes the unsigned
    encoder applicable. -/
theorem twosRep_lt (len : Nat) (v : Int) (h : InTwosRange len v) :
    twosRep len v < 256 ^ len := by
  obtain ⟨hlo, hhi⟩ := h
  have hP : (0 : Int) ≤ ((256 ^ len : Nat) : Int) := Int.natCast_nonneg _
  unfold twosRep
  split
  · rename_i hv
    have : ((v.toNat : Nat) : Int) = v := Int.toNat_of_nonneg hv
    omega
  · rename_i hv
    have hnn : (0 : Int) ≤ ((256 ^ len : Nat) : Int) + v := by omega
    have : ((((256 ^ len : Nat) : Int) + v).toNat : Int) = ((256 ^ len : Nat) : Int) + v :=
      Int.toNat_of_nonneg hnn
    omega

/-! ## The codecs -/

/-- Two's-complement big-endian encoding in `len` bytes, over `List Nat`. -/
def encodeTwosBE (len : Nat) (v : Int) : List Nat := encodeBE len (twosRep len v)

/-- Two's-complement big-endian decoding: the leading bit selects the sign. -/
def decodeTwosBE (bs : List Nat) : Int :=
  let u := decodeBE bs
  if 2 * u < 256 ^ bs.length then (u : Int) else (u : Int) - ((256 ^ bs.length : Nat) : Int)

/-- `List UInt8` layer. -/
def encodeTwosBEU (len : Nat) (v : Int) : List UInt8 := natsToUInt8 (encodeTwosBE len v)

/-- `List UInt8` layer. -/
def decodeTwosBEU (bs : List UInt8) : Int := decodeTwosBE (uint8ToNats bs)

/-- `ByteArray` layer. -/
def encodeTwosBEBytes (len : Nat) (v : Int) : ByteArray := (encodeTwosBEU len v).toByteArray

/-- `ByteArray` layer. -/
def decodeTwosBEBytes (ba : ByteArray) : Int := decodeTwosBEU ba.data.toList

/-! ## Lengths -/

@[simp] theorem length_encodeTwosBE (len : Nat) (v : Int) :
    (encodeTwosBE len v).length = len := by simp [encodeTwosBE]

@[simp] theorem length_encodeTwosBEU (len : Nat) (v : Int) :
    (encodeTwosBEU len v).length = len := by simp [encodeTwosBEU, natsToUInt8]

@[simp] theorem size_encodeTwosBEBytes (len : Nat) (v : Int) :
    (encodeTwosBEBytes len v).size = len := by
  show (encodeTwosBEU len v).toByteArray.size = len
  rw [ByteArray.size_eq_toList_length, List.data_toByteArray, List.toList_toArray,
    length_encodeTwosBEU]

/-- The two's-complement encoding is the unsigned encoding of the representative. -/
theorem encodeTwosBEBytes_eq (len : Nat) (v : Int) :
    encodeTwosBEBytes len v = encodeBEBytes len (twosRep len v) := rfl

/-! ## Roundtrips -/

/-- **Roundtrip (`List Nat`)**: two's-complement decode after encode is the identity,
    for representable `v`. -/
theorem decodeTwosBE_encodeTwosBE {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBE (encodeTwosBE len v) = v := by
  obtain ⟨hlo, hhi⟩ := h
  have hu : decodeBE (encodeTwosBE len v) = twosRep len v :=
    decodeBE_encodeBE (twosRep_lt len v ⟨hlo, hhi⟩)
  unfold decodeTwosBE
  simp only [hu, length_encodeTwosBE]
  unfold twosRep
  split
  · rename_i hv
    have hcast : ((v.toNat : Nat) : Int) = v := Int.toNat_of_nonneg hv
    have hlt : 2 * v.toNat < 256 ^ len := by omega
    simp only [if_pos hlt]; omega
  · rename_i hv
    have hnn : (0 : Int) ≤ ((256 ^ len : Nat) : Int) + v := by omega
    have hcast : ((((256 ^ len : Nat) : Int) + v).toNat : Int) = ((256 ^ len : Nat) : Int) + v :=
      Int.toNat_of_nonneg hnn
    have hnot : ¬ (2 * (((256 ^ len : Nat) : Int) + v).toNat < 256 ^ len) := by omega
    simp only [if_neg hnot]; omega

/-- **Roundtrip (`List UInt8`)**. -/
theorem decodeTwosBEU_encodeTwosBEU {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBEU (encodeTwosBEU len v) = v := by
  show decodeTwosBE (uint8ToNats (natsToUInt8 (encodeBE len (twosRep len v)))) = v
  rw [uint8ToNats_natsToUInt8 isBytes_encodeBE]
  exact decodeTwosBE_encodeTwosBE h

/-- **Roundtrip (`ByteArray`)**. -/
theorem decodeTwosBEBytes_encodeTwosBEBytes {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBEBytes (encodeTwosBEBytes len v) = v := by
  show decodeTwosBEU (encodeTwosBEU len v).toByteArray.data.toList = v
  rw [List.data_toByteArray, List.toList_toArray, decodeTwosBEU_encodeTwosBEU h]

/-- The signed encoding is injective on representable values. -/
theorem encodeTwosBE_injective {len : Nat} {m n : Int}
    (hm : InTwosRange len m) (hn : InTwosRange len n)
    (h : encodeTwosBE len m = encodeTwosBE len n) : m = n := by
  have := congrArg decodeTwosBE h
  rwa [decodeTwosBE_encodeTwosBE hm, decodeTwosBE_encodeTwosBE hn] at this

end Endianness
