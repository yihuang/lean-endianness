import Endianness.UInt8

/-!
# Endianness.UInt256

A 256-bit unsigned integer type (the EVM word size), implemented as a wrapper
around Lean core's `BitVec 256` — mirroring how `UInt8` … `UInt64` are
implemented in core — together with the usual fixed-width endianness codec
(32 bytes) and its roundtrip theorems.

Contents:

* the type `UInt256` with `ofNat` / `toNat`, numerals, equality, `Repr`,
  and wrap-around arithmetic / bitwise operations inherited from `BitVec 256`;
* the bridge lemmas `toNat_lt`, `toNat_ofNat`, `toNat_inj`, `ofNat_toNat`;
* the byte codec `toBEBytes` / `toLEBytes` / `ofBEBytes` / `ofLEBytes`
  with the four roundtrip theorems.
-/

namespace Endianness

/-- A 256-bit unsigned integer. Wrap-around semantics modulo `2^256`. -/
structure UInt256 where
  /-- The underlying bit vector. -/
  toBitVec : BitVec 256
  deriving DecidableEq

namespace UInt256

/-- Wrap-around constructor from a natural number (`n mod 2^256`). -/
def ofNat (n : Nat) : UInt256 := ⟨BitVec.ofNat 256 n⟩

/-- The value as a natural number. -/
def toNat (x : UInt256) : Nat := x.toBitVec.toNat

/-- The modulus `2^256`. -/
def size : Nat := 2 ^ 256

/-! ## Bridge lemmas between `ofNat` and `toNat` -/

theorem toNat_lt (x : UInt256) : x.toNat < 2 ^ 256 := x.toBitVec.isLt

theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % 2 ^ 256 :=
  BitVec.toNat_ofNat ..

theorem toNat_inj {x y : UInt256} : x.toNat = y.toNat ↔ x = y := by
  cases x with | mk a =>
  cases y with | mk b =>
  show (a.toNat = b.toNat) ↔ (UInt256.mk a = UInt256.mk b)
  rw [BitVec.toNat_inj]
  constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt256.toBitVec h

theorem ofNat_toNat (x : UInt256) : ofNat x.toNat = x := by
  apply toNat_inj.mp
  rw [toNat_ofNat, Nat.mod_eq_of_lt x.toNat_lt]

/-- The bound in the `256 ^ 32` form used by the byte-codec layer. -/
theorem toNat_lt_256 (x : UInt256) : x.toNat < 256 ^ 32 := by
  have h := x.toNat_lt
  have e : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rwa [e]

/-! ## Basic instances -/

instance : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩
instance : BEq UInt256 := ⟨fun a b => a.toBitVec == b.toBitVec⟩
instance : Repr UInt256 := ⟨fun x _ => repr x.toNat⟩
instance : ToString UInt256 := ⟨fun x => toString x.toNat⟩

/-! ## Wrap-around arithmetic and bitwise operations (inherited from `BitVec 256`) -/

protected def add (a b : UInt256) : UInt256 := ⟨a.toBitVec + b.toBitVec⟩
protected def sub (a b : UInt256) : UInt256 := ⟨a.toBitVec - b.toBitVec⟩
protected def mul (a b : UInt256) : UInt256 := ⟨a.toBitVec * b.toBitVec⟩
protected def and (a b : UInt256) : UInt256 := ⟨a.toBitVec &&& b.toBitVec⟩
protected def or (a b : UInt256) : UInt256 := ⟨a.toBitVec ||| b.toBitVec⟩
protected def xor (a b : UInt256) : UInt256 := ⟨a.toBitVec ^^^ b.toBitVec⟩
protected def not (a : UInt256) : UInt256 := ⟨~~~ a.toBitVec⟩
protected def shiftLeft (a : UInt256) (n : Nat) : UInt256 := ⟨a.toBitVec <<< n⟩
protected def shiftRight (a : UInt256) (n : Nat) : UInt256 := ⟨a.toBitVec >>> n⟩

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : AndOp UInt256 := ⟨UInt256.and⟩
instance : OrOp UInt256 := ⟨UInt256.or⟩
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : Complement UInt256 := ⟨UInt256.not⟩
instance : HShiftLeft UInt256 Nat UInt256 := ⟨UInt256.shiftLeft⟩
instance : HShiftRight UInt256 Nat UInt256 := ⟨UInt256.shiftRight⟩

theorem toNat_add (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 256 :=
  BitVec.toNat_add ..

theorem toNat_mul (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 :=
  BitVec.toNat_mul ..

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (2 ^ 256 - b.toNat + a.toNat) % 2 ^ 256 :=
  BitVec.toNat_sub ..

/-! ## Byte codec (32 bytes) -/

/-- `UInt256` → 32 big-endian bytes. -/
def toBEBytes (x : UInt256) : List UInt8 := encodeBEU 32 x.toNat

/-- `UInt256` → 32 little-endian bytes. -/
def toLEBytes (x : UInt256) : List UInt8 := encodeLEU 32 x.toNat

/-- Big-endian bytes → `UInt256` (the decoded value modulo `2^256`). -/
def ofBEBytes (bs : List UInt8) : UInt256 := ofNat (decodeBEU bs)

/-- Little-endian bytes → `UInt256`. -/
def ofLEBytes (bs : List UInt8) : UInt256 := ofNat (decodeLEU bs)

@[simp] theorem length_toBEBytes (x : UInt256) : (toBEBytes x).length = 32 := by
  simp [toBEBytes]

@[simp] theorem length_toLEBytes (x : UInt256) : (toLEBytes x).length = 32 := by
  simp [toLEBytes]

/-- **Roundtrip**: encoding a `UInt256` to big-endian bytes and decoding is the identity. -/
theorem ofBEBytes_toBEBytes (x : UInt256) : ofBEBytes (toBEBytes x) = x := by
  have h := decodeBEU_encodeBEU (UInt256.toNat_lt_256 x)
  show ofNat (decodeBEU (encodeBEU 32 x.toNat)) = x
  rw [h, ofNat_toNat]

/-- **Roundtrip**: encoding a `UInt256` to little-endian bytes and decoding is the identity. -/
theorem ofLEBytes_toLEBytes (x : UInt256) : ofLEBytes (toLEBytes x) = x := by
  have h := decodeLEU_encodeLEU (UInt256.toNat_lt_256 x)
  show ofNat (decodeLEU (encodeLEU 32 x.toNat)) = x
  rw [h, ofNat_toNat]

/-- **Roundtrip**: decoding exactly 32 big-endian bytes and re-encoding is the identity. -/
theorem toBEBytes_ofBEBytes {bs : List UInt8} (h : bs.length = 32) :
    toBEBytes (ofBEBytes bs) = bs := by
  have e : (ofBEBytes bs).toNat = decodeBEU bs := by
    show (ofNat (decodeBEU bs)).toNat = decodeBEU bs
    rw [toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hb := decodeBEU_lt bs
    rwa [h] at hb
  show encodeBEU 32 (ofBEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeBEU_decodeBEU bs

/-- **Roundtrip**: decoding exactly 32 little-endian bytes and re-encoding is the identity. -/
theorem toLEBytes_ofLEBytes {bs : List UInt8} (h : bs.length = 32) :
    toLEBytes (ofLEBytes bs) = bs := by
  have e : (ofLEBytes bs).toNat = decodeLEU bs := by
    show (ofNat (decodeLEU bs)).toNat = decodeLEU bs
    rw [toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hb := decodeLEU_lt bs
    rwa [h] at hb
  show encodeLEU 32 (ofLEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeLEU_decodeLEU bs

end UInt256

end Endianness
