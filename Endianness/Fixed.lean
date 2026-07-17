import Endianness.UInt8

/-!
# Endianness.Fixed

Fixed-width integer (`UInt16` / `UInt32` / `UInt64`) endianness codecs,
with four roundtrip theorems per type:

* `ofBEBytes_toBEBytes` / `ofLEBytes_toLEBytes` — decode after encode
* `toBEBytes_ofBEBytes` / `toLEBytes_ofLEBytes` — encode after decode
  (for inputs of exactly the right length)

The interface is `List UInt8`, composing with the `Endianness.UInt8` and
`Endianness.ByteArray` layers.
-/

namespace Endianness

/-! ## Width bounds and `ofNat ∘ toNat = id` -/

theorem UInt16.toNat_lt_256 (x : UInt16) : x.toNat < 256 ^ 2 := by
  have h := UInt16.toNat_lt x
  have e : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
  rwa [e]

theorem UInt32.toNat_lt_256 (x : UInt32) : x.toNat < 256 ^ 4 := by
  have h := UInt32.toNat_lt x
  have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rwa [e]

theorem UInt64.toNat_lt_256 (x : UInt64) : x.toNat < 256 ^ 8 := by
  have h := UInt64.toNat_lt x
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rwa [e]

theorem UInt16.ofNat_toNat (x : UInt16) : UInt16.ofNat x.toNat = x := by
  apply UInt16.toNat_inj.mp
  rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt x.toNat_lt]

theorem UInt32.ofNat_toNat (x : UInt32) : UInt32.ofNat x.toNat = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt x.toNat_lt]

theorem UInt64.ofNat_toNat (x : UInt64) : UInt64.ofNat x.toNat = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt x.toNat_lt]

/-! ## UInt16 (2 bytes) -/

/-- `UInt16` → 2 big-endian bytes. -/
def UInt16.toBEBytes (x : UInt16) : List UInt8 := encodeBEU 2 x.toNat

/-- `UInt16` → 2 little-endian bytes. -/
def UInt16.toLEBytes (x : UInt16) : List UInt8 := encodeLEU 2 x.toNat

/-- Big-endian bytes → `UInt16` (the decoded value modulo `2^16`). -/
def UInt16.ofBEBytes (bs : List UInt8) : UInt16 := UInt16.ofNat (decodeBEU bs)

/-- Little-endian bytes → `UInt16`. -/
def UInt16.ofLEBytes (bs : List UInt8) : UInt16 := UInt16.ofNat (decodeLEU bs)

@[simp] theorem UInt16.length_toBEBytes (x : UInt16) : (UInt16.toBEBytes x).length = 2 := by
  simp [UInt16.toBEBytes]

@[simp] theorem UInt16.length_toLEBytes (x : UInt16) : (UInt16.toLEBytes x).length = 2 := by
  simp [UInt16.toLEBytes]

/-- **Roundtrip**: encoding a `UInt16` to big-endian bytes and decoding is the identity. -/
theorem UInt16.ofBEBytes_toBEBytes (x : UInt16) : UInt16.ofBEBytes (UInt16.toBEBytes x) = x := by
  have h := decodeBEU_encodeBEU (UInt16.toNat_lt_256 x)
  show UInt16.ofNat (decodeBEU (encodeBEU 2 x.toNat)) = x
  rw [h, UInt16.ofNat_toNat]

/-- **Roundtrip**: encoding a `UInt16` to little-endian bytes and decoding is the identity. -/
theorem UInt16.ofLEBytes_toLEBytes (x : UInt16) : UInt16.ofLEBytes (UInt16.toLEBytes x) = x := by
  have h := decodeLEU_encodeLEU (UInt16.toNat_lt_256 x)
  show UInt16.ofNat (decodeLEU (encodeLEU 2 x.toNat)) = x
  rw [h, UInt16.ofNat_toNat]

/-- **Roundtrip**: decoding exactly 2 big-endian bytes and re-encoding is the identity. -/
theorem UInt16.toBEBytes_ofBEBytes {bs : List UInt8} (h : bs.length = 2) :
    UInt16.toBEBytes (UInt16.ofBEBytes bs) = bs := by
  have e : (UInt16.ofBEBytes bs).toNat = decodeBEU bs := by
    show (UInt16.ofNat (decodeBEU bs)).toNat = decodeBEU bs
    rw [UInt16.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeBEU_lt bs
    rwa [h] at hb
  show encodeBEU 2 (UInt16.ofBEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeBEU_decodeBEU bs

/-- **Roundtrip**: decoding exactly 2 little-endian bytes and re-encoding is the identity. -/
theorem UInt16.toLEBytes_ofLEBytes {bs : List UInt8} (h : bs.length = 2) :
    UInt16.toLEBytes (UInt16.ofLEBytes bs) = bs := by
  have e : (UInt16.ofLEBytes bs).toNat = decodeLEU bs := by
    show (UInt16.ofNat (decodeLEU bs)).toNat = decodeLEU bs
    rw [UInt16.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeLEU_lt bs
    rwa [h] at hb
  show encodeLEU 2 (UInt16.ofLEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeLEU_decodeLEU bs

/-! ## UInt32 (4 bytes) -/

/-- `UInt32` → 4 big-endian bytes. -/
def UInt32.toBEBytes (x : UInt32) : List UInt8 := encodeBEU 4 x.toNat

/-- `UInt32` → 4 little-endian bytes. -/
def UInt32.toLEBytes (x : UInt32) : List UInt8 := encodeLEU 4 x.toNat

/-- Big-endian bytes → `UInt32` (the decoded value modulo `2^32`). -/
def UInt32.ofBEBytes (bs : List UInt8) : UInt32 := UInt32.ofNat (decodeBEU bs)

/-- Little-endian bytes → `UInt32`. -/
def UInt32.ofLEBytes (bs : List UInt8) : UInt32 := UInt32.ofNat (decodeLEU bs)

@[simp] theorem UInt32.length_toBEBytes (x : UInt32) : (UInt32.toBEBytes x).length = 4 := by
  simp [UInt32.toBEBytes]

@[simp] theorem UInt32.length_toLEBytes (x : UInt32) : (UInt32.toLEBytes x).length = 4 := by
  simp [UInt32.toLEBytes]

/-- **Roundtrip**: encoding a `UInt32` to big-endian bytes and decoding is the identity. -/
theorem UInt32.ofBEBytes_toBEBytes (x : UInt32) : UInt32.ofBEBytes (UInt32.toBEBytes x) = x := by
  have h := decodeBEU_encodeBEU (UInt32.toNat_lt_256 x)
  show UInt32.ofNat (decodeBEU (encodeBEU 4 x.toNat)) = x
  rw [h, UInt32.ofNat_toNat]

/-- **Roundtrip**: encoding a `UInt32` to little-endian bytes and decoding is the identity. -/
theorem UInt32.ofLEBytes_toLEBytes (x : UInt32) : UInt32.ofLEBytes (UInt32.toLEBytes x) = x := by
  have h := decodeLEU_encodeLEU (UInt32.toNat_lt_256 x)
  show UInt32.ofNat (decodeLEU (encodeLEU 4 x.toNat)) = x
  rw [h, UInt32.ofNat_toNat]

/-- **Roundtrip**: decoding exactly 4 big-endian bytes and re-encoding is the identity. -/
theorem UInt32.toBEBytes_ofBEBytes {bs : List UInt8} (h : bs.length = 4) :
    UInt32.toBEBytes (UInt32.ofBEBytes bs) = bs := by
  have e : (UInt32.ofBEBytes bs).toNat = decodeBEU bs := by
    show (UInt32.ofNat (decodeBEU bs)).toNat = decodeBEU bs
    rw [UInt32.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeBEU_lt bs
    rwa [h] at hb
  show encodeBEU 4 (UInt32.ofBEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeBEU_decodeBEU bs

/-- **Roundtrip**: decoding exactly 4 little-endian bytes and re-encoding is the identity. -/
theorem UInt32.toLEBytes_ofLEBytes {bs : List UInt8} (h : bs.length = 4) :
    UInt32.toLEBytes (UInt32.ofLEBytes bs) = bs := by
  have e : (UInt32.ofLEBytes bs).toNat = decodeLEU bs := by
    show (UInt32.ofNat (decodeLEU bs)).toNat = decodeLEU bs
    rw [UInt32.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeLEU_lt bs
    rwa [h] at hb
  show encodeLEU 4 (UInt32.ofLEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeLEU_decodeLEU bs

/-! ## UInt64 (8 bytes) -/

/-- `UInt64` → 8 big-endian bytes. -/
def UInt64.toBEBytes (x : UInt64) : List UInt8 := encodeBEU 8 x.toNat

/-- `UInt64` → 8 little-endian bytes. -/
def UInt64.toLEBytes (x : UInt64) : List UInt8 := encodeLEU 8 x.toNat

/-- Big-endian bytes → `UInt64` (the decoded value modulo `2^64`). -/
def UInt64.ofBEBytes (bs : List UInt8) : UInt64 := UInt64.ofNat (decodeBEU bs)

/-- Little-endian bytes → `UInt64`. -/
def UInt64.ofLEBytes (bs : List UInt8) : UInt64 := UInt64.ofNat (decodeLEU bs)

@[simp] theorem UInt64.length_toBEBytes (x : UInt64) : (UInt64.toBEBytes x).length = 8 := by
  simp [UInt64.toBEBytes]

@[simp] theorem UInt64.length_toLEBytes (x : UInt64) : (UInt64.toLEBytes x).length = 8 := by
  simp [UInt64.toLEBytes]

/-- **Roundtrip**: encoding a `UInt64` to big-endian bytes and decoding is the identity. -/
theorem UInt64.ofBEBytes_toBEBytes (x : UInt64) : UInt64.ofBEBytes (UInt64.toBEBytes x) = x := by
  have h := decodeBEU_encodeBEU (UInt64.toNat_lt_256 x)
  show UInt64.ofNat (decodeBEU (encodeBEU 8 x.toNat)) = x
  rw [h, UInt64.ofNat_toNat]

/-- **Roundtrip**: encoding a `UInt64` to little-endian bytes and decoding is the identity. -/
theorem UInt64.ofLEBytes_toLEBytes (x : UInt64) : UInt64.ofLEBytes (UInt64.toLEBytes x) = x := by
  have h := decodeLEU_encodeLEU (UInt64.toNat_lt_256 x)
  show UInt64.ofNat (decodeLEU (encodeLEU 8 x.toNat)) = x
  rw [h, UInt64.ofNat_toNat]

/-- **Roundtrip**: decoding exactly 8 big-endian bytes and re-encoding is the identity. -/
theorem UInt64.toBEBytes_ofBEBytes {bs : List UInt8} (h : bs.length = 8) :
    UInt64.toBEBytes (UInt64.ofBEBytes bs) = bs := by
  have e : (UInt64.ofBEBytes bs).toNat = decodeBEU bs := by
    show (UInt64.ofNat (decodeBEU bs)).toNat = decodeBEU bs
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeBEU_lt bs
    rwa [h] at hb
  show encodeBEU 8 (UInt64.ofBEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeBEU_decodeBEU bs

/-- **Roundtrip**: decoding exactly 8 little-endian bytes and re-encoding is the identity. -/
theorem UInt64.toLEBytes_ofLEBytes {bs : List UInt8} (h : bs.length = 8) :
    UInt64.toLEBytes (UInt64.ofLEBytes bs) = bs := by
  have e : (UInt64.ofLEBytes bs).toNat = decodeLEU bs := by
    show (UInt64.ofNat (decodeLEU bs)).toNat = decodeLEU bs
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hb := decodeLEU_lt bs
    rwa [h] at hb
  show encodeLEU 8 (UInt64.ofLEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeLEU_decodeLEU bs

end Endianness
