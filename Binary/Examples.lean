import Binary.Core
import Binary.UInt8
import Binary.ByteArray
import Binary.Fixed
import Binary.Minimal
import Binary.Signed
import Binary.UInt256

/-!
# Binary.Examples

Usage examples: numeric evaluation (`#eval`), property checking on concrete
instances (`by decide` / `by native_decide`), and proofs that apply the
library theorems directly.
-/

namespace Binary

-- Big-endian encoding of 0xDEADBEEF → [0xDE, 0xAD, 0xBE, 0xEF] = [222, 173, 190, 239]
#eval encodeBE 4 0xDEADBEEF

-- Little-endian encoding of 0xDEADBEEF → [239, 190, 173, 222]
#eval encodeLE 4 0xDEADBEEF

-- Big-endian decoding of [222, 173, 190, 239] → 3735928559
#eval decodeBE [222, 173, 190, 239]

-- 1024 = 0x400 as 2 big-endian bytes → [4, 0]
#eval encodeBE 2 1024

-- ByteArray interface
#eval (encodeBEBytes 4 0xDEADBEEF).data.toList
#eval decodeBEBytes (encodeBEBytes 4 0xDEADBEEF)

-- UInt32 / UInt64 interfaces
#eval (UInt32.toBEBytes 0xDEADBEEF).map UInt8.toNat
#eval UInt32.ofLEBytes (UInt32.toLEBytes 2026)

-- Roundtrips on concrete instances, verified by computation
example : decodeBE (encodeBE 4 0xDEADBEEF) = 0xDEADBEEF := by decide
example : decodeLE (encodeLE 8 123456789) = 123456789 := by decide
example : encodeBE 4 (decodeBE [1, 2, 3, 4]) = [1, 2, 3, 4] := by decide
example : UInt32.ofBEBytes (UInt32.toBEBytes 42) = 42 := by native_decide
example : UInt64.ofLEBytes (UInt64.toLEBytes 0x0123456789ABCDEF) = 0x0123456789ABCDEF := by
  native_decide

-- The same property proved via the library theorem (no computation needed)
example : decodeBE (encodeBE 4 0xDEADBEEF) = 0xDEADBEEF :=
  decodeBE_encodeBE (by decide)

-- Universally quantified version: the one-byte roundtrip
example : ∀ n < 256, decodeBE (encodeBE 1 n) = n := fun _ hn => decodeBE_encodeBE hn

-- Concatenation law instance:
-- decodeBE ([0xDE, 0xAD] ++ [0xBE, 0xEF]) = 0xDEAD * 256^2 + 0xBEEF
example : decodeBE ([0xDE, 0xAD] ++ [0xBE, 0xEF])
    = decodeBE [0xDE, 0xAD] * 256 ^ 2 + decodeBE [0xBE, 0xEF] :=
  decodeBE_append _ _

/-! ## UInt256 (EVM word, 32 bytes) -/

-- 0xDEADBEEF as 32 big-endian bytes (left-padded with zeros)
#eval (UInt256.toBEBytes (UInt256.ofNat 0xDEADBEEF)).map UInt8.toNat

-- The last two little-endian bytes of 0x0102 are [2, 1] followed by zeros
#eval (UInt256.toLEBytes (0x0102 : UInt256)).map UInt8.toNat

-- Roundtrip via the library theorem
example : UInt256.ofBEBytes (UInt256.toBEBytes (42 : UInt256)) = 42 :=
  UInt256.ofBEBytes_toBEBytes 42

-- Roundtrip verified by native computation on a 256-bit value
example : UInt256.ofLEBytes (UInt256.toLEBytes (0x0102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F20 : UInt256))
    = 0x0102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F20 := by
  native_decide

-- Wrap-around arithmetic inherited from BitVec 256: (2^256 - 1) + 1 = 0
example : (UInt256.ofNat (2 ^ 256 - 1) + 1).toNat = 0 := by native_decide

/-! ## Minimal-length codec (`Binary.Minimal`)

The width is computed from the value rather than supplied. -/

-- The shortest big-endian encoding: 0xDEADBEEF needs 4 bytes → [222, 173, 190, 239]
#eval encodeBEMin 0xDEADBEEF

-- Widths: 255 fits in one byte, 256 needs two
#eval (minBytes 255, minBytes 256)

-- Zero encodes as ONE zero byte (the EVM convention), not the empty string
#eval encodeBEMin 0

-- 32 bytes for a full EVM word, 33 once it overflows one
#eval (minBytes (2 ^ 256 - 1), minBytes (2 ^ 256))

-- The minimal encoding never has a leading zero byte — that is what "minimal" means
example : (encodeBEMin 256).head! ≠ 0 := by decide

-- Roundtrip needs NO hypothesis: the width is chosen to fit
example : decodeBE (encodeBEMin 0xDEADBEEF) = 0xDEADBEEF := decodeBE_encodeBEMin _
example : decodeBEBytes (encodeBEMinBytes 123456789) = 123456789 :=
  decodeBEBytes_encodeBEMinBytes _

-- Exact width by theorem, from the byte-range bound 256^(k-1) <= n < 256^k
example : minBytes 256 = 2 := minBytes_eq_of_byte_range (by decide) (by decide) (by decide)
example : minBytes 65535 = 2 := minBytes_eq_of_byte_range (by decide) (by decide) (by decide)

/-! ## Two's-complement signed codec (`Binary.Signed`) -/

-- -1 in one byte → [255]; -2 in four → [255, 255, 255, 254]
#eval encodeTwosBE 1 (-1)
#eval encodeTwosBE 4 (-2)

-- The sign boundary: -128 and 127 are the extremes of one byte
#eval (encodeTwosBE 1 (-128), encodeTwosBE 1 127)

-- Decoding reads the leading bit as the sign
#eval (decodeTwosBE [128], decodeTwosBE [127], decodeTwosBE [255])

-- -1 in an EVM word is 32 bytes of 0xFF
#eval (encodeTwosBEBytes 32 (-1)).data.toList.all (fun b => b == 0xFF)

-- Roundtrips on concrete instances, discharged by the Decidable instance
example : decodeTwosBE (encodeTwosBE 4 (-2)) = -2 :=
  decodeTwosBE_encodeTwosBE (by decide)
example : decodeTwosBEBytes (encodeTwosBEBytes 32 (-12345)) = -12345 :=
  decodeTwosBEBytes_encodeTwosBEBytes (by decide)

-- `InTwosRange` is a REAL hypothesis: out of range the encoding wraps.
-- 129 does not fit one signed byte, and comes back as -127.
#eval decodeTwosBE (encodeTwosBE 1 129)
example : ¬ InTwosRange 1 129 := by decide

end Binary
