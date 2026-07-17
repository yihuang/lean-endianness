import Endianness.Core
import Endianness.UInt8
import Endianness.ByteArray
import Endianness.Fixed
import Endianness.UInt256
import Endianness.Examples

/-!
# Endianness

A big-endian / little-endian byte-order codec library with machine-checked
proofs, written against the Lean 4 core library only (no mathlib dependency).

* `Endianness.Core` — codecs over `List Nat` byte strings and all core proofs
* `Endianness.UInt8` — the practical `List UInt8` interface with roundtrips
* `Endianness.ByteArray` — the `ByteArray` runtime interface with roundtrips
* `Endianness.Fixed` — fixed-width `UInt16` / `UInt32` / `UInt64` codecs
* `Endianness.UInt256` — a 256-bit unsigned integer (EVM word) with codecs
* `Endianness.Examples` — usage examples and computation-checked instances
-/
