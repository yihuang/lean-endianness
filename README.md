# Binary — a Lean 4 big-endian / little-endian byte-order codec library

Fixed-width endianness encoding/decoding with **machine-checked proofs** of all
core properties. Written against the Lean 4 core library only — **no mathlib
dependency**.

- Toolchain: `leanprover/lean4:v4.32.0`
- Build: `lake build` (zero `sorry`; includes examples and computation-checked instances)

## Project layout

```
binary/
├── lakefile.toml
├── lean-toolchain
├── Binary.lean            # root module (re-exports everything)
└── Binary/
    ├── Core.lean              # List Nat byte strings: codecs + all core proofs
    ├── UInt8.lean             # List UInt8 interface + roundtrips
    ├── ByteArray.lean         # ByteArray runtime interface + roundtrips
    ├── Fixed.lean             # UInt16/32/64 fixed-width codecs + roundtrips
    ├── UInt256.lean           # 256-bit unsigned integer (EVM word) + codecs
    └── Examples.lean          # usage examples and computation-checked instances
```

## Layered design

| Layer | Byte-string representation | Role |
|---|---|---|
| `Core` | `List Nat` with `IsBytes bs := ∀ b ∈ bs, b < 256` | the mathematical core; every proof happens here |
| `UInt8` | `List UInt8` | practical interface; properties lifted from Core |
| `ByteArray` | `ByteArray` | runtime I/O interface |
| `Fixed` | `UInt16/32/64 ↔ List UInt8` | fixed-width codecs |
| `UInt256` | `UInt256 ↔ List UInt8` / `ByteArray` | 256-bit word (EVM), wraps `BitVec 256` |

Encoding semantics: `encodeBE len n` / `encodeLE len n` produce exactly `len`
bytes; when `n ≥ 256^len` the value is truncated (i.e. `n mod 256^len` is
encoded), so roundtrip theorems take `n < 256^len` as their hypothesis.

## Theorem index

### Core layer (`Binary.Core`)

| Theorem | Statement |
|---|---|
| `decodeLE_encodeLE` / `decodeBE_encodeBE` | `n < 256^len → decode (encode len n) = n` (**roundtrip**) |
| `encodeLE_decodeLE` / `encodeBE_decodeBE` | `IsBytes bs → encode bs.length (decode bs) = bs` (**roundtrip**) |
| `decodeLE_lt` / `decodeBE_lt` | `IsBytes bs → decode bs < 256^bs.length` (upper bound) |
| `length_encodeLE` / `length_encodeBE` | `(encode len n).length = len` (`@[simp]`) |
| `isBytes_encodeLE` / `isBytes_encodeBE` | encodings are always valid byte strings |
| `encodeLE_injective` / `encodeBE_injective` | fixed-length encoding is injective below `256^len` |
| `decodeLE_injective` / `decodeBE_injective` | decoding is injective on valid strings of equal length |
| `decodeLE_append` | `decodeLE (xs ++ ys) = decodeLE xs + 256^xs.length * decodeLE ys` |
| `decodeBE_append` | `decodeBE (xs ++ ys) = decodeBE xs * 256^ys.length + decodeBE ys` |
| `encodeBE_succ` | `encodeBE (len+1) n = encodeBE len (n/256) ++ [n%256]` |
| `decodeBE_snoc` | `decodeBE (bs ++ [b]) = decodeBE bs * 256 + b` |

### UInt8 layer (`Binary.UInt8`)

`encodeLEU/encodeBEU : Nat → Nat → List UInt8`, `decodeLEU/decodeBEU : List UInt8 → Nat`.
Roundtrips: `decodeLEU_encodeLEU`, `decodeBEU_encodeBEU`, `encodeLEU_decodeLEU`,
`encodeBEU_decodeBEU`; unconditional bounds `decodeLEU_lt`, `decodeBEU_lt`;
length lemmas (`@[simp]`). Bridging: `UInt8.ofNat_toNat`,
`uint8ToNats_natsToUInt8`, `natsToUInt8_uint8ToNats`.

### ByteArray layer (`Binary.ByteArray`)

`encodeLEBytes/encodeBEBytes : Nat → Nat → ByteArray`, `decodeLEBytes/decodeBEBytes : ByteArray → Nat`.
Roundtrips: `decodeLEBytes_encodeLEBytes`, `decodeBEBytes_encodeBEBytes`,
`encodeLEBytes_decodeLEBytes_size`, `encodeBEBytes_decodeBEBytes_size`;
`size_encodeLEBytes` / `size_encodeBEBytes` (`@[simp]`).

### Fixed layer (`Binary.Fixed`)

For each `T ∈ {UInt16, UInt32, UInt64}` (width `k ∈ {2, 4, 8}`):

- `T.toBEBytes / T.toLEBytes : T → List UInt8`, `T.ofBEBytes / T.ofLEBytes : List UInt8 → T`
- `T.ofBEBytes_toBEBytes` / `T.ofLEBytes_toLEBytes`: decode after encode
- `T.toBEBytes_ofBEBytes` / `T.toLEBytes_ofLEBytes`: encode after decode, given `bs.length = k`
- `T.length_toBEBytes` / `T.length_toLEBytes` (`@[simp]`)

### UInt256 (`Binary.UInt256`)

A 256-bit unsigned integer (EVM word size) wrapping `BitVec 256`, in the same
style as core's `UInt8` … `UInt64`.

- Basics: `UInt256.ofNat`, `UInt256.toNat`, `UInt256.size = 2^256`;
  instances `OfNat` (numerals), `DecidableEq`, `BEq`, `Inhabited`, `Repr`, `ToString`
- Bridge lemmas: `toNat_lt`, `toNat_ofNat`, `toNat_inj`, `ofNat_toNat`, `toNat_lt_256`
- Wrap-around arithmetic/bitwise ops via instances: `Add`, `Sub`, `Mul`,
  `AndOp`, `OrOp`, `XorOp`, `Complement`, `HShiftLeft`, `HShiftRight`,
  with `toNat_add` / `toNat_mul` / `toNat_sub`
- Byte codec (32 bytes): `toBEBytes`, `toLEBytes`, `ofBEBytes`, `ofLEBytes`
- Roundtrips: `ofBEBytes_toBEBytes`, `ofLEBytes_toLEBytes`,
  `toBEBytes_ofBEBytes` / `toLEBytes_ofLEBytes` (given `bs.length = 32`)
- `ByteArray` codec (32 bytes): `toBEByteArray`, `toLEByteArray`,
  `ofBEByteArray`, `ofLEByteArray`
- Refinement lemmas: `toList_toBEByteArray` / `toList_toLEByteArray` and
  `ofBEByteArray_eq_ofBEBytes` / `ofLEByteArray_eq_ofLEBytes` (the `ByteArray`
  codec agrees with the `List UInt8` codec)
- `ByteArray` roundtrips: `ofBEByteArray_toBEByteArray`,
  `ofLEByteArray_toLEByteArray`, `toBEByteArray_ofBEByteArray` /
  `toLEByteArray_ofLEByteArray` (given `ba.size = 32`),
  `size_toBEByteArray` / `size_toLEByteArray` (`@[simp]`),
  `toNat_ofBEByteArray_of_size` / `toNat_ofLEByteArray_of_size`

## Usage examples

```lean
import Binary

-- Big-endian encoding: 0xDEADBEEF → [222, 173, 190, 239]
#eval Binary.encodeBE 4 0xDEADBEEF

-- Little-endian encoding: → [239, 190, 173, 222]
#eval Binary.encodeLE 4 0xDEADBEEF

-- Big-endian decoding → 3735928559
#eval Binary.decodeBE [222, 173, 190, 239]

-- Proving a concrete instance via the library theorem (no computation)
example : Binary.decodeBE (Binary.encodeBE 4 0xDEADBEEF) = 0xDEADBEEF :=
  Binary.decodeBE_encodeBE (by decide)

-- UInt256: 32-byte big-endian, roundtrip by theorem
example : Binary.UInt256.ofBEBytes (Binary.UInt256.toBEBytes (42 : Binary.UInt256)) = 42 :=
  Binary.UInt256.ofBEBytes_toBEBytes 42
```

## Using it as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "binary"
path = "../binary"
```

then `import Binary`.

## Building and verifying

```bash
elan toolchain install leanprover/lean4:v4.32.0   # if not already installed
lake build
```

`Binary/Examples.lean` prints real codec outputs via `#eval`, and several
`example`s verify concrete instances fully computationally with `decide` /
`native_decide`.
