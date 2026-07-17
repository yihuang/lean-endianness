# Endianness — a Lean 4 big-endian / little-endian byte-order codec library

Endianness encoding/decoding with **machine-checked proofs** of all core
properties — fixed-width, minimal-length, and two's-complement signed. Written
against the Lean 4 core library only — **no mathlib dependency**.

- Toolchain: `leanprover/lean4:v4.32.0`
- Build: `lake build` (zero `sorry`; includes examples and computation-checked instances)

## Project layout

```
endianness/
├── lakefile.toml
├── lean-toolchain
├── Endianness.lean            # root module (re-exports everything)
└── Endianness/
    ├── Core.lean              # List Nat byte strings: codecs + all core proofs
    ├── UInt8.lean             # List UInt8 interface + roundtrips
    ├── ByteArray.lean         # ByteArray runtime interface + roundtrips
    ├── Fixed.lean             # UInt16/32/64 fixed-width codecs + roundtrips
    ├── Minimal.lean           # minimal-length BE codec (EVM/ABI convention)
    ├── Signed.lean            # two's-complement BE codec (signed EVM/ABI ints)
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
| `Minimal` | all three | shortest BE encoding of a `Nat`; width computed, not given |
| `Signed` | all three | two's-complement BE codec for `Int` |
| `UInt256` | `UInt256 ↔ List UInt8` | 256-bit word (EVM), wraps `BitVec 256` |

Encoding semantics: `encodeBE len n` / `encodeLE len n` produce exactly `len`
bytes; when `n ≥ 256^len` the value is truncated (i.e. `n mod 256^len` is
encoded), so roundtrip theorems take `n < 256^len` as their hypothesis.

## Theorem index

### Core layer (`Endianness.Core`)

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

### UInt8 layer (`Endianness.UInt8`)

`encodeLEU/encodeBEU : Nat → Nat → List UInt8`, `decodeLEU/decodeBEU : List UInt8 → Nat`.
Roundtrips: `decodeLEU_encodeLEU`, `decodeBEU_encodeBEU`, `encodeLEU_decodeLEU`,
`encodeBEU_decodeBEU`; unconditional bounds `decodeLEU_lt`, `decodeBEU_lt`;
length lemmas (`@[simp]`). Bridging: `UInt8.ofNat_toNat`,
`uint8ToNats_natsToUInt8`, `natsToUInt8_uint8ToNats`.

### ByteArray layer (`Endianness.ByteArray`)

`encodeLEBytes/encodeBEBytes : Nat → Nat → ByteArray`, `decodeLEBytes/decodeBEBytes : ByteArray → Nat`.
Roundtrips: `decodeLEBytes_encodeLEBytes`, `decodeBEBytes_encodeBEBytes`,
`encodeLEBytes_decodeLEBytes_size`, `encodeBEBytes_decodeBEBytes_size`;
`size_encodeLEBytes` / `size_encodeBEBytes` (`@[simp]`).

### Fixed layer (`Endianness.Fixed`)

For each `T ∈ {UInt16, UInt32, UInt64}` (width `k ∈ {2, 4, 8}`):

- `T.toBEBytes / T.toLEBytes : T → List UInt8`, `T.ofBEBytes / T.ofLEBytes : List UInt8 → T`
- `T.ofBEBytes_toBEBytes` / `T.ofLEBytes_toLEBytes`: decode after encode
- `T.toBEBytes_ofBEBytes` / `T.toLEBytes_ofLEBytes`: encode after decode, given `bs.length = k`
- `T.length_toBEBytes` / `T.length_toLEBytes` (`@[simp]`)

### Minimal layer (`Endianness.Minimal`)

The shortest byte string that decodes back to `n`, as opposed to the fixed-width
codecs above where you supply the width. `0` encodes as a single `0x00`, matching the
EVM convention rather than the empty string.

| Theorem | Statement |
|---|---|
| `minBytes` | the width: `Nat.log2 n / 8 + 1` (and `1` at `n = 0`) |
| `minBytes_spec` | `0 < len → (n < 256^len ↔ minBytes n ≤ len)` (**minimality**: the LEAST width that fits) |
| `lt_pow_minBytes` | `n < 256 ^ minBytes n` (the width works) |
| `minBytes_le_of_lt` | `n < 256^len → 0 < len → minBytes n ≤ len` |
| `minBytes_eq_of_byte_range` | `256^(k-1) ≤ n < 256^k → minBytes n = k` (**exact width**, the natural byte-range form) |
| `minBytes_eq_of_range` | `2^(8k-1) ≤ n < 2^(8k) → minBytes n = k` (bit-length form; narrower — only values whose top byte has its high bit set) |
| `minBytes_div` | `256 ≤ n → minBytes n = minBytes (n/256) + 1` (base-256 recursion, derived from the spec — no `log2` reasoning) |
| `minBytes_eq_one` | `n < 256 → minBytes n = 1` (base case) |
| `decodeBE_encodeBEMin` (+ `U`/`Bytes`) | roundtrip — **no side condition**, the width is chosen to fit |
| `encodeBEMin_injective` | the minimal encoding is injective |
| `length_encodeBEMin` / `size_encodeBEMinBytes` | `= minBytes n` (`@[simp]`) |

`minBytes_div` + `minBytes_eq_one` are what let a caller identify its own recursive
width function with `minBytes` by plain induction.

### Signed layer (`Endianness.Signed`)

Two's-complement big-endian, the convention signed EVM/ABI integers use. The encoding
is the fixed-width unsigned one applied to `twosRep`, so the unsigned theory carries
over.

| Theorem | Statement |
|---|---|
| `twosRep len v` | the unsigned representative: `v.toNat`, or `(256^len + v).toNat` when negative |
| `InTwosRange len v` | `-256^len ≤ 2v < 256^len` — the usual `[-2^(8len-1), 2^(8len-1))`, stated without a truncating exponent |
| `twosRep_lt` | in range, the representative fits in `len` bytes |
| `decodeTwosBE_encodeTwosBE` (+ `U`/`Bytes`) | **roundtrip**, given `InTwosRange` |
| `encodeTwosBE_injective` | injective on representable values |
| `encodeTwosBEBytes_eq` | `= encodeBEBytes len (twosRep len v)` (bridge to the unsigned theory) |
| `length_encodeTwosBE` / `size_encodeTwosBEBytes` | `= len` (`@[simp]`) |

`InTwosRange` is required, not decoration: out of range the encoding wraps —
`decodeTwosBE (encodeTwosBE 1 129) = -127`.

### UInt256 (`Endianness.UInt256`)

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

## Usage examples

```lean
import Endianness

-- Big-endian encoding: 0xDEADBEEF → [222, 173, 190, 239]
#eval Endianness.encodeBE 4 0xDEADBEEF

-- Little-endian encoding: → [239, 190, 173, 222]
#eval Endianness.encodeLE 4 0xDEADBEEF

-- Big-endian decoding → 3735928559
#eval Endianness.decodeBE [222, 173, 190, 239]

-- Proving a concrete instance via the library theorem (no computation)
example : Endianness.decodeBE (Endianness.encodeBE 4 0xDEADBEEF) = 0xDEADBEEF :=
  Endianness.decodeBE_encodeBE (by decide)

-- Minimal-length: the width is computed, not supplied. 0xDEADBEEF → [222,173,190,239]
#eval Endianness.encodeBEMin 0xDEADBEEF
#eval (Endianness.minBytes 255, Endianness.minBytes 256)   -- → (1, 2)

-- Minimal roundtrip needs NO hypothesis
example : Endianness.decodeBE (Endianness.encodeBEMin 0xDEADBEEF) = 0xDEADBEEF :=
  Endianness.decodeBE_encodeBEMin _

-- Signed: two's complement. -1 in one byte → [255]; -2 in four → [255,255,255,254]
#eval Endianness.encodeTwosBE 1 (-1)
#eval Endianness.decodeTwosBE [128]   -- → -128

-- Signed roundtrip, given representability
example : Endianness.decodeTwosBE (Endianness.encodeTwosBE 4 (-2)) = -2 :=
  Endianness.decodeTwosBE_encodeTwosBE (by decide)

-- UInt256: 32-byte big-endian, roundtrip by theorem
example : Endianness.UInt256.ofBEBytes (Endianness.UInt256.toBEBytes (42 : Endianness.UInt256)) = 42 :=
  Endianness.UInt256.ofBEBytes_toBEBytes 42
```

## Using it as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "endianness"
path = "../endianness"
```

then `import Endianness`.

## Building and verifying

```bash
elan toolchain install leanprover/lean4:v4.32.0   # if not already installed
lake build
```

`Endianness/Examples.lean` prints real codec outputs via `#eval`, and several
`example`s verify concrete instances fully computationally with `decide` /
`native_decide`.
