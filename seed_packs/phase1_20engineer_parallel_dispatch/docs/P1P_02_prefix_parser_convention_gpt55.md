# P1P-02 — Prefix parser convention design

Handle: `gpt55`

Progress classification: **Infrastructure**.  This document fixes a parser and
serialization convention for the contract-expansion prefix language.  It does
not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## 1. Executive verdict

**PARSER_CONVENTION_READY_FOR_LEAN**

The recommended convention is a canonical, single-length encoding for each
truth-table arity `n`.  The key choice is to allocate a fixed
`witnessBits n`-bit prefix slot after `x` and `i`: the active prefix `p` occupies
the first `i` bits of that slot and the remaining `witnessBits n - i` bits are
zero padding.  This makes the ambient length depend only on `n`, not on the
chosen prefix length `i`.

This is only parser/serialization design.  It does not prove NP membership,
does not implement a Lean parser, and does not open R1-C.

## 2. Encoding layout

### Parameters and helper lengths

For the tree-MCSP target induced by a threshold and a witness encoding/codec,
write:

- `tableLen n = 2^n`, matching `Pnp3.Models.Partial.tableLen n`.
- `witnessBits n` for the full target witness length.
- `tagBits = 8`.
- `tagValue = 0b10110010`, a fixed version/domain separator for this exact
  prefix-language serialization.
- `iWidth n = min { k : Nat | witnessBits n + 1 ≤ 2^k }`.
  This width encodes every `i` in `[0, witnessBits n]`.  If
  `witnessBits n = 0`, then `iWidth n = 0` and the unique empty `i` field
  denotes `i = 0`.

### Bit order convention

All multi-bit natural-number fields are big-endian within their slice.  The
entire ambient bit-vector is read left-to-right in the order below.

### Field layout

For a well-formed string at arity `n` and prefix length `i`, the ambient bit
layout is exactly:

```text
[tag: 8 bits]
[n: unary self-delimiting bits, 1^n 0]
[x: tableLen n bits]
[i: iWidth n bits, unsigned big-endian]
[p: i bits]
[pad: witnessBits n - i bits]
```

Equivalently, as one concatenation:

```text
tagValue || 1^n 0 || x || enc_iWidth(n)(i) || p || 0^(witnessBits n - i)
```

### Answers to required layout questions

- **Fixed-width or self-delimiting encoding for `n`?**
  `n` is self-delimiting unary: `1^n 0`.  This lets the parser recover `n`
  before knowing `tableLen n`, `iWidth n`, or `witnessBits n`.

- **Fixed-width or self-delimiting encoding for `i`?**
  `i` is fixed-width after `n` is known: exactly `iWidth n` bits, unsigned
  big-endian.  The parser rejects decoded values with `i > witnessBits n`.

- **Where exactly does `x : TruthTable n` live?**
  `x` is the contiguous `tableLen n = 2^n`-bit slice immediately after the
  unary `n` field and immediately before the fixed-width `i` field.  In the
  concrete tree-MCSP search problem this is exactly the instance bit-vector of
  length `problem.instanceBits n = tableLen n`.

- **Where exactly does `p : BitVec i` live?**
  `p` is the first `i` bits of the fixed `witnessBits n`-bit prefix slot
  immediately after the `i` field.

- **What is `pad`?**
  `pad` is the unused suffix of that fixed witness-prefix slot.  Its length is
  `padBits = witnessBits n - i`, and it occupies the final
  `witnessBits n - i` bits of the ambient string.

- **Are pad bits required zero or ignored?**
  Pad bits are **required zero**.  They are semantically ignored by
  `PrefixExtendableInput`, but the parser rejects nonzero pad bits so that
  successful parsing is canonical and the round-trip theorem is not polluted by
  many encodings of the same prefix input.

- **Malformed behavior?**
  Every violation of this layout returns `none`.  There is no promise-style
  behavior and no semantic fallback.

## 3. Ambient length `M(n)`

The proposed ambient length is:

```text
M(n) = tagBits + (n + 1) + tableLen n + iWidth n + witnessBits n
     = 8 + (n + 1) + 2^n + iWidth n + witnessBits n
```

This is the single accepted length for all prefixes at the same arity `n`.
The variable active prefix length `i` does not change `M(n)` because `p` and
`pad` together always occupy exactly `witnessBits n` bits.

The required inequality is immediate:

```text
tableLen n ≤ M(n)
```

because `M(n)` contains `tableLen n` as a summand and every other summand is a
natural number.  This deliberately avoids the rejected toy convention
`M(n) = n`, which would not contain the truth table and would make exhaustive
truth-table checking exponential in the actual input length.

When mapped onto the staged R1-B2a ambient-length helper, use:

```text
overhead(n) = 8 + (n + 1) + iWidth n
witnessBits(n) = codec.witnessBits n
extraPadBits(n) = 0

treeMCSPPrefixAmbientLength overhead codec.witnessBits extraPadBits n
  = tableLen n + overhead(n) + codec.witnessBits n + 0
  = M(n)
```

The parser-level `pad` is not an extra ambient-length summand; it is the unused
suffix inside the fixed `witnessBits n` slot.

## 4. Parser behavior

The intended Lean parser name is:

```text
parseTreeMCSPPrefixInput : BitVec m → Option (PrefixInput ... m)
```

Operational behavior:

1. Check the first `8` bits against `tagValue`.
2. Decode unary `n` as the number of consecutive `1` bits after the tag before
   the first `0` bit.
3. Compute `expected = M(n)` and reject unless `m = expected`.
4. Slice `x` as the next `tableLen n` bits.
5. Slice `i` as the next `iWidth n` bits and decode it as an unsigned natural.
6. Reject if `i > witnessBits n`.
7. Slice `p` as the next `i` bits.
8. Slice `pad` as the remaining `witnessBits n - i` bits.
9. Reject unless every pad bit is zero.
10. Return `some input` with:
    - `input.tag = tagValue`;
    - `input.n = n`;
    - `input.x = x`;
    - `input.i = i`;
    - `input.prefixLength_le` supplied by the successful `i ≤ witnessBits n`
      check;
    - `input.p = p`;
    - `input.padBits = witnessBits n - i`;
    - `input.pad = pad`.

Malformed cases:

| Case | Parser result | Notes |
| --- | --- | --- |
| bad tag | `none` | Includes `m < 8`, since the tag slice is unavailable. |
| inconsistent length | `none` | After decoding `n`, require `m = M(n)` exactly. |
| invalid `n` encoding | `none` | No unary terminator `0` before the end of the input, or terminator exists but the resulting `M(n)` does not equal `m`. |
| invalid `i` encoding | `none` | For fixed-width binary every available slice denotes a natural; invalid means the `i` slice is unavailable because length checks failed. |
| `i > witnessBits n` | `none` | Prevents out-of-range prefix coordinates. |
| `x` slice too short | `none` | Normally implied by `m ≠ M(n)`, but stated as a separate parser guard. |
| `p` slice too short | `none` | Normally implied by `m ≠ M(n)` or `i > witnessBits n`, but stated as a separate parser guard. |
| invalid pad | `none` | Any nonzero bit in the final `witnessBits n - i` bits is invalid. |

## 5. Round-trip target

The later Lean theorem should not claim round-trip for arbitrary
`PrefixInput` values, because the current structure allows noncanonical fields:
wrong `tag`, arbitrary `padBits`, nonzero `pad`, or an ambient `m` unrelated to
`M(input.n)`.

The target should be a canonical round-trip theorem:

```text
if input is canonical, then
  parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput input) = some input
```

where `canonical` means:

- `input.tag = tagValue`;
- ambient length is `M input.n`;
- `input.padBits = witnessBits input.n - input.i`;
- every bit of `input.pad` is zero; and
- `input.x`, `input.i`, and `input.p` are placed in the slices specified above.

A stronger, and often cleaner, theorem is the field-level constructor form:

```text
parseTreeMCSPPrefixInput
  (encodeTreeMCSPPrefixFields n x i h_i p)
  = some (canonicalPrefixInput n x i h_i p)
```

where the encoder constructs zero padding itself.

## 6. Length convention theorem

Because this convention has no optional trailing bytes and no ignored padding,
the later theorem should be exact:

```text
if parseTreeMCSPPrefixInput y = some input, then m = M input.n
```

No alternative padded theorem is needed.  The only padding is the required-zero
suffix inside the fixed `witnessBits input.n` slot, and it is already included
in `M(input.n)`.

## 7. Malformed rejection theorem

The parser-specific theorem to prove later is:

```text
if parseTreeMCSPPrefixInput y = none, then
  PrefixExtensionLanguage parser m y = false
```

This should instantiate the already available abstract malformed-input theorem
for the concrete parser.  The parser implementation must make all malformed
layout cases return `none`, so malformed serialized strings become nonmembers
of the prefix-extension language rather than implicit promises.

## 8. Runtime claim level

Current honest runtime status:

- The parser scans at most `M(n)` bits: tag scan is constant, unary `n` scan is
  at most `n + 1`, field slicing totals `tableLen n + iWidth n + witnessBits n`,
  and zero-pad validation scans at most `witnessBits n` bits.
- Field slicing is linear in the ambient input length under a simple array/list
  cost model: `O(M(n))` total copied or inspected bits.
- Tag decoding costs `O(1)`.
- Unary `n` decoding costs `O(n + 1)`, hence `O(M(n))` because `n + 1` is a
  summand of `M(n)`.
- Fixed-width `i` decoding costs `O(iWidth n)`, hence `O(M(n))` because
  `iWidth n` is a summand of `M(n)`.

Claim level:

- **Paper-level now:** yes, the above gives a straightforward linear scan/slice
  argument in `M(n)`.
- **Structural Lean theorem possible:** yes, for arithmetic facts such as
  slice lengths, `tableLen n ≤ M(n)`, `n + 1 ≤ M(n)`, `iWidth n ≤ M(n)`, and
  `witnessBits n ≤ M(n)`.
- **Requires polynomial-time formalism:** any theorem that this parser is a
  polynomial-time Turing-machine routine, or that it compiles into
  `ComplexityInterfaces.NP`, still requires the missing X01-style formalism or
  a direct TM implementation.  This document does not supply that bridge.

## 9. Interaction with R1-B2a

### `treeMCSPPrefixAmbientLength`

This design instantiates the existing ambient-length shape with:

```text
overhead n = 8 + (n + 1) + iWidth n
witnessBits n = codec.witnessBits n
padBits n = 0
```

Then the helper length is definitionally the proposed `M(n)` up to addition
associativity/commutativity.  The existing `tableLen_le_treeMCSPPrefixAmbientLength`
style arithmetic remains the right theorem shape.

### `RuntimeAwarePrefixParser`

The following fields become real parser facts once the Lean parser lands:

- `parser`: the concrete `PrefixParser` using `tagValue`, `M`, and
  `parseTreeMCSPPrefixInput`.
- `malformed_inputs_rejected`: follows from the abstract malformed theorem plus
  the parser's `none` behavior for every malformed layout case.
- `length_convention_matches_M`: follows from the exact length check
  `m = M(input.n)` on every successful parse.

The field that remains staged is:

- `parser_polynomial_time_in_M`: still a named runtime obligation until the
  repository has a formal parser-cost-to-`NP_TM` bridge or a direct TM parser.

### `TreeMCSPPrefixRuntimeBudget`

The following fields become real or partly real from this design:

- `tableLen_le_M`: real arithmetic theorem, because `tableLen n` is a summand
  of `M(n)`.
- `malformed_inputs_rejected`: real theorem after concrete parser definition.
- `length_convention_matches_M`: real theorem after concrete parser definition.

The following remain staged outside this parser convention:

- `threshold_poly_in_M`: depends on the chosen threshold schedule.
- `witnessBits_poly_in_M`: depends on the concrete tree-circuit witness codec.
- `decode_polynomial_time_in_M`: depends on codec implementation/runtime model.
- `parser_polynomial_time_in_M`: needs formal runtime bridge or direct TM.
- `circuit_eval_polynomial_time_in_size`: needs runtime model for circuit eval.
- `truth_table_lookup_polynomial_time_in_M`: needs runtime model for lookup.
- `relation_polynomial_time_in_M`: combines codec decode, circuit evaluation,
  and truth-table enumeration; not supplied by this parser design.

## 10. Lean implementation plan

Because the verdict is `PARSER_CONVENTION_READY_FOR_LEAN`, the next Lean task is
narrow and parser-only.

- **File path:** add a new module under
  `pnp4/Pnp4/Frontier/ContractExpansion/`, for example
  `TreeMCSPPrefixParser.lean`, and list it in `lakefile.lean` as required by
  repository policy for pnp4 modules.
- **Definitions:**
  - `treeMCSPPrefixTagBits = 8`;
  - `treeMCSPPrefixTagValue = 0b10110010` or the equivalent bit-vector value;
  - `treeMCSPPrefixIWidth witnessBits n`;
  - `treeMCSPPrefixM witnessBits n`;
  - zero-padding predicate for a `BitVec` slice;
  - canonical field encoder for `(n, x, i, p)`;
  - `parseTreeMCSPPrefixInput`;
  - concrete `PrefixParser` wrapper for the tree-MCSP search problem.
- **Theorems:**
  - `tableLen_le_treeMCSPPrefixM`;
  - successful parse implies `m = treeMCSPPrefixM witnessBits input.n`;
  - successful parse implies decoded tag is `tagValue`;
  - successful parse implies `input.i ≤ witnessBits input.n`;
  - malformed tag/length/unary-`n`/out-of-range-`i`/short-slice/nonzero-pad
    cases return `none`;
  - canonical encode-parse round trip;
  - concrete malformed-input rejection via `PrefixExtensionLanguage_rejects_malformed`.
- **Expected time:** 1 focused day for parser definitions and arithmetic/slice
  theorems if suitable `BitVec` slice/append lemmas already exist; 2-3 days if
  basic slice infrastructure must be built locally.
- **Risk:** medium.  The convention is simple, but dependent widths
  (`tableLen n`, `iWidth n`, and `witnessBits n - i`) may require nontrivial
  Nat arithmetic and `BitVec` transport lemmas.  Runtime-to-`NP` claims remain
  out of scope.

## 11. Why this helps the P≠NP route

This does not prove a lower bound.

It may help prove `PrefixExtensionLanguage ∈ NP` for a concrete tree-MCSP prefix
language by replacing the current abstract parser boundary with a canonical
serialization, exact ambient length, malformed-input rejection behavior, and a
round-trip target.  That NP-membership result is a prerequisite for any honest
R1-C-style contract-expansion step, but this markdown design alone is not R1-C,
not a source theorem, not a gap witness, and not a P≠NP claim.
