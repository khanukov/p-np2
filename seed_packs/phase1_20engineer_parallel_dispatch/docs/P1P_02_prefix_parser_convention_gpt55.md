# P1P-02 — Prefix parser convention design

Handle: `gpt55`

Progress classification: **Infrastructure**.  This document fixes a parser and
serialization convention for the contract-expansion prefix language.  It does
not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it
must not be reported as P-vs-NP mainline progress.

## 1. Executive verdict

**PARSER_CONVENTION_READY_FOR_LEAN**

The convention below is intentionally conservative:

- exactly one ambient length per target parameter `n`;
- the full truth table is carried literally inside the input;
- the active prefix has variable logical length `i`, but occupies a fixed
  `witnessBits n`-bit region by zero-padding the inactive suffix;
- malformed strings are rejected by returning `none`.

This is ready for a first Lean implementation of parser/encoder correctness and
length facts.  It is not yet enough for `PrefixExtensionLanguage ∈ NP`, because
TM-level polynomial-time infrastructure and a concrete witness codec/runtime
proof are still separate obligations.

## 2. Encoding layout

### Conventions

All multi-bit natural-number fields are encoded **most-significant bit first**.
Bit offsets below are zero-based half-open intervals `[lo, hi)`.

For the concrete tree-MCSP target induced by `threshold` and `codec`, write:

```text
tableLen n     := 2^n
W(n)           := codec.witnessBits n
idxWidth(n)    := if W(n) = 0 then 0 else bitLength(W(n))
gammaLen(n)    := 2 * bitLength(n + 1) - 1
tagLen         := 8
TREE_PREFIX_V1 := 0b10110010 = 178
```

Here `bitLength(k)` is the unique positive width for `k > 0` satisfying
`2^(bitLength(k)-1) ≤ k < 2^bitLength(k)`.  Since `n + 1 > 0`, `gammaLen(n)` is
always defined.  For `idxWidth(n)`, the width is large enough to encode every
`i ≤ W(n)`.  If `W(n)=0`, the `i` field is empty and means `i=0`.

### Exact field order

The serialized input is:

```text
[tag : 8 bits]
[n   : Elias-gamma code of n+1]
[x   : tableLen n bits]
[i   : idxWidth(n) bits]
[p   : i bits]
[pad : W(n) - i bits]
```

Equivalently, after decoding `n`, the input has the following offsets:

```text
0                                      8
|--------------- tag -----------------|

8                                      8 + gammaLen(n)
|--------------- n code --------------|

8 + gammaLen(n)                       8 + gammaLen(n) + tableLen n
|--------------- x -------------------|

8 + gammaLen(n) + tableLen n          8 + gammaLen(n) + tableLen n + idxWidth(n)
|--------------- i -------------------|

8 + gammaLen(n) + tableLen n + idxWidth(n)
                                      8 + gammaLen(n) + tableLen n + idxWidth(n) + i
|--------------- p -------------------|

8 + gammaLen(n) + tableLen n + idxWidth(n) + i
                                      M(n)
|--------------- pad -----------------|
```

### Field details

- **`tag`** is fixed-width, exactly 8 bits.  The only accepted tag is
  `TREE_PREFIX_V1 = 0b10110010`.  The `PrefixInput.tag` field should be set to
  the natural number `178`.
- **`n`** is self-delimiting, encoded as the Elias-gamma code of `n+1`:
  `z` zero bits, followed by a one bit, followed by `z` payload bits.  The
  decoded positive integer is the `1 ++ payload` binary number of width `z+1`,
  and `n` is that value minus one.  This avoids any fixed global upper bound on
  target lengths.
- **`x : TruthTable n`** lives immediately after the `n` code and occupies
  exactly `tableLen n = 2^n` bits.  For the tree-MCSP search problem this is
  exactly `problem.instanceBits n`.
- **`i`** is fixed-width relative to the decoded `n`: it occupies
  `idxWidth(n)` bits and is decoded as an unsigned natural number.  If
  `W(n)=0`, this field is empty and decodes to `0`.
- **`p : BitVec i`** lives immediately after the `i` field and occupies exactly
  the first `i` bits of the fixed witness-prefix block.
- **`pad`** is the remaining inactive suffix of the fixed witness-prefix block,
  with length `W(n)-i`.  It is represented in `PrefixInput` as
  `padBits = W(n)-i` and `pad : BitVec padBits`.
- **Pad bits are required to be zero.**  They are semantically ignored by
  `PrefixExtendableInput`, but the parser rejects nonzero pad bits to make the
  serialization canonical and to support a clean `parse (encode input)` theorem.
- **Malformed behavior:** every malformed case listed in §4 returns `none`.
  There is no promise-language behavior and no ignored trailing garbage.

## 3. Ambient length `M(n)`

The proposed ambient length is:

```text
M(n) := 8 + gammaLen(n) + tableLen n + idxWidth(n) + W(n)
```

where `tableLen n = 2^n` and `W(n) = codec.witnessBits n`.

The active prefix length `i` does not appear in `M(n)` because the serialized
`p ++ pad` region always has fixed total length `W(n)`.  This preserves the
single-length-per-target convention expected by `RuntimeAwarePrefixParser`.

The required table-length inequality is immediate:

```text
tableLen n ≤ M(n)
```

because `M(n)` is `tableLen n` plus nonnegative overhead
`8 + gammaLen(n) + idxWidth(n) + W(n)`.  This intentionally rejects the toy
choice `M(n)=n`, which would fail to measure truth-table scanning against the
actual ambient input size.

## 4. Parser behavior

The future Lean parser should have the shape:

```text
parseTreeMCSPPrefixInput :
  BitVec m → Option (PrefixInput (treeMCSPSearchProblem threshold (ofCodec codec)) m)
```

Operational behavior:

1. Read the first 8 bits as `tag`.
2. Reject unless `tag = TREE_PREFIX_V1`.
3. Decode `n` from an Elias-gamma code beginning at offset 8.
4. Compute `M(n)` and reject unless the ambient length `m = M(n)`.
5. Slice `x` as the next `tableLen n` bits.
6. Decode `i` from the next `idxWidth(n)` bits, with the empty field decoding
   to `0` when `W(n)=0`.
7. Reject unless `i ≤ W(n)`.
8. Slice `p` as the next `i` bits.
9. Slice `pad` as the remaining `W(n)-i` bits.
10. Reject unless every pad bit is zero.
11. Return a `PrefixInput` whose `prefixLength_le` field is the proof of
    `i ≤ W(n)` obtained in step 7.

Malformed cases:

| Case | Parser result | Notes |
| --- | --- | --- |
| bad tag | `none` | Any 8-bit value other than `178`; also `m < 8`. |
| inconsistent length | `none` | After decoding `n`, reject if `m ≠ M(n)`. |
| invalid `n` encoding | `none` | No gamma terminator bit, insufficient gamma payload, or insufficient bits to finish the whole layout. |
| invalid `i` encoding | `none` | For `W(n)>0`, fewer than `idxWidth(n)` bits remain; for `W(n)=0`, any nonempty separate `i` field is impossible because `m=M(n)`. |
| `i > witnessBits n` | `none` | Reject unsigned values outside `[0, W(n)]`. |
| `x` slice too short | `none` | This is caught either during slicing or by `m ≠ M(n)`. |
| `p` slice too short | `none` | This is caught either during slicing or by `m ≠ M(n)`. |
| invalid pad | `none` | Any one bit in `pad` is invalid. |

## 5. Round-trip target

The later Lean target should be the full canonical round trip:

```text
parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput input) = some input
```

for canonical `input` values satisfying:

- `input.tag = TREE_PREFIX_V1`;
- `input.x` has length `tableLen input.n` through the tree-MCSP problem type;
- `input.prefixLength_le : input.i ≤ W(input.n)`;
- `input.padBits = W(input.n) - input.i`;
- `input.pad` is all zero.

A fully unrestricted round trip over arbitrary `PrefixInput` is too strong,
because the existing structure permits arbitrary `tag`, arbitrary `padBits`, and
arbitrary `pad` values.  Either define an encoder only for canonical inputs, or
prove the theorem for a `CanonicalTreeMCSPPrefixInput input` predicate.

A second useful theorem is parse-after-encode for raw fields:

```text
parseTreeMCSPPrefixInput
  (encodeTreeMCSPPrefixFields n x i p) = some canonicalInput
```

assuming `i ≤ W(n)`.

## 6. Length convention theorem

Because this convention permits no trailing padding outside `M(n)`, the intended
length theorem is exactly the R1-B2a field:

```text
if parseTreeMCSPPrefixInput y = some input then m = M(input.n)
```

No alternative padding-sensitive theorem is needed.  The only padding is the
internal zero suffix `pad : BitVec (W(n)-i)`, already counted inside `M(n)`.

## 7. Malformed rejection theorem

The parser-level theorem should instantiate the existing malformed-input field:

```text
if parseTreeMCSPPrefixInput y = none then
  PrefixExtensionLanguage parser m y = false
```

This should be discharged by the already existing generic theorem
`PrefixExtensionLanguage_rejects_malformed` once the concrete parser is packaged
as a `PrefixParser`.  The serialization-specific work is proving that every
bad tag, bad length, bad code, out-of-range `i`, short slice, or nonzero pad
indeed makes `parseTreeMCSPPrefixInput` return `none`.

## 8. Runtime claim level

Current claim level:

- **Parser scans `O(M(n))` bits:** paper-level now; a structural Lean theorem is
  plausible once parser helper functions expose a step/count measure.
- **Field slicing is `O(M(n))`:** paper-level now; structural Lean theorem
  possible for list/vector/bit-vector slice functions.
- **Tag decoding cost:** constant time in the paper model; structurally bounded
  by 8 inspected bits.
- **`n` decoding cost:** `O(gammaLen(n))`, hence `O(M(n))`.
- **`i` decoding cost:** `O(idxWidth(n))`, hence `O(M(n))` because
  `idxWidth(n)` is an addend of `M(n)`.
- **Pad validation cost:** `O(W(n))`, hence `O(M(n))` because `W(n)` is an
  addend of `M(n)`.
- **No TM-level runtime claim yet:** a proof of `PrefixExtensionLanguage ∈ NP`
  still requires an X01-style polynomial-time formalism or a direct verifier TM
  construction connected to `ComplexityInterfaces.NP` / `NP_TM`.

Thus the parser convention is implementation-ready, but its runtime status is
**paper-level plus future structural Lean arithmetic**, not a completed
polynomial-time verifier theorem.

## 9. Interaction with R1-B2a

This design maps cleanly onto the existing R1-B2a names.

### `treeMCSPPrefixAmbientLength`

Instantiate:

```text
overhead(n)    := 8 + gammaLen(n) + idxWidth(n)
witnessBits(n) := codec.witnessBits n
padBits(n)     := 0
```

Then:

```text
treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n
  = tableLen n + (8 + gammaLen(n) + idxWidth(n)) + W(n) + 0
```

which is definitionally the same up to associativity/commutativity of addition
as the proposed `M(n)`.

The `tableLen_le_M` field becomes a real arithmetic theorem.

### `RuntimeAwarePrefixParser`

Fields that become real after Lean implementation:

- `parser`: the concrete `PrefixParser` packaged around
  `parseTreeMCSPPrefixInput`;
- `malformed_inputs_rejected`: follows from the generic malformed rejection
  theorem for `PrefixExtensionLanguage`;
- `length_convention_matches_M`: proved from the parser's explicit
  `m = M(n)` check.

Field that remains staged:

- `parser_polynomial_time_in_M : Prop`, until a non-placeholder runtime
  formalism or direct TM parser proof exists.

### `TreeMCSPPrefixRuntimeBudget`

Fields that become real or closer to real from this design:

- `tableLen_le_M`: real arithmetic theorem;
- `malformed_inputs_rejected`: real theorem via parser failure;
- `length_convention_matches_M`: real parser theorem;
- `parser_polynomial_time_in_M`: paper-level/structural only, still staged as
  a `Prop` field.

Fields that remain outside this parser convention:

- `threshold_poly_in_M`;
- `witnessBits_poly_in_M`;
- `decode_polynomial_time_in_M`;
- `circuit_eval_polynomial_time_in_size`;
- `truth_table_lookup_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`.

Those require a concrete tree-circuit witness codec and the global runtime
bridge, not just input serialization.

## 10. Lean implementation plan

Since the verdict is `PARSER_CONVENTION_READY_FOR_LEAN`, the next Lean task can
be narrow and source-only in the contract-expansion frontier.

- **File path:** `pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean`
- **Definitions:**
  - `treePrefixTag : Nat := 178`;
  - `bitLength`, `gammaLen`, `idxWidth` helper definitions if no suitable
    reusable definitions exist;
  - `treeMCSPPrefixM threshold codec n` matching this document;
  - `encodeTreeMCSPPrefix...` for canonical raw fields or canonical inputs;
  - `parseTreeMCSPPrefixInput`;
  - a packaged `treeMCSPConcretePrefixParser`.
- **Theorems:**
  - `tableLen_le_treeMCSPPrefixM`;
  - parser bad-tag rejection;
  - parser bad-length rejection;
  - parser nonzero-pad rejection;
  - `parse_encodeTreeMCSPPrefix...` for canonical inputs/fields;
  - `parseTreeMCSPPrefixInput_length_convention`;
  - `parseTreeMCSPPrefixInput_malformed_rejected` via the generic language
    theorem.
- **Expected time:** 1-2 focused engineering days if bit-vector slicing helpers
  are already usable; 2-4 days if small helper lemmas about bit lengths,
  half-open slices, and dependent `BitVec` casts must be built.
- **Risk:** medium.  The mathematical convention is simple, but dependent
  lengths (`tableLen n`, `idxWidth(n)`, `W(n)-i`) may require careful helper
  lemmas and casts.  Runtime fields should remain staged unless a real runtime
  framework is in scope.

## 11. Why this helps the P≠NP route

This does **not** prove a lower bound.  It does **not** construct
`VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, a source theorem,
a gap witness, an endpoint, or an R1-C extraction.

It helps only by removing one infrastructure blocker: the prefix-extension
language can now have a concrete, canonical parser/serialization target.  If a
later Lean implementation proves the parser correctness, length convention, and
malformed rejection facts, then one prerequisite for an honest proof that
`PrefixExtensionLanguage ∈ NP` is reduced.  That NP-membership proof still also
needs a concrete witness codec, polynomial witness-size and relation-runtime
facts, and a bridge to the repository's TM-based `NP` definition.
