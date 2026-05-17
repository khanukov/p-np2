# P1P-02 — Prefix parser convention design

Handle: gpt55  
Branch observed: work  
Progress classification: Infrastructure / contract-expansion design. This is not a lower-bound proof and is not mainline mathematical progress toward the final separation target.

## 1. Executive verdict

**PARSER_CONVENTION_READY_FOR_LEAN**

This document chooses a concrete, implementation-ready bit convention for the staged tree-MCSP prefix parser. The design is intentionally conservative:

- the target parameter `n` is self-delimiting, so parsing does not need any external length parameter;
- the prefix length `i` is fixed-width after `n` is known, so the total ambient length depends only on `n`, not on `i`;
- the truth table `x : TruthTable n` is included as a contiguous `tableLen n = 2^n` slice;
- the variable prefix payload `p : BitVec i` is followed by zero padding inside a full `witnessBits n` prefix slot;
- malformed encodings return `none`.

The remaining staged item is not the parser convention. It is the global polynomial-time / TM-level verifier formalism needed to turn local parser and relation-runtime facts into an actual NP-membership theorem.

## 2. Encoding layout

### 2.1 Bit order and constants

All positions below use zero-based record offsets, scanning left to right. For a serialized vector `y : BitVec m`, offset `0` is the first serialized bit, offset `m - 1` is the last serialized bit.

Constants:

- `tagBits = 16`.
- `treeMCSPPrefixTag = 0x5045`, the 16-bit ASCII tag `PE`.
- Tag bit pattern, in left-to-right order: `0101000001000101`.
- `tableLen n = 2^n`.
- For the concrete tree-MCSP target, `instanceBits n = tableLen n`.
- `witnessBits n` is the witness-length function supplied by the selected tree-circuit witness codec.

### 2.2 Field order

The exact layout is:

| Field | Width | Offsets | Contents |
| --- | ---: | --- | --- |
| `tag` | `16` | `[0, 16)` | fixed pattern `0101000001000101` |
| `n` | `n + 1` | `[16, 16 + n + 1)` | unary self-delimiting code: `n` one-bits followed by one zero-bit |
| `x` | `tableLen n` | immediately after `n` | the truth table payload, coerced to `x : TruthTable n` |
| `i` | `witnessBits n + 1` | immediately after `x` | one-hot bounded code for a value in `{0, ..., witnessBits n}` |
| `p` | `i` | immediately after `i` | the active prefix payload, coerced to `p : BitVec i` |
| `pad` | `witnessBits n - i` | immediately after `p` through the end | zero padding inside the fixed witness-width prefix slot |

Equivalently, after parsing `n`, the suffix is:

`x[tableLen n] || iCode[witnessBits n + 1] || prefixSlot[witnessBits n]`,

where `prefixSlot = p || pad` and `pad` has length `witnessBits n - i`.

### 2.3 Fixed-width or self-delimiting choices

- `n` uses a self-delimiting unary code: `1^n 0`.
  - Reason: the parser can recover `n` without an external size bound or a preselected maximum parameter width.
  - Cost: `n + 1` bits, which is harmless because the record also contains the `2^n`-bit truth table.
- `i` uses a fixed-width code once `n` is known: exactly `witnessBits n + 1` bits.
  - The code is one-hot over positions `0` through `witnessBits n`.
  - The decoded value is the unique index `i` whose code bit is one.
  - Reason: this makes total ambient length a function of `n` only. A self-delimiting `i` code would make the total record length depend on `i` unless another compensating padding convention were introduced.

### 2.4 Exact location of `x : TruthTable n`

Let:

- `tagEnd = 16`;
- `nEnd = 16 + n + 1`;
- `xStart = nEnd`;
- `xEnd = xStart + tableLen n`.

Then `x` is exactly the slice `y[xStart, xEnd)`, interpreted as `TruthTable n` / `BitVec (tableLen n)` with the same left-to-right coordinate order.

### 2.5 Exact location of `p : BitVec i`

Let:

- `iStart = xEnd`;
- `iEnd = iStart + witnessBits n + 1`;
- `prefixStart = iEnd`;
- `pStart = prefixStart`;
- `pEnd = pStart + i`;
- `padStart = pEnd`;
- `recordEnd = prefixStart + witnessBits n`.

Then `p` is exactly the slice `y[pStart, pEnd)`, interpreted as `BitVec i` with the same left-to-right coordinate order.

### 2.6 What is `pad`?

`pad` is the inactive suffix of the fixed `witnessBits n` prefix slot:

`pad = y[padStart, recordEnd)`.

Its length is `padBits = witnessBits n - i`. It exists only so the ambient record length does not depend on the active prefix length `i`.

### 2.7 Are pad bits required zero or ignored?

Pad bits are **required zero**.

Rationale:

- Zero padding gives a canonical encoding.
- It prevents multiple serialized strings from representing the same parsed prefix input.
- It makes the parser's malformed behavior crisp: nonzero inactive bits are rejected rather than ignored.

### 2.8 Malformed behavior summary

The parser returns `none` for every syntactic violation. It never silently repairs a field and never accepts a noncanonical representation.

## 3. Ambient length `M(n)`

The proposed ambient length is:

`M(n) = 16 + (n + 1) + tableLen n + (witnessBits n + 1) + witnessBits n`.

Equivalently:

`M(n) = tableLen n + 2 * witnessBits n + n + 18`.

This intentionally does **not** use the rejected toy convention `M(n) = n`. The record contains the full truth table.

### 3.1 `tableLen n ≤ M(n)` status

`tableLen n ≤ M(n)` is preserved by direct summand inclusion:

`M(n) = tableLen n + nonnegativeOverhead(n)`,

where:

`nonnegativeOverhead(n) = 2 * witnessBits n + n + 18`.

Thus the truth-table scan over `2^n` entries is linear in the ambient record length up to this local arithmetic inequality.

### 3.2 Relation to `treeMCSPPrefixAmbientLength`

The staged R1-B2a shape is:

`treeMCSPPrefixAmbientLength overhead witnessBits padBits n = tableLen n + overhead n + witnessBits n + padBits n`.

This design instantiates it as:

- `overhead n = 16 + (n + 1) + (witnessBits n + 1) = witnessBits n + n + 18`;
- the `witnessBits n` summand is the full `prefixSlot = p || pad`;
- `padBits n = 0` for any additional global padding outside the prefix slot.

The `PrefixInput.pad` field is therefore not an extra ambient-length tail beyond `M(n)`. It is the inactive suffix of the fixed witness-width prefix slot.

## 4. Parser behavior

The future parser is named:

`parseTreeMCSPPrefixInput : BitVec m → Option (PrefixInput ... m)`.

High-level algorithm:

1. Check that the first 16 bits exist and equal the fixed tag.
2. Scan after the tag until the first zero bit; the number of preceding one-bits is `n`.
3. Compute `expected = M(n)`.
4. Reject unless `m = expected`.
5. Slice `x` as the next `tableLen n` bits.
6. Slice `iCode` as the next `witnessBits n + 1` bits.
7. Decode `iCode` as a one-hot value in `{0, ..., witnessBits n}`.
8. Slice the following `witnessBits n` bits as `prefixSlot`.
9. Split `prefixSlot` into `p` of length `i` and `pad` of length `witnessBits n - i`.
10. Reject unless every bit of `pad` is zero.
11. Return `some input` with:
    - `input.tag = treeMCSPPrefixTag`;
    - `input.n = n`;
    - `input.x = x`;
    - `input.i = i`;
    - `input.prefixLength_le` discharged by the one-hot code width;
    - `input.p = p`;
    - `input.padBits = witnessBits n - i`;
    - `input.pad = pad`.

Malformed cases:

| Case | Parser behavior |
| --- | --- |
| bad tag | `none` |
| inconsistent length, meaning `m ≠ M(n)` after decoding `n` | `none` |
| invalid `n` encoding, meaning no terminating zero after the tag before the record ends | `none` |
| invalid `i` encoding, meaning not exactly one one-bit in the `witnessBits n + 1`-bit `iCode` field | `none` |
| `i > witnessBits n` | `none`; this cannot occur from a valid one-hot code, but it is still the specified behavior for any failed bounded decode |
| `x` slice too short | `none`; practically caught by `m ≠ M(n)` before slicing |
| `p` slice too short | `none`; practically caught by `m ≠ M(n)` and the fixed prefix-slot length before splitting |
| invalid pad, meaning some inactive pad bit is one | `none` |

## 5. Round-trip target

The later Lean theorem should be a canonical round-trip theorem, not a theorem over arbitrary existing `PrefixInput` records.

Target statement in prose:

If a tuple `(n, x, i, p)` satisfies `i ≤ witnessBits n`, and `encodeTreeMCSPPrefixInput n x i p` uses the fixed tag, unary `n`, one-hot `i`, and zero inactive padding, then:

`parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput n x i p) = some canonicalInput(n, x, i, p)`.

A full theorem of the form `parse (encode input) = some input` for every `input : PrefixInput ... m` is too strong because `PrefixInput` permits arbitrary `tag`, arbitrary `padBits`, and arbitrary `pad` contents. The canonical encoder deliberately normalizes those fields to the fixed tag and zero padding.

A second theorem can be added later for parsed inputs:

If `parseTreeMCSPPrefixInput y = some input`, then encoding the semantic fields of `input` reproduces `y`. This parser-to-encoder direction is plausible precisely because pad bits are required zero.

## 6. Length convention theorem

The later Lean theorem should be:

If `parseTreeMCSPPrefixInput y = some input`, then `m = M(input.n)`.

This design does not allow extra trailing padding outside `M(n)`, so no alternative `m ≥ M(input.n)` theorem is needed. The only padding is the zero inactive suffix inside the fixed `witnessBits n` prefix slot, and its length is already included in `M(n)`.

## 7. Malformed rejection theorem

The parser-specific theorem to prove later is:

If `parseTreeMCSPPrefixInput y = none`, then the prefix-extension language built from this parser rejects `y`.

This should be discharged by instantiating the existing generic malformed-rejection theorem for `PrefixExtensionLanguage`. The new parser work only needs to prove that each concrete syntactic malformed case actually makes `parseTreeMCSPPrefixInput` return `none`.

Recommended theorem family:

- bad tag implies parse failure;
- unterminated unary `n` implies parse failure;
- decoded `n` with `m ≠ M(n)` implies parse failure;
- non-one-hot `iCode` implies parse failure;
- nonzero pad implies parse failure;
- parse failure implies language rejection.

## 8. Runtime claim level

Current defensible runtime claims:

- parser scans `O(M(n))` bits;
- field slicing costs `O(M(n))` total;
- tag checking costs `O(1)` because the tag width is fixed at 16 bits;
- unary `n` decoding costs `O(n + 1)`, which is `O(M(n))` because the record includes `tableLen n`;
- one-hot `i` decoding costs `O(witnessBits n + 1)`, which is `O(M(n))` because `witnessBits n` is an explicit summand of `M(n)`;
- zero-pad validation costs `O(witnessBits n)`, hence `O(M(n))`.

Claim level:

- **Paper-level:** ready now. The above scan/slice bounds are straightforward.
- **Structural Lean theorem:** possible now as arithmetic/list/vector traversal lemmas once a concrete parser representation is introduced.
- **Polynomial-time formalism:** still required for any final TM-level NP-membership theorem. The repository currently stages these runtime facts as named obligations rather than connecting them to a global machine-cost model.

Therefore this document does not claim an NP theorem. It only supplies the parser convention needed before such a theorem can be attempted honestly.

## 9. Interaction with R1-B2a

### 9.1 `treeMCSPPrefixAmbientLength`

This design maps directly onto the existing ambient-length helper:

- `overhead n` becomes the real arithmetic overhead for tag, unary `n`, and one-hot `i`:
  `overhead n = witnessBits n + n + 18`;
- `witnessBits n` remains the full prefix slot length;
- `padBits n = 0` for extra global padding;
- `tableLen_le_M` becomes immediate by the existing `tableLen` summand.

### 9.2 `RuntimeAwarePrefixParser`

Fields that become real after Lean implementation:

- `parser`: the concrete `PrefixParser` using the convention above;
- `malformed_inputs_rejected`: discharged through the generic malformed-rejection theorem plus parser failure lemmas;
- `length_convention_matches_M`: discharged by the parser's `m = M input.n` theorem.

Field that remains staged:

- `parser_polynomial_time_in_M`: can be supported by structural scan/slice lemmas, but it remains a `Prop` obligation until the repository provides or selects a machine-cost formalism.

### 9.3 `TreeMCSPPrefixRuntimeBudget`

Fields that become real or locally arithmetic:

- `tableLen_le_M`: real arithmetic theorem;
- `malformed_inputs_rejected`: real parser/language theorem;
- `length_convention_matches_M`: real parser theorem.

Fields still staged or codec-dependent:

- `threshold_poly_in_M`: depends on the chosen threshold schedule;
- `witnessBits_poly_in_M`: depends on the concrete circuit witness codec;
- `decode_polynomial_time_in_M`: depends on the concrete codec decoder;
- `parser_polynomial_time_in_M`: structural proof possible, TM-level proof staged;
- `circuit_eval_polynomial_time_in_size`: depends on the circuit model runtime formalism;
- `truth_table_lookup_polynomial_time_in_M`: structurally plausible but still tied to the global runtime model;
- `relation_polynomial_time_in_M`: depends on codec decode, circuit evaluation, and the truth-table agreement loop.

## 10. Lean implementation plan

Because the verdict is `PARSER_CONVENTION_READY_FOR_LEAN`, the next Lean task should be narrow and parser-only.

Proposed next task:

- File path: `pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPPrefixParser.lean`.
- Definitions:
  - fixed tag constant for this parser;
  - unary `n` encoder/decoder;
  - one-hot bounded `i` encoder/decoder;
  - ambient length `treeMCSPConcretePrefixM` matching `tableLen n + 2 * witnessBits n + n + 18`;
  - concrete `parseTreeMCSPPrefixInput`;
  - canonical `encodeTreeMCSPPrefixInput`.
- Theorems:
  - parser accepts canonical encoder output;
  - parser success implies `m = M input.n`;
  - parser success implies fixed tag and zero pad;
  - each malformed syntactic case returns `none`;
  - parser failure implies prefix-extension language rejection by applying the existing generic theorem;
  - `tableLen n ≤ M(n)`.
- Expected time: 1-2 focused engineering days if vector slicing utilities are already sufficient; 2-4 days if helper lemmas for `BitVec` slicing have to be built.
- Risk: medium. The mathematical design is simple, but Lean friction may arise from dependent vector slicing, proof transport across computed lengths, and the one-hot decoder's proof that `i ≤ witnessBits n`.

Do not include a full NP-membership theorem in this parser-only task. That belongs after the parser theorem surface and codec/runtime interfaces are audited.

## 11. Why this helps the P≠NP route

This does not prove a lower bound.

It does not construct a verified DAG lower-bound source, does not prove a weak search lower bound, and does not claim a final separation theorem.

It helps only in the following infrastructure sense: a concrete parser convention is a prerequisite for an honest proof that the prefix-extension language is in NP. Without an exact serialization, length convention, round-trip target, malformed rejection behavior, and runtime story, any claimed NP-membership theorem for this language would be under-specified. This design removes that parser ambiguity and leaves the remaining codec/runtime and machine-formalism obligations visible.

## Output summary

Task: P1P-02  
Handle: gpt55  
Branch: work  
Commit before: 4f39e76d7bc0f4fed22dad883267f40f1e7a6d1b  
Commit after: pending at authoring time  
Changed files: `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02_prefix_parser_convention_gpt55.md`  
Outcome: REPORT_LANDED  
Executive verdict: PARSER_CONVENTION_READY_FOR_LEAN  
M(n): `tableLen n + 2 * witnessBits n + n + 18`  
tableLen_le_M status: immediate by summand inclusion  
Parser convention: fixed 16-bit tag, unary self-delimiting `n`, contiguous truth table, one-hot fixed-width `i`, full witness-width prefix slot split as `p || zero pad`  
Malformed behavior: all malformed cases return `none`; parser failure implies language rejection  
Runtime status: paper-level scan/slice bounds now; structural Lean lemmas possible; TM-level NP runtime still staged  
Next Lean task: parser-only module with encoder/decoder, length, round-trip, malformed-failure, and `tableLen_le_M` theorems  
Commands run: `./scripts/check.sh`  
Scope violations: none
