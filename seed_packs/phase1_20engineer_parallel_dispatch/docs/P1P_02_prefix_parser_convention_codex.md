# P1P-02 — Prefix parser convention design

Handle: codex

## 1. Executive verdict

**PARSER_CONVENTION_READY_FOR_LEAN**

This document fixes a concrete serialization convention for the staged R1-B / R1-B1 / R1-B2a prefix-extension parser, without implementing Lean code.  The work is **infrastructure**, not lower-bound progress: it reduces the parser/serialization ambiguity that currently prevents an honest later proof that a concrete `PrefixExtensionLanguage` instance is in NP.

The convention is designed for the tree-MCSP search problem whose instance bits are the full truth table, so the ambient input length includes `tableLen n = 2^n`.  This is the key correction relative to any toy length convention such as `M(n) = n`, which cannot contain the truth-table instance.

## 2. Encoding layout

### Bit order and field order

All fields are serialized left-to-right in a single bitstring.  Numeric fields use most-significant-bit-first binary payloads.

The complete layout is:

```text
[tag : 8 bits]
[n : gamma(n + 1)]
[x : tableLen n bits]
[i : iWidth(n) bits]
[p : i bits]
[pad : witnessBits n - i bits]
```

where:

- `tag` is the fixed 8-bit domain separator `10110010`.
- `gamma(n + 1)` is Elias gamma encoding of the positive integer `n + 1`:
  - let `b = binary(n + 1)` with no leading zeros;
  - output `(|b| - 1)` zero bits followed by `b`;
  - this is self-delimiting and represents every natural `n` by encoding `n + 1 ≥ 1`.
- `tableLen n = 2^n`.
- `iWidth(n) = ceil_log2(witnessBits n + 1)`, i.e. the least `k` such that `witnessBits n + 1 ≤ 2^k`.
- `i` is an unsigned fixed-width integer occupying exactly `iWidth(n)` bits.
- `p` is the prefix payload occupying exactly `i` bits.
- `pad` occupies exactly `witnessBits n - i` bits.

### Required answers

- **Fixed-width or self-delimiting encoding for `n`?**
  `n` uses self-delimiting Elias gamma encoding of `n + 1`.  This lets the parser recover `n` before it knows `tableLen n`, `witnessBits n`, or `iWidth(n)`.

- **Fixed-width or self-delimiting encoding for `i`?**
  `i` uses fixed-width binary with width `iWidth(n) = ceil_log2(witnessBits n + 1)`.  This makes the total ambient length independent of the chosen prefix length `i`.

- **Where exactly does `x : TruthTable n` live?**
  `x` begins immediately after `tag ++ gamma(n + 1)` and occupies exactly `tableLen n = 2^n` bits.  For the concrete tree-MCSP search problem this is exactly the `problem.instanceBits n` slice.

- **Where exactly does `p : BitVec i` live?**
  Decode `i` immediately after the `x` slice.  Then `p` begins immediately after the fixed-width `i` field and occupies exactly the next `i` bits.

- **What is `pad`?**
  `pad` is the suffix of the fixed witness window not used by the active prefix.  It has length `witnessBits n - i`.  Operationally, the field `[p][pad]` is a full `witnessBits n`-bit window whose first `i` bits are active and whose remaining bits are inactive padding.

- **Are pad bits required zero or ignored?**
  Pad bits are **required zero**.  The semantic predicate ignores padding after parsing, but the parser must reject nonzero padding so that there is a unique canonical encoding and no promise-style ambiguity.

- **Malformed behavior?**
  The parser returns `none` for every malformed condition listed in section 4.  No malformed string is allowed to parse to a dummy/default `PrefixInput`.

## 3. Ambient length `M(n)`

For a fixed tree-MCSP threshold and witness encoding/codec, define:

```text
tagWidth       = 8
gammaLen(n+1)  = 2 * floor_log2(n + 1) + 1
tableLen n     = 2^n
iWidth(n)      = ceil_log2(witnessBits n + 1)
M(n)           = tagWidth + gammaLen(n + 1) + tableLen n + iWidth(n) + witnessBits n
```

This intentionally uses the full witness-window length `witnessBits n`, not the active prefix length `i`.  The `p`/`pad` split varies with `i`, but their combined length is always:

```text
i + (witnessBits n - i) = witnessBits n.
```

Therefore every well-formed encoding with parameter `n` has length exactly `M(n)`.

The required truth-table inclusion is immediate by monotonicity of natural-number addition:

```text
tableLen n ≤ 8 + gammaLen(n + 1) + tableLen n + iWidth(n) + witnessBits n = M(n).
```

So `tableLen_le_M` is preserved for all `n`, independently of threshold, prefix length, and padding.  The rejected toy convention `M(n) = n` is not viable because the instance field alone has length `tableLen n = 2^n`, which exceeds `n` for all sufficiently large `n` and is not even represented by the ambient string.

## 4. Parser behavior

The intended parser name is:

```text
parseTreeMCSPPrefixInput : BitVec m → Option (PrefixInput ... m)
```

Its behavior is deterministic and canonical:

1. Read the first 8 bits as `tag`.
2. Reject unless `tag = 10110010`.
3. Decode `gamma(n + 1)` immediately after the tag.
4. Let `n` be the decoded positive value minus one.
5. Compute `tableLen n`, `witnessBits n`, and `iWidth(n)`.
6. Reject unless the total ambient length `m` is exactly `M(n)`.
7. Slice exactly `tableLen n` bits into `x`.
8. Slice exactly `iWidth(n)` bits and decode unsigned `i`.
9. Reject unless `i ≤ witnessBits n`.
10. Slice exactly `i` bits into `p`.
11. Slice exactly `witnessBits n - i` bits into `pad`.
12. Reject unless every bit of `pad` is zero.
13. Reject unless no trailing bits remain; equivalently this is already enforced by `m = M(n)` plus the exact slices.
14. Return `some input` with:
    - `input.tag = 0b10110010` as a natural tag value;
    - `input.n = n`;
    - `input.x = x`;
    - `input.i = i`;
    - `input.prefixLength_le` from the checked inequality `i ≤ witnessBits n`;
    - `input.p = p`;
    - `input.padBits = witnessBits n - i`;
    - `input.pad = pad`.

Malformed cases are handled as follows:

| Case | Parser result | Reason |
| --- | --- | --- |
| bad tag | `none` | Wrong domain/version separator. |
| inconsistent length | `none` | After decoding `n`, require `m = M(n)`. |
| invalid `n` encoding | `none` | Gamma code must terminate, have a leading unary-zero run followed by a one, and have enough payload bits. |
| invalid `i` encoding | `none` | The fixed `iWidth(n)` slice must exist and decode as a canonical unsigned integer.  If `iWidth(n) = 0`, only the empty slice is valid and decodes to `0`, which can only happen when `witnessBits n = 0`. |
| `i > witnessBits n` | `none` | Violates the `PrefixInput.prefixLength_le` invariant. |
| `x` slice too short | `none` | Cannot form `TruthTable n`; in practice caught by `m = M(n)` and exact slicing. |
| `p` slice too short | `none` | Cannot form `BitVec i`; in practice caught by `m = M(n)` and exact slicing. |
| invalid pad | `none` | Any nonzero pad bit is rejected. |

## 5. Round-trip target

The later Lean target should prove a canonical encode/parse round trip:

```text
parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput n x i h_i p) =
  some {
    tag = 0b10110010,
    n = n,
    x = x,
    i = i,
    prefixLength_le = h_i,
    p = p,
    padBits = witnessBits n - i,
    pad = zeroVec (witnessBits n - i)
  }
```

This is the right direction to prove first.  The converse `encode(parse y) = y` is also true for accepted strings because pad bits are required zero and the numeric encodings are canonical, but it is not necessary for NP-membership staging.  If proof engineering around dependent equality of `prefixLength_le` is expensive, the first theorem can be stated with an extensional equality that compares `tag`, `n`, `x`, `i`, `p`, and zero padding while treating proof fields proof-irrelevantly.

## 6. Length convention theorem

Because this parser rejects all extra padding outside the fixed layout, the strongest R1-B2a theorem should be provable:

```text
if parseTreeMCSPPrefixInput y = some input then m = M(input.n).
```

This matches the existing `RuntimeAwarePrefixParser.length_convention_matches_M` and `TreeMCSPPrefixRuntimeBudget.length_convention_matches_M` fields exactly.

No alternative variable-length accepted-padding theorem is proposed.  Allowing arbitrary trailing padding would weaken length uniqueness and complicate `M(n)` accounting without helping the NP-membership goal.

## 7. Malformed rejection theorem

The later Lean theorem should be the existing language-level shape specialized to this concrete parser:

```text
if parseTreeMCSPPrefixInput y = none then
  PrefixExtensionLanguage parser m y = false.
```

At the abstract level this is already the theorem shape of `PrefixExtensionLanguage_rejects_malformed`.  The parser-specific work is to prove that every syntactic malformed case in section 4 indeed makes `parseTreeMCSPPrefixInput y = none`; the language rejection then follows immediately from the existing abstract theorem.

## 8. Runtime claim level

Current claims should be stated at three different levels:

- **Paper-level now:** the parser scans at most `M(n)` bits, performs exact field slicing over subranges of the same string, decodes `tag` in constant time, decodes `gamma(n + 1)` in `O(gammaLen(n + 1))`, and decodes `i` in `O(iWidth(n))`.  Zero-pad validation scans `witnessBits n - i ≤ witnessBits n` bits.  Therefore the whole parser is linear in `M(n)` under the usual RAM/list-scan model.
- **Structural Lean theorem possible next:** prove arithmetic and list/bitvector decomposition facts such as slice lengths, `tableLen_le_M`, `parse_some_length`, `parse_encode`, and per-field scan bounds expressed as simple natural-number inequalities.  These do not require a global TM model.
- **Requires polynomial-time formalism:** a real theorem that this parser is polynomial-time in the repository's canonical `ComplexityInterfaces.NP` / `NP_TM` sense still requires an X01-style bridge from local bitvector algorithms and cost bounds to the TM-level formalism.  Until that exists, `parser_polynomial_time_in_M` remains a named obligation, not a discharged NP theorem.

No TM-level runtime theorem is claimed here.

## 9. Interaction with R1-B2a

This convention maps cleanly onto the R1-B2a surfaces:

- `treeMCSPPrefixAmbientLength overhead witnessBits padBits n`:
  - set `overhead n = 8 + gammaLen(n + 1) + iWidth(n)`;
  - use the existing `witnessBits n` argument for the full `[p][pad]` witness window;
  - set the separate `padBits n = 0`, because variable inactive padding is already included inside the fixed witness window rather than as an additional global suffix.
- `RuntimeAwarePrefixParser`:
  - `parser` becomes the concrete parser built from this convention;
  - `malformed_inputs_rejected` becomes real via the existing abstract rejection theorem plus parser-case lemmas;
  - `length_convention_matches_M` becomes real via the exact-length parser theorem;
  - `parser_polynomial_time_in_M` remains staged until a polynomial-time formalism exists.
- `TreeMCSPPrefixRuntimeBudget`:
  - `tableLen_le_M` becomes real by the arithmetic theorem in section 3;
  - `malformed_inputs_rejected` and `length_convention_matches_M` become real for this parser;
  - `threshold_poly_in_M`, `witnessBits_poly_in_M`, and codec/runtime fields remain dependent on the chosen threshold and codec;
  - `decode_polynomial_time_in_M`, `circuit_eval_polynomial_time_in_size`, `truth_table_lookup_polynomial_time_in_M`, and `relation_polynomial_time_in_M` remain staged obligations, not consequences of parser design alone.

## 10. Lean implementation plan

Because the verdict is `PARSER_CONVENTION_READY_FOR_LEAN`, the next Lean task should be:

- **File path:** `pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean`
- **Definitions:**
  - gamma-code length and parser for `n + 1`;
  - `ceil_log2`/`iWidth` helper if no suitable existing helper is available;
  - `treeMCSPPrefixTag = 0b10110010`;
  - `treeMCSPPrefixOverhead` and `treeMCSPPrefixM`;
  - `encodeTreeMCSPPrefixInput`;
  - `parseTreeMCSPPrefixInput`;
  - a `PrefixParser` value using the concrete parse function.
- **Theorems:**
  - `tableLen_le_treeMCSPPrefixM`;
  - `parseTreeMCSPPrefixInput_encode`;
  - `parseTreeMCSPPrefixInput_some_length`;
  - parser-case rejection lemmas for bad tag, invalid gamma, length mismatch, out-of-range `i`, short slices, and nonzero padding;
  - a specialization of `PrefixExtensionLanguage_rejects_malformed` for the concrete parser.
- **Expected time:** 1–2 focused engineering days if bitvector slicing helpers are already adequate; 2–4 days if new dependent `BitVec` slice lemmas are needed.
- **Risk:** medium.  The mathematical convention is straightforward, but dependent lengths, proof irrelevance for `prefixLength_le`, and gamma-parser totality may create Lean proof overhead.  There is no lower-bound or NP endpoint risk if the implementation stays inside parser/length theorems.

## 11. Why this helps P≠NP route

This does **not** prove a lower bound.  It does **not** prove `P ≠ NP`, does **not** produce a `VerifiedNPDAGLowerBoundSource`, and does **not** instantiate R1-C.

It helps only by removing a concrete infrastructure blocker: with a fixed parser, fixed ambient length `M(n)`, canonical padding, malformed rejection, and round-trip target, a later task can honestly attempt to prove that the concrete prefix-extension language is in NP.  Such an NP-membership result is a prerequisite for any honest R1-C-style contract expansion, but it is not itself a lower-bound result.
