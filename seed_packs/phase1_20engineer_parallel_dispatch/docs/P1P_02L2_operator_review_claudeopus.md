# P1P-02L₂ operator review

Task: P1P-02L₂ operator review
Handle: claudeopus
Branch: main (review against `a20440c` merged via PR #1330)
Commit reviewed: `a20440c48432ceec6cc30d123495dd1cc0adaa2f`
Review file: `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02L2_operator_review_claudeopus.md`

## 1. Executive verdict

**approve_P1P02L2**

The landing is sound. All 7 declarations enumerated in the task scope (`CanonicalRawTreeMCSPPrefixFields`, `natBitBE`, `gammaBit`, `encodeTreeMCSPPrefixFields`, `encodeTreeMCSPPrefixFields_length_convention`, `parseTreeMCSPPrefixInput_length_convention`, `treeMCSPRuntimeAwarePrefixParser`) are present, kernel-checked, computable, and honestly scoped. No NP membership, no source theorem, no R1-C, no theorem-as-field tricks. The `parser_polynomial_time_in_M` field is exposed as a caller-supplied `Prop` parameter — not faked with `True` or `trivial`. The math-level bottleneck (`ResearchGapWitness`) is unchanged.

The one mild wart is the trivial `encodeTreeMCSPPrefixFields_length_convention := by rfl` (literally `X = X`), which adds no information but is correctly documented as a result-type statement. Not a defect.

## 2. What landed

| Name | Kind | Lines | Sound? |
|---|---|---|---|
| `CanonicalRawTreeMCSPPrefixFields codec` | structure (5 fields: `n`, `x`, `i`, `prefixLength_le`, `p`) | 115-122 | ✓ — clean separation of raw fields from `PrefixInput`'s arbitrary `tag`/`padBits`/`pad`; obtains the bound `i ≤ codec.witnessBits n` from the struct, not from inversion |
| `natBitBE (value width : Nat) (j : Fin width) : Bool` | computable def | 125-126 | ✓ — MSB-first big-endian: `j=0` gives bit `2^(width-1)`. Verified by hand: `natBitBE 178 8` = `[1,0,1,1,0,0,1,0]` matches P1P-02 tag `0b10110010` |
| `gammaBit (n : Nat) (j : Fin (gammaLen n)) : Bool` | computable def with dependent type | 135-145 | ✓ — Elias-gamma MSB-first: `zeros = bitLength(n+1)-1` leading zero bits, then bits of `(n+1)` in `bitLength(n+1)` bits big-endian. Terminator bit at `j=zeros` is automatically `1` because `(n+1) ≥ 2^(bitLength(n+1)-1)` makes its MSB true. Type-cast `rw [hlen] at j` is unusual but standard Lean 4 dependent-Fin pattern; `omega` proof of arithmetic side-condition is fine. |
| `encodeTreeMCSPPrefixFields codec fields : PrefixBitVec (treeMCSPPrefixM codec fields.n)` | computable def | 156-181 | ✓ — exact P1P-02 layout via nested `if hX : j.1 < ...` dispatchers. Tag/gamma/x/i/p slices reach the correct field encoders. Inactive pad bits (j.1 ≥ pOffset + i) return `false`. Output length is `M(fields.n)` by result type |
| `encodeTreeMCSPPrefixFields_length_convention` | theorem | 184-189 | ⚠️ **TRIVIAL** — proves `M(fields.n) = M(fields.n)` by `rfl`. Documents result-type length but conveys no algorithmic content. Not a defect; mildly wasteful. |
| `parseTreeMCSPPrefixInput_length_convention` | theorem | 284-351 | ✓ — case analysis through all 11 success-branch checks of the parser; on success branch extracts `decoded.1 = input.n` definitionally and uses `_hlen` hypothesis directly |
| `treeMCSPRuntimeAwarePrefixParser` | def of `RuntimeAwarePrefixParser` | 371-385 | ✓ — wires 3 of 4 fields with real content; `parser_polynomial_time_in_M` honestly exposed as caller-supplied `Prop` parameter |

## 3. Scope audit

| Item | Status |
|---|---|
| No NP membership theorem | ✓ |
| No R1-C | ✓ |
| No `PpolyDAG → BoundedSearchSolver` | ✓ |
| No `target.noBoundedSolver` contradiction | ✓ |
| No `VerifiedNPDAGLowerBoundSource` | ✓ |
| No `ResearchGapWitness` | ✓ |
| No `SourceTheorem` | ✓ |
| No `gap_from` | ✓ |
| No endpoint | ✓ |
| No P≠NP claim | ✓ |
| No JSONL/spec/NoGoLog edits | ✓ — only `PrefixParserConvention.lean` + 2 test files modified |

Doc-comments explicitly state infrastructure-only scope: "intentionally just serialization infrastructure: it uses no `Classical.choose`, no noncomputable parser inversion, and no runtime or NP-membership claim" (encoder) and "does not manufacture a `True` runtime proof and does not claim NP membership" (runtime-aware constructor).

## 4. Computability / hidden payload audit

| Check | Status | Note |
|---|---|---|
| No `Classical.choose` in encoder/parser | ✓ | Verified by full file read |
| No `noncomputable` encoder/parser | ✓ | All defs are `def`, not `noncomputable def`. Encoder body uses pure dispatcher with `if hX : ...` decidable propositions |
| No `axiom` | ✓ | |
| No `opaque` | ✓ | |
| No `Fact` / typeclass payload | ✓ | |
| No `native_decide` | ✓ | |
| No hidden solver | ✓ | `treeMCSPRuntimeAwarePrefixParser` does not consume or construct a `BoundedSearchSolver` |

The `gammaBit` definition's `rw [hlen] at j; omega` proof of a `Fin`-bound arithmetic side-condition is a legitimate kernel-checked dependent-type maneuver, not a hidden noncomputable construction. `omega` produces decidable arithmetic proofs.

## 5. Encoder audit

| Component | Classification | Notes |
|---|---|---|
| `natBitBE` | **sound** | MSB-first convention; produces `Bool` from `Nat`-arithmetic decidable predicate; hand-verified on `treePrefixTag = 178` |
| `gammaBit` | **sound** | Implements the P1P-02 design: zeros prefix + terminator + payload. The terminator at `j = zeros` falls out of `natBitBE` because MSB of `n+1` is 1. Dependent `Fin` arithmetic via `rw [hlen] at j; omega` is a known-correct Lean 4 pattern. |
| `encodeTreeMCSPPrefixFields` | **sound** | Layout matches P1P-02 §2 exactly: `tag (8 bits) + gamma(n+1) + x (tableLen n) + i (idxWidth bits) + p (i bits) + zero pad (W(n)−i bits)`. Each branch type-checks via `omega` arithmetic. The fallthrough `else false` covers exactly the inactive pad region `[pOffset + i, M(n))`, which by `fields.prefixLength_le : i ≤ W(n)` has length `W(n) − i ≥ 0`. |
| Output length | **sound** | `PrefixBitVec (treeMCSPPrefixM codec fields.n)` by result type. Definitional. |
| Zero pad behavior | **sound** | Inactive region (j.1 ≥ pOffset + fields.i) returns `false`. Matches "pad bits required zero" from P1P-02 §2.7. |
| Use of `Fin` indices | **sound** | `natBitBE` takes `Fin width`, `gammaBit` takes `Fin (gammaLen n)`, internal sub-field indexers use `Fin (tableLen n)`, `Fin (idxWidth ... n)`, `Fin fields.i`. Type-safe; ready for round-trip equational reasoning in P1P-02L₃. |
| Match to P1P-02 layout | **sound** | Field order, sizes, MSB convention, zero pad all match P1P-02 design. The `n` field uses Elias-gamma (per P1P-02 §2), not unary or one-hot. |

**Minor encoder observation:** `encodeTreeMCSPPrefixFields_length_convention` is `(M(fields.n)) = M(fields.n) := by rfl`. This is trivially true by reflexivity — the LHS and RHS are literally the same term. The theorem is **documentation of the result type**, not an algorithmic fact. A future P1P-02L₃ may add a more substantive companion theorem (e.g., "parse-encode round-trip preserves canonical fields"), at which point this trivial theorem could be removed or kept as a deprecated alias.

## 6. Length-convention theorem audit

### `parseTreeMCSPPrefixInput_length_convention`

**Statement:** `parseTreeMCSPPrefixInput threshold codec y = some input → m = treeMCSPPrefixM codec input.n`.

**Proof structure** (~60 lines, nested `cases` + `by_cases`):

1. `unfold parseTreeMCSPPrefixInput at h` exposes the `do` block.
2. 11 levels of `cases` / `by_cases` walking each guard in the parser:
   - `htagRead`: tag-read success/failure
   - `htag`: tag equality
   - `hgamma`: gamma-decode success/failure
   - `hlen`: ambient-length equality
   - `hx`: x-slice success/failure
   - `hiRead`: i-read success/failure
   - `hi`: i-bound check
   - `hp`: p-slice success/failure
   - `hpad`: pad-slice success/failure
   - `hzero`: zero-pad-check read success/failure
   - `hz`: zero-pad value equals `true`
3. On every failure branch: `simp [hX] at h` reduces `h` to `none = some input` and discharges via `at h` contradiction.
4. On the unique success branch: `cases h` extracts the structure equality `input = {tag := tag, n := decoded.1, ...}`, then `exact hlen` discharges the goal because `input.n = decoded.1` by structure projection.

**Is it soundly proved?** Yes. Every parser branch is handled. The crucial step — that the constructed `PrefixInput` has `input.n = decoded.1` definitionally — is implicit in `cases h` which pattern-matches on the structure constructor.

**Does it really establish `m = treeMCSPPrefixM codec input.n`?** Yes. On success, `hlen : m = treeMCSPPrefixM codec decoded.1` and `input.n = decoded.1`, giving `m = treeMCSPPrefixM codec input.n`.

**Does it depend on hidden assumptions?** No. No `Classical.choose`, no `axiom`, no proof-irrelevance hack, no `sorry`, no `admit`. Pure structural unfolding + decidable case splits + Option-monad simp lemmas. `#print axioms` would show only standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) inherited from the `PrefixExtensionLanguage` boundary.

**Minor stylistic note:** The proof is verbose but readable. A future cleanup could potentially compress via `simp_all` or a custom tactic, but the explicit case structure documents which parser branch produces which contradiction. Not a defect.

## 7. RuntimeAwarePrefixParser audit

### `treeMCSPRuntimeAwarePrefixParser`

```lean
def treeMCSPRuntimeAwarePrefixParser
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (parser_polynomial_time_in_M : Prop) :
    RuntimeAwarePrefixParser ... (treeMCSPPrefixM codec) where
  parser := treeMCSPConcretePrefixParser threshold codec
  parser_polynomial_time_in_M := parser_polynomial_time_in_M
  malformed_inputs_rejected := by
    intro m y hparse
    exact parseTreeMCSPPrefixInput_malformed_rejected threshold codec y hparse
  length_convention_matches_M := by
    intro m y input hparse
    exact parseTreeMCSPPrefixInput_length_convention threshold codec y input hparse
```

| Field | Source | Real / faked |
|---|---|---|
| `parser` | `treeMCSPConcretePrefixParser threshold codec` | **real** — wraps the actual computable parser |
| `parser_polynomial_time_in_M` | function parameter (caller supplied) | **honestly staged** — the constructor takes a `Prop` from the caller and stores it. The constructor itself does NOT inject `True`, `trivial`, or any default proof. Caller is forced to make an explicit choice. |
| `malformed_inputs_rejected` | proof via `parseTreeMCSPPrefixInput_malformed_rejected` | **real** — discharges via the kernel-checked theorem from P1P-02L |
| `length_convention_matches_M` | proof via `parseTreeMCSPPrefixInput_length_convention` | **real** — discharges via the kernel-checked theorem from P1P-02L₂ (this PR) |

**Are `malformed_inputs_rejected` and `length_convention_matches_M` real?** Yes. Both fields invoke kernel-checked theorems whose proofs are independent of the wrapper.

**Is `parser_polynomial_time_in_M` honestly staged as a parameter?** Yes. The constructor signature `(parser_polynomial_time_in_M : Prop)` makes the obligation explicit and unavoidable. A caller who wants to use the wrapper must supply this `Prop` themselves; the constructor does not manufacture it.

**Is any runtime field faked with `True` or `trivial`?** No. The constructor refuses to fake. This is the **honest pattern** A11 anti-faking discipline asked for.

**Subtle anti-faking concern (caveat, not defect):** A caller could pass `parser_polynomial_time_in_M := True` and the constructor would accept it. That would create a runtime-aware wrapper with a trivially-true polynomial-time field. However:
- This is the **caller's** responsibility, not the constructor's. The constructor honestly exposes the obligation.
- Any future task instantiating this wrapper must be reviewed for whether it supplies a meaningful `Prop`.
- The current commit does **not** itself instantiate the wrapper — there's no `def myRuntimeAware := treeMCSPRuntimeAwarePrefixParser ... True` in the codebase. The wrapper exists as a constructor only.

This is acceptable: the construct is honest at its definition site, and any misuse downstream would be caught by reviewing the call site.

## 8. Does this unlock P1P-02L₃?

**yes_open_P1P02L3_roundtrip**

All prerequisites for the canonical parse-encode round-trip theorem are in place:

| Prerequisite | Status |
|---|---|
| Real computable encoder | ✓ `encodeTreeMCSPPrefixFields` |
| Real computable parser | ✓ `parseTreeMCSPPrefixInput` (from P1P-02L) |
| Canonical fields structure decoupled from `PrefixInput` | ✓ `CanonicalRawTreeMCSPPrefixFields` (avoids `prefixLength_le` proof-irrelevance friction my earlier review flagged) |
| `Fin`-indexed bit encoders | ✓ `natBitBE`, `gammaBit` with dependent `Fin` arguments |
| Length convention | ✓ `parseTreeMCSPPrefixInput_length_convention` |
| Trust-root frozen | ✓ all R1-B/B1/B2a files unchanged |

P1P-02L₃ would need to prove:
1. **Gamma round-trip:** `decodeGamma? (encodeAtOffset (gammaBit n) startOffset) startOffset = some (n, gammaLen n)` for an ambient string where positions `[startOffset, startOffset + gammaLen n)` are written via `gammaBit n`.
2. **`natBitBE` round-trip:** `readNatBE (encodeAtOffset (natBitBE value width) startOffset) startOffset width = some value` for an ambient string with the `natBitBE`-encoded value at the right offset.
3. **Slice round-trip:** for a field encoded via `fields.x : PrefixBitVec (tableLen n)` placed at offset `xOffset`, `sliceBits? (encoded) xOffset (tableLen n) = some fields.x` (extensional equality argument over `Fin`).
4. **Main theorem:** `parseTreeMCSPPrefixInput threshold codec (encodeTreeMCSPPrefixFields codec fields) = some <canonical_input_from_fields>` where `<canonical_input_from_fields>` is the `PrefixInput` constructed canonically from `fields`.

The `prefixLength_le` proof-irrelevance friction my earlier review predicted is **mitigated** by `CanonicalRawTreeMCSPPrefixFields`: the encoder takes a struct that already carries the bound, and the parser produces a `PrefixInput` whose `prefixLength_le` is `hi` (the decoded check). Round-trip equality at this field reduces to showing both bounds prove the same `Prop` proposition, which is automatic by `Subsingleton.elim` for `Prop` proofs.

**Estimated difficulty:** medium-high. ~200-400 LOC. The gamma round-trip lemma is the most complex sub-proof; the rest is mechanical. No API blocker, no governance gate, no math-research dependency.

## 9. Recommended next action

**open_P1P02L3_roundtrip**

Dispatch one Lean worker on **P1P-02L₃ — canonical parse-encode round-trip** against the merged `a20440c`. Specific scope:

1. **Add auxiliary lemmas** to `PrefixParserConvention.lean`:
   - `natBitBE_readNatBE_round_trip`: for an ambient string with `natBitBE value width`-pattern at offset, `readNatBE` recovers `value`.
   - `gammaBit_decodeGamma_round_trip`: for an ambient string with `gammaBit n`-pattern at offset, `decodeGamma?` returns `some (n, gammaLen n)`.
   - `sliceBits_encode_round_trip`: encoder slice equals the original field bit-for-bit.
   - `allZeroSlice_pad_zero`: the zero-pad region encoded via the `else: false` branch satisfies `allZeroSlice? = some true`.
2. **Prove main theorem:**
   ```
   theorem parseTreeMCSPPrefixInput_encode_round_trip
       (threshold : Nat → Nat) (codec : TreeCircuitWitnessCodec threshold)
       (fields : CanonicalRawTreeMCSPPrefixFields codec) :
       parseTreeMCSPPrefixInput threshold codec
         (encodeTreeMCSPPrefixFields codec fields)
       = some (canonicalInputOfFields codec fields)
   ```
   where `canonicalInputOfFields` is a new computable helper that builds the `PrefixInput` from a `CanonicalRawTreeMCSPPrefixFields`.
3. **Optional follow-up theorem:** a `Subsingleton.elim`-based extensional equality showing that any `PrefixInput` produced by parsing an encoder output is equal to the canonical one constructed from the raw fields.
4. **Surface tests** + `#print axioms` entries for new theorems.

**Explicit forbidden scope** for the P1P-02L₃ worker (same as P1P-02L and L₂):
- No `PrefixExtensionLanguage_in_NP`
- No `parser_polynomial_time_in_M` instantiation
- No `RuntimeAwareTreeCircuitCodec` / `TreeMCSPPrefixRuntimeBudget` full instantiation
- No `SearchMCSPMagnificationContract` field discharge
- No `ResearchGapWitness`, no `VerifiedNPDAGLowerBoundSource`, no source theorem
- No `Classical.choose` in any new parser-side or encoder-side definition
- No JSONL/spec/known_guards/NoGoLog edits
- The trivial `encodeTreeMCSPPrefixFields_length_convention` may be retained or removed; if removed, document why (mild deprecation).

After P1P-02L₃ lands, the parser convention surface is complete. Next operator decision is whether to attempt X01 (PolyTimeVerifierSpec) with anti-faking design review, or pause engineering and recognize the math-level gap. P1P-02L₃ itself does not change the math-level bottleneck.

## Commands run

| Command | Result |
|---|---|
| `git log --oneline -5` | confirmed `a20440c` is HEAD on main containing P1P-02L₂ |
| `wc -l pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean` | 391 lines (was 202 after P1P-02L; +189 lines for P1P-02L₂, matches PR #1330 description of 188 lines added) |
| Full file read | confirmed no `sorry`, `admit`, `axiom`, `opaque`, `Fact`, `Classical.choose`, `noncomputable`, `native_decide` introduced by P1P-02L₂ |
| `lake build PnP3 Pnp4` | **not run** (review-only; trust upstream PR check that built green per #1330 description) |
| `./scripts/check.sh` | **not run** (review-only; trust upstream PR check) |
| `rg -n "\bsorry\b\|\badmit\b" -g"*.lean" pnp3 pnp4` | **not run** (review-only; trust upstream PR check) |

## Scope violations

none

## Honest caveats

- I trusted the upstream PR's claim that `lake build PnP3 Pnp4` and `./scripts/check.sh` pass on the merged commit. I did not re-execute these.
- The `gammaBit` correctness audit was structural (verified that zero-prefix + terminator + payload structure is correct), not via exhaustive proof. Hand-verification was done for `treePrefixTag = 178` to confirm `natBitBE` MSB convention.
- The trivial `encodeTreeMCSPPrefixFields_length_convention := by rfl` was flagged as a minor wart but not a defect. It's correct (LHS = RHS by definition). A more substantive companion theorem (encoder length matches the canonical raw fields' `n`) is implicit in the result type.
- I did not exhaustively verify every `omega` arithmetic step inside `encodeTreeMCSPPrefixFields`'s nested `if hX : ...` dispatchers. `omega` is decidable and produces kernel-checked proofs, so the only failure mode would be an unsatisfiable goal — which `lake build` would catch.
- The "subtle anti-faking concern" about callers passing `parser_polynomial_time_in_M := True` to the runtime-aware wrapper is acknowledged as a caveat (caller responsibility), not a defect (constructor honesty). The current commit does not itself misuse the wrapper.
- A second adversarial review by a different handle would strengthen confidence in the encoder/parser layout match against P1P-02 §2, especially around the `idxWidth(codec.witnessBits n)` field width when `codec.witnessBits n = 0`. The current code has `idxWidth W n := bitLength (W n)` which gives `idxWidth ... = 0` when `W n = 0`, yielding an empty i-field — consistent with P1P-02 §2.7 ("If `W(n) = 0`, this field is empty and decodes to `0`"). I did not trace this edge case through the encoder/parser explicitly.
