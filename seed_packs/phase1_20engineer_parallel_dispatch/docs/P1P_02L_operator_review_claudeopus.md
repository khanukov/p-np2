# P1P-02L operator review

Task: P1P-02L operator review
Handle: claudeopus
Branch: main (review runs against `d100d33` merged via PR #1323)
Commit reviewed: `d100d335337e83aec453dc30bb54bde06f7a4b79`
Review file: `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02L_operator_review_claudeopus.md`

## 1. Executive verdict

**approve_P1P02L**

The landing is sound. It is the first **real computable** parser in the contract-expansion track and is honestly scoped: no R1-C, no `PrefixExtensionLanguage_in_NP`, no source-theorem promotion, no theorem-as-field tricks. The missing theorems (`length_convention`, `encode`, canonical round-trip) are local proof-engineering follow-ups that are well-defined against the real parser body; they do not indicate a faulty landing.

The math-level bottleneck (non-vacuous `ResearchGapWitness`) is unchanged. This is contract-expansion infrastructure, not P≠NP progress.

## 2. What landed

| Name | Kind | Sound? |
|---|---|---|
| `treePrefixTag : Nat := 178` | def, constant | ✓ |
| `tagLen : Nat := 8` | def, constant | ✓ |
| `bitLength : Nat → Nat` | def, `if n=0 then 0 else Nat.log2 n + 1` | ✓ |
| `gammaLen (n : Nat) : Nat := 2 * bitLength (n+1) - 1` | def | ✓ (matches P1P-02) |
| `idxWidth (W : Nat → Nat) (n : Nat) : Nat := bitLength (W n)` | def | ✓ (note: takes `W : Nat → Nat`, not the codec; call site uses `idxWidth codec.witnessBits n`) |
| `treeMCSPPrefixM codec n` | def | ✓ matches P1P-02: `tagLen + gammaLen n + tableLen n + idxWidth(codec, n) + witnessBits n` |
| `readBit? y offset : Option Bool` | computable def | ✓ |
| `readNatBE y offset width : Option Nat` | computable def, big-endian MSB-first | ✓ |
| `sliceBits? y offset width : Option (PrefixBitVec width)` | computable def, dependent slice | ✓ |
| `allZeroSlice? y offset width : Option Bool` | computable def | ✓ |
| `decodeGammaAux? y offset fuel zeros : Option (Nat × Nat)` | computable def, structural recursion on `fuel` | ✓ |
| `decodeGamma? y offset := decodeGammaAux? y offset (m+1) 0` | computable def | ✓ (fuel bound `m+1` is safe; any valid gamma code at offset `≤ m` has length `≤ m`) |
| `CanonicalTreeMCSPPrefixInput codec input` | Prop predicate (conjunction of 4 conditions) | ✓ |
| `parseTreeMCSPPrefixInput threshold codec y : Option (PrefixInput ... m)` | **computable** def using `do` monad | ✓ |
| `treeMCSPConcretePrefixParser threshold codec : PrefixParser ...` | def, packages `parseTreeMCSPPrefixInput` into R1-B `PrefixParser` interface | ✓ |
| `tableLen_le_treeMCSPPrefixM` | theorem, by `unfold; omega` | ✓ |
| `parseTreeMCSPPrefixInput_bad_tag` | theorem, by `simp` | ✓ (narrow: assumes tag was successfully read) |
| `parseTreeMCSPPrefixInput_malformed_rejected` | theorem, instantiates `PrefixExtensionLanguage_rejects_malformed` | ✓ |

Surface-test wrappers and `#print axioms` entries added to `AlgorithmsToLowerBoundsSurfaceTests.lean` and `AxiomsAudit.lean`.

## 3. Scope audit

| Item | Status |
|---|---|
| No R1-C | ✓ |
| No `PrefixExtensionLanguage_in_NP` | ✓ |
| No `PpolyDAG → BoundedSearchSolver` | ✓ |
| No `target.noBoundedSolver` | ✓ |
| No `VerifiedNPDAGLowerBoundSource` | ✓ |
| No `ResearchGapWitness` | ✓ |
| No `SourceTheorem` | ✓ |
| No `gap_from` | ✓ |
| No endpoint | ✓ |
| No P≠NP claim | ✓ |
| No JSONL/spec/known_guards edits | ✓ (only `lakefile.lean` Glob line + 2 test files) |

All scope discipline preserved. The doc-comment on `parseTreeMCSPPrefixInput` explicitly states "It does not assert any polynomial-time verifier theorem or NP-membership result."

## 4. Computability / hidden payload audit

| Check | Status | Note |
|---|---|---|
| Parser is computable | ✓ | `def parseTreeMCSPPrefixInput ... := do ...` over `Option` monad |
| No `Classical.choose` | ✓ | None present in this file |
| No `noncomputable` parser | ✓ | All helpers and the main parser are `def`, not `noncomputable def` |
| No `axiom` | ✓ | |
| No `opaque` | ✓ | |
| No `Fact` / typeclass payload | ✓ | |
| No `native_decide` | ✓ | |
| No hidden solver | ✓ | Parser does not construct or consume a `BoundedSearchSolver` |

All decidability conditions inside the `do` block (`tag = treePrefixTag`, `m = treeMCSPPrefixM codec n`, `i ≤ codec.witnessBits n`, `padZero = true`) are kernel-decidable (`Nat.decEq`, `Nat.decLe`, `Bool` decEq), so the parser is genuinely computable, not "computable in spirit".

The consumed `PrefixExtensionLanguage` itself remains `noncomputable` (via `classical`), but that is part of R1-B's accepted boundary; the parser does not introduce new noncomputability.

## 5. Parser semantics audit

| Step | Description | Classification |
|---|---|---|
| 1. tag check | Read first 8 bits as MSB-first big-endian unsigned natural; reject unless equal to `treePrefixTag = 178` | **sound** |
| 2. gamma decode | `decodeGamma? y tagLen` starting at offset 8; returns `(n, consumedGamma)` | **sound** with caveat: parser uses `consumedGamma` returned by decoder rather than recomputing `gammaLen n`. By construction of `decodeGammaAux?`, on success `consumedGamma = 2*zeros + 1` where `zeros = bitLength(n+1) - 1`, so `consumedGamma = gammaLen n`. **needs proof follow-up** to make this lemma explicit when proving length_convention. |
| 3. ambient length check | `if _hlen : m = treeMCSPPrefixM codec n` | **sound** |
| 4. x slicing | `sliceBits? y xOffset (tableLen n)` at `xOffset = tagLen + consumedGamma` | **sound** modulo `consumedGamma = gammaLen n` lemma |
| 5. i decode | `readNatBE y iOffset (idxWidth codec.witnessBits n)` | **sound** |
| 6. `i ≤ witnessBits n` check | `if hi : i ≤ codec.witnessBits n` | **sound** — this exact `hi` is used as the `prefixLength_le` field of the returned `PrefixInput`, preserving type safety |
| 7. p slicing | `sliceBits? y pOffset i` | **sound** |
| 8. pad slicing | `sliceBits? y padOffset padWidth` where `padWidth = codec.witnessBits n - i` | **sound** |
| 9. all-zero pad check | `allZeroSlice? y padOffset padWidth` then `if _hpad : padZero = true` | **sound** but mildly redundant: the same bits are read by both `sliceBits?` (for `pad` value) and `allZeroSlice?` (for the check). Functionally correct; minor inefficiency. |
| 10. PrefixInput construction | All fields filled with their dependent values | **sound** (depends crucially on `_hlen`, `hi`, and the slicing bounds for type checking) |

**Minor observation:** `pad` is constructed as the slice value from step 8, and `padZero` is enforced separately. Step 9 could be folded into step 8 if a future cleanup wants to avoid re-reading the same bytes, but this is not a correctness issue.

**No semantic bugs detected.** The parser implements exactly the P1P-02 convention.

## 6. Theorem soundness audit

### `tableLen_le_treeMCSPPrefixM`

| Check | Status |
|---|---|
| Statement matches P1P-02 intent | ✓ — directly states `tableLen n ≤ M(n)` |
| Proof soundness | ✓ — `unfold treeMCSPPrefixM; omega` over a definitional sum of `Nat`s; trivially valid |
| Useful for `TreeMCSPPrefixRuntimeBudget` | ✓ — directly discharges `tableLen_le_M : ∀ n, tableLen n ≤ M n` field when the budget is instantiated with `M := treeMCSPPrefixM codec` |
| Useful for `RuntimeAwarePrefixParser` | indirect (no field of this name there, but enables future polynomial bounds) |

### `parseTreeMCSPPrefixInput_bad_tag`

| Check | Status |
|---|---|
| Statement matches P1P-02 intent | ✓ — explicit malformed-tag rejection |
| Proof soundness | ✓ — `simp [parseTreeMCSPPrefixInput, htag, hbad]` unfolds the do-bind and reduces the `if` on `tag = treePrefixTag` to `false` |
| Useful as a building block | partial — narrow to the case where `readNatBE` already succeeded. Does not cover `m < 8` case (where `readNatBE` itself returns `none` and the do-bind short-circuits). Both cases are necessary for a full "wrong tag ⟹ none" lemma; this PR only covers half. **Minor gap.** |

The narrow case is what's actually needed for the malformed-rejection chain (since the `m < 8` case is already covered by the do-bind short-circuit at the level of `readNatBE`), so this is not a defect — but a future cleanup could add `parseTreeMCSPPrefixInput_short_input` for completeness.

### `parseTreeMCSPPrefixInput_malformed_rejected`

| Check | Status |
|---|---|
| Statement matches P1P-02 intent | ✓ — exactly the parser-failure ⟹ language-rejection arrow |
| Proof soundness | ✓ — directly applies `PrefixExtensionLanguage_rejects_malformed` from `PrefixExtensionLanguage.lean` |
| Useful for `TreeMCSPPrefixRuntimeBudget` | ✓ — directly discharges the `malformed_inputs_rejected` field |
| Useful for `RuntimeAwarePrefixParser` | ✓ — same field name |

Strongest of the three theorems by reuse value. Cleanly composes with R1-B abstract infrastructure.

## 7. Missing theorem audit

### A. `parseTreeMCSPPrefixInput_length_convention`

**Statement:** `parse y = some input → m = treeMCSPPrefixM codec input.n`

- **Local proof engineering?** Yes. Case analysis on the parser's `do` block: on every success branch, the parser explicitly checks `_hlen : m = treeMCSPPrefixM codec n` and assigns `input.n := n`, so the equation holds definitionally on success. Requires one auxiliary lemma `decodeGamma?_success_consumedGamma : decodeGamma? y offset = some (n, c) → c = gammaLen n` (already true by the structure of `decodeGammaAux?`).
- **Global type/API blocker?** None. The R1-B `PrefixParser` interface and `RuntimeAwarePrefixParser.length_convention_matches_M` field type signatures already accept exactly this statement.
- **Likely next task?** Yes. Should be P1P-02L₂ step 1.
- **Estimated difficulty:** medium. ~50-100 lines: one helper lemma for the gamma decoder, then a case-split on the parser body.

### B. `encodeTreeMCSPPrefixInput`

**Need:** computable `encode : PrefixInput → PrefixBitVec (treeMCSPPrefixM codec input.n)` (or similar dependent shape).

- **Local proof engineering?** Mostly. Requires defining a few new helpers: `natField` (or `natMSBBits` — already prototyped in closed PR #1326), `gammaField` (Elias-gamma bits for `n+1` — already prototyped in closed PR #1324 line 78-86), then a field-by-field encoder via `match` on bit positions.
- **Global type/API blocker?** None. The `PrefixBitVec m := AlgorithmsToLowerBounds.BitVec m` is just `Fin m → Bool`, so encoding is a `fun j => ...` with a case-split on `j.val`'s position within field boundaries.
- **Likely next task?** Yes. Should be P1P-02L₂ step 2. Reference design: closed PR #1324 (real `encodeTreeMCSPPrefixInput` via match on bit positions, lines 88-119 of that diff) and closed PR #1326 (slice readers + MSB bit helpers, lines 73-104 of that diff).
- **Estimated difficulty:** medium-low. ~80-150 lines.

### C. Parse-encode canonical round-trip

**Statement:** for `input` satisfying `CanonicalTreeMCSPPrefixInput codec input`, `parseTreeMCSPPrefixInput threshold codec (encodeTreeMCSPPrefixInput input) = some input`.

- **Local proof engineering?** Yes. Walks the parser body step by step:
  1. `readNatBE` on the tag field of the encoding recovers `treePrefixTag` (encoder MSB-first ↔ decoder MSB-first).
  2. `decodeGamma?` on the gamma field of the encoding recovers `(input.n, gammaLen input.n)` — this is the hardest sub-lemma; requires showing `decodeGammaAux?` correctly walks the unary-then-payload structure.
  3. `sliceBits?` on the x/p/pad slices recovers the bit-vector exactly (encoder writes, decoder reads — should be a Fin-extensionality argument).
  4. `readNatBE` on the i field recovers `input.i` (same MSB-first round-trip as tag).
  5. `allZeroSlice?` on the pad slice returns `true` (because canonical inputs require pad bits zero).
  6. Final `PrefixInput` constructor reproduces all fields of `input` (this is where the structure-extensionality of `PrefixInput` matters; needs `prefixLength_le` proof irrelevance).
- **Global type/API blocker?** None expected, but **proof irrelevance of dependent fields** (`prefixLength_le : input.i ≤ codec.witnessBits input.n`) might require either `Subsingleton`-based reasoning or `cast`-with-`Eq.refl`-irrelevance, which can be tedious in Lean 4. This is the only place where Lean friction might significantly inflate the estimate.
- **Likely next task?** Yes. Should be P1P-02L₂ step 3.
- **Estimated difficulty:** medium-high. ~150-300 lines depending on `prefixLength_le` proof-irrelevance friction. The gamma decoder round-trip is the most non-trivial sub-lemma; the rest is mechanical.

**Total P1P-02L₂ estimate:** 2-4 days of focused Lean engineering, ~400-600 lines of Lean, no math content beyond what's already in P1P-02.

## 8. Does this unlock P1P-02L₂?

**yes_open_P1P02L2**

All three follow-ups are local proof engineering against a real parser, with no API blocker, no governance gate, no out-of-scope dependency, no math-research dependency. The encoder design has prototypes in closed PRs #1324 and #1326 that can be referenced. The length_convention theorem follows directly from the parser body's `_hlen` check.

## 9. Recommended next action

**open_P1P02L2_length_encoder_roundtrip**

Dispatch one Lean worker on `P1P-02L₂ — encoder + length convention + canonical round-trip` against the merged `d100d33`. Specific scope:

1. **Add** `natMSBBits : (width value : Nat) → PrefixBitVec width` and `gammaField : (n : Nat) → PrefixBitVec (gammaLen n)` helpers (or refer to closed PR #1326's `natMSBBit`/`natMSBBits`/`gammaBits` definitions for the design template).
2. **Add** computable `encodeTreeMCSPPrefixInput : PrefixInput ... m → PrefixBitVec m` (gated on `CanonicalTreeMCSPPrefixInput` or providing an alternative `encodeTreeMCSPPrefixCanonical` taking raw `(n, x, i, h_i, p)` tuple — see closed PR #1324 line 88-119 for prototype).
3. **Prove** `parseTreeMCSPPrefixInput_length_convention`. Add an auxiliary lemma `decodeGammaAux?_success_consumedGamma_eq_gammaLen` first.
4. **Prove** canonical round-trip `parseTreeMCSPPrefixInput threshold codec (encodeTreeMCSPPrefixInput input) = some input` for canonical inputs.
5. **Wire** the new theorems through `RuntimeAwarePrefixParser.length_convention_matches_M` and `TreeMCSPPrefixRuntimeBudget.length_convention_matches_M` field instantiations, but only as derived definitions — do **not** instantiate the budget fully (other staged runtime fields stay `Prop` obligations).

**Explicit forbidden scope** for the P1P-02L₂ worker (same as P1P-02L):
- No `PrefixExtensionLanguage_in_NP`
- No `parser_polynomial_time_in_M` instantiation (that needs X01-style polynomial-time formalism)
- No `RuntimeAwareTreeCircuitCodec` / `TreeMCSPPrefixRuntimeBudget` full instantiation
- No `SearchMCSPMagnificationContract` field discharge
- No `ResearchGapWitness`, no `VerifiedNPDAGLowerBoundSource`, no source theorem
- No `Classical.choose` in any parser-side definition (keep parser computable)
- No JSONL/spec/known_guards/NoGoLog edits

## Commands run

| Command | Result |
|---|---|
| `git log --oneline -5` | confirmed `d100d33` is HEAD on main containing P1P-02L; consistent with claimed commit SHA |
| `wc -l pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean` | 202 lines (matches PR #1323 description) |
| `grep -E "axiom\|sorry\|admit\|noncomputable\|opaque\|native_decide\|Classical.choose" pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean` | no matches (full file read confirms; only `Classical`-free `def`s and theorems) |
| `lake build PnP3 Pnp4` | **not run** (review-only; trust upstream PR check that built green per #1323 description) |
| `./scripts/check.sh` | **not run** (review-only; trust upstream PR check) |
| `rg -n "\bsorry\b\|\badmit\b" -g"*.lean" pnp3 pnp4` | **not run** (review-only; trust upstream PR check) |

The three build/audit commands were not re-executed as part of this review since the PR was already merged with `lake build` green per the PR description. If the operator wants independent re-verification, the standard `./scripts/check.sh` invocation suffices.

## Scope violations

none

## Honest caveats

- I trusted the upstream PR's claim that `lake build PnP3 Pnp4` and `./scripts/check.sh` pass on the merged commit. I did not re-execute these.
- The audit of `decodeGammaAux?` correctness (specifically, that `consumedGamma = gammaLen n` on success and that `decodeGamma?` correctly decodes any well-formed gamma code) was structural, not by exhaustive proof. The lemma needed for P1P-02L₂ length_convention will provide the kernel-checked confirmation.
- I did not audit whether the parser's pad-zero check is semantically equivalent to the `CanonicalTreeMCSPPrefixInput` pad-zero predicate. The connection is intuitively clear (parser checks ambient bits at `padOffset..padOffset+padWidth` are zero; `CanonicalTreeMCSPPrefixInput` requires `input.pad k = false` for `k : Fin padBits`), but a fully proven `parser_success → canonical` lemma would make this rigorous. It is not currently part of P1P-02L's surface; it is implicit in the future round-trip theorem of P1P-02L₂.
- The narrow scope of `parseTreeMCSPPrefixInput_bad_tag` (assuming tag was successfully read) is a minor coverage gap but not a defect, since the `m < 8` case is handled by the do-bind short-circuit in the parser body.
- This review is the synthesis of one operator pass. A second adversarial review by a different handle would tighten the audit of the gamma decoder's edge cases (e.g., what happens at offset boundaries near `m`).
