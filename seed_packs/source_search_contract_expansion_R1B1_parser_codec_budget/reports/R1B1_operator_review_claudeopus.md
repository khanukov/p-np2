# R1-B1 PrefixExtensionLanguageNP operator review — claudeopus

**Slot:** R1-B1 standalone operator review (post-merge of V2).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `be60884`.
**Commit reviewed:** `48429b0` (`Add R1-B1 prefix verifier budget module`, merged via `be60884` as PR #1281).

**Review subjects:**

* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` (188 LOC) — the landed Lean module.
* `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/README.md` and `WORKER_PROMPT_R1B1.md` — the seed pack authoring scope.
* `lakefile.lean` — single `Glob.one` line added.

This complements (does not replace) the parallel-dispatch comparative review `R1B1_parallel_dispatch_review_claudeopus.md` in the same directory. The comparative review established V2 (`48429b0`) over V1 (`dc68600`). This standalone review audits the merged V2 against the R1-B1 spec independently.

This is **operator-scoped review**. No Lean edits, no JSONL / spec / known_guards edits, no trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims. No R1-C implementation.

---

## 1. Executive verdict

```text
approve_with_caveats
```

R1-B1 lands a **correctly scoped, partially substantive contribution**: it discharges the relation-decidability priority for the codec case as a real Lean theorem, while honestly leaving polynomial-time and serialization obligations as staged `Prop` fields. The verdict is `approve_with_caveats` rather than `approve_R1B1` to register that:

1. The discharged `relation_decidable` is **mathematically correct but not polynomially-time**; NP membership still requires polynomial-time runtime that R1-B1 does not address.
2. Three of five budget fields remain as `Prop` placeholders (no concrete proofs).
3. **`PrefixExtensionLanguage_in_NP` is not claimed, and should not be claimed by R1-C work that builds on this.**

R1-C should **not** open. R1-B2 (polynomial-time / runtime / serialization budget) is the appropriate next step OR an operator decision to step back. See §8, §9, §10.

---

## 2. What landed

| Object | Location | Role |
| --- | --- | --- |
| `treeMCSPPrefixParser` | `PrefixExtensionLanguageNP.lean:19-30` | Parameterized parser constructor. Takes `threshold`, `encoding`, `tag`, `M`, `parse` as explicit arguments and packages them into `PrefixParser (treeMCSPSearchProblem threshold encoding)`. No hardness assumption. |
| `TreeMCSPPrefixParserObligations` | `PrefixExtensionLanguageNP.lean:41-51` | Audit-only structure: `tag`, `M`, `parse`, plus three `Prop` obligation fields (`parser_polynomial_time`, `malformed_inputs_rejected_by_parse`, `length_convention_matches_M`). |
| `TreeMCSPPrefixParserObligations.parser` | `PrefixExtensionLanguageNP.lean:54-59` | Extracts a `PrefixParser` from the obligation package via the parameterized constructor. |
| `treeMCSPSearchRelation_decidable_of_encoding` | `PrefixExtensionLanguageNP.lean:70-82` | Generic conditional lemma: given a Decidable provider `hdec` for `encoding.verifies`, build `Decidable ((treeMCSPSearchProblem threshold encoding).relation n x w)`. Proof: `dsimp [treeMCSPSearchProblem]; exact hdec n x w`. |
| **`TreeCircuitWitnessCodec.verifiesDecidable`** | `PrefixExtensionLanguageNP.lean:92-124` | **The load-bearing theorem.** Constructs `Decidable (codec.verifies n tt w)` for any tree-circuit witness codec. Uses case-split on `codec.decode`, `Fintype.decidableForallFintype` over `Fin n → Bool` for `ComputesTruthTable`, and `Nat ≤ Nat` decidability via `infer_instance`. |
| `treeMCSPSearchRelation_decidable_of_codec` | `PrefixExtensionLanguageNP.lean:127-138` | Specialization: for codec-induced encoding via `TreeMCSPSearchWitnessEncoding.ofCodec`, the search-problem relation is decidable. Proof: `dsimp; exact verifiesDecidable codec n x w`. |
| `TreeMCSPPrefixCoreBudgetProgress` | `PrefixExtensionLanguageNP.lean:148-160` | Five-field progress record: `parser_polynomial_time : Prop`, `relation_decidable : ∀ n x w, Decidable (relation n x w)` (proof-relevant), `relation_polynomial_time : Prop`, `witness_length_polynomial : Prop`, `remaining_runtime_or_codec_blockers : Prop`. |
| `TreeMCSPPrefixCoreBudgetProgress.ofEncodingDecidable` | `PrefixExtensionLanguageNP.lean:166-184` | Constructor that takes per-field obligations and produces the progress record by routing `relation_decidable` through `treeMCSPSearchRelation_decidable_of_encoding`. |

**What is NOT in the file:**

* No `PrefixExtensionLanguage_in_NP` theorem.
* No `BoundedSearchSolver` construction.
* No `SearchMCSPMagnificationContract` instance.
* No `VerifiedNPDAGLowerBoundSource` / `ResearchGapWitness` reference.
* No polynomial-time proof for the codec verification procedure.
* No concrete byte-level serialization of `(tag, n, x, i, p, pad)`.

---

## 3. Scope audit

| Check | Status | Evidence |
| --- | --- | --- |
| No extraction theorem | ✓ | no theorem of shape `PpolyDAG L → BoundedSearchSolver _` |
| No `PpolyDAG L → BoundedSearchSolver` | ✓ | `BoundedSearchSolver` not referenced |
| No `target.noBoundedSolver` | ✓ | `noBoundedSolver` not referenced |
| No `VerifiedNPDAGLowerBoundSource` | ✓ | not constructed; not referenced |
| No `ResearchGapWitness` | ✓ | not referenced |
| No endpoint | ✓ | no `P_subset_PpolyDAG` / `P_ne_NP` |
| No R1-C work | ✓ | no extraction / self-reduction theorem |
| No `SourceTheorem` / `gap_from` | ✓ | neither identifier appears |
| No P ≠ NP claim | ✓ | confirmed by reading all 188 LOC |
| No `SearchMCSPMagnificationContract` field invocation | ✓ | structure type referenced only via `treeMCSPSearchProblem`; no contract instance constructed |
| Trust-root unchanged | ✓ | `pnp3/Complexity/Interfaces.lean` only imported transitively; no edits |

**Scope audit verdict:** clean. R1-B1 operates strictly inside the allowed scope.

---

## 4. Parser audit

### 4.1 `treeMCSPPrefixParser` — parameterized constructor only

**Location:** `PrefixExtensionLanguageNP.lean:19-30`.

```lean
def treeMCSPPrefixParser
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (tag : Nat)
    (M : Nat → Nat)
    (parse : ∀ {m : Nat},
      PrefixBitVec m →
        Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)) :
    PrefixParser (treeMCSPSearchProblem threshold encoding) where
  tag := tag
  M := M
  parse := parse
```

**Audit:**

* The constructor is **purely structural**. It does not produce a concrete `parse` implementation; the worker must supply one.
* No byte-level serialization is committed. `parse` is left abstract.
* The doc-comment is explicit: *"Supplying `parse` is not a hardness assumption; it is only the staged decoding boundary already isolated by `PrefixParser`."*
* The parameterization on `threshold`, `encoding`, `tag`, `M` exposes all auditable inputs.

### 4.2 `TreeMCSPPrefixParserObligations` — honest staging

**Location:** `PrefixExtensionLanguageNP.lean:41-51`.

```lean
structure TreeMCSPPrefixParserObligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat}, ...
  parser_polynomial_time : Prop
  malformed_inputs_rejected_by_parse : Prop
  length_convention_matches_M : Prop
```

**Audit:**

* Three audit fields are **`Prop` placeholders**, not `True` fillers. A worker who instantiates this structure must supply real propositions (which may or may not be provable).
* The doc-comment is explicit: *"The accompanying propositions are obligations to be proved by a future codec/serialization implementation; this module does not inhabit them with `True` or any vacuous placeholder."*
* The three fields cover the seed pack README §A.3 requirements (tag rejection, malformed-input rejection, length convention).

### 4.3 Hidden-hardness check

* Does the parser hide a hardness assumption? **No.** `parse` is a pure decoding function `BitVec → Option`. It cannot encode a lower-bound predicate.
* Does the parser hide a promise? **No.** The seed pack README §A.4 specifies that membership uses the relation directly; `parsePrefixInput` does not branch on hardness.
* Does the parser hide lower-bound information? **No.** A `BitVec → Option` function has no semantic content beyond bit-pattern recognition.

### 4.4 Parser audit verdict

**Parser progress is staged (not discharged), but honestly so.**

R1-B1 provides:
* (a) a parameterized constructor (no hardness, no fake serialization);
* (b) an obligation package with three `Prop` fields representing the missing serialization-correctness facts.

R1-B1 does **not** provide:
* a concrete `parse` implementation;
* proofs of any of `parser_polynomial_time`, `malformed_inputs_rejected_by_parse`, `length_convention_matches_M`.

This is **the correct R1-B1 outcome for the parser side**: the WORKER_PROMPT priority (1) "concrete `PrefixParser` instance" is delivered as a **parameterized constructor + obligation package**, but not as an instance for the canonical target. The follow-up R1-B2 would discharge this.

---

## 5. Relation decidability audit

This is the load-bearing section.

### 5.1 `treeMCSPSearchRelation_decidable_of_encoding` — generic reduction

**Location:** `PrefixExtensionLanguageNP.lean:70-82`.

```lean
def treeMCSPSearchRelation_decidable_of_encoding
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (hdec : ∀ n x w, Decidable (encoding.verifies n x w))
    (n) (x) (w) :
    Decidable ((treeMCSPSearchProblem threshold encoding).relation n x w) := by
  dsimp [treeMCSPSearchProblem]
  exact hdec n x w
```

**Soundness check.** The definition at `SearchMCSPConcreteTargets.lean:114-122` states:

```lean
def treeMCSPSearchProblem (threshold) (encoding) : SearchMCSPCompressionProblem where
  ...
  relation := encoding.verifies
  ...
```

So `(treeMCSPSearchProblem threshold encoding).relation = encoding.verifies` definitionally. `dsimp [treeMCSPSearchProblem]` unfolds this, and `hdec n x w` provides the Decidable instance directly.

**Verdict:** sound. The proof is one `dsimp` + one application. No classical use, no hidden axiom, no fake solver, no smuggled hardness. The generic reduction faithfully unfolds `treeMCSPSearchProblem.relation` to `encoding.verifies`. ✓

### 5.2 `TreeCircuitWitnessCodec.verifiesDecidable` — the actual decidability theorem

**Location:** `PrefixExtensionLanguageNP.lean:92-124`.

```lean
def TreeCircuitWitnessCodec.verifiesDecidable
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    Decidable (codec.verifies n tt w) := by
  unfold TreeCircuitWitnessCodec.verifies
  cases hdecode : codec.decode n w with
  | none => exact isFalse (...)
  | some c => ...
      haveI hcompDecidable : Decidable (ComputesTruthTable treeCircuitClass c tt) := by
        unfold ComputesTruthTable
        exact Fintype.decidableForallFintype
      have targetDecidable : Decidable target := by
        unfold target
        infer_instance
      cases targetDecidable with
      | isTrue htarget => exact isTrue ⟨c, rfl, htarget.1, htarget.2⟩
      | isFalse htarget => exact isFalse (...)
```

**Verifying soundness against the actual `codec.verifies` definition** (`SearchMCSPConcreteTargets.lean:61-70`):

```lean
def TreeCircuitWitnessCodec.verifies (codec) (n) (tt) (w) : Prop :=
  ∃ c : Pnp3.Models.Circuit n,
    codec.decode n w = some c ∧
      Pnp3.Models.Circuit.size c ≤ threshold n ∧
        ComputesTruthTable treeCircuitClass c tt
```

**Step-by-step soundness audit:**

* **Case `codec.decode n w = none`:** if `decode = none`, no `c` satisfies `decode = some c`, so the existential is false. The proof returns `isFalse (by intro h; rcases h with ⟨c, hc, _, _⟩; cases hc)`. The `cases hc` discharges the impossible `none = some c` hypothesis. **Sound.**

* **Case `codec.decode n w = some c`:** the witness `c` is fixed. The existential becomes `∃ c', codec.decode n w = some c' ∧ size c' ≤ threshold n ∧ ComputesTruthTable ...`. Since `decode = some c`, the only candidate `c'` for which `decode = some c'` holds is `c` itself (by `Option.some.injEq`). So the existential reduces to `size c ≤ threshold n ∧ ComputesTruthTable treeCircuitClass c tt`. This is the `target` proposition built in the proof.

  - **Subdecidability 1 (`Circuit.size c ≤ threshold n`):** this is `Nat ≤ Nat`, decidable by `instDecidableLeNat`.
  - **Subdecidability 2 (`ComputesTruthTable treeCircuitClass c tt`):** the proof unfolds `ComputesTruthTable` and applies `Fintype.decidableForallFintype`. This is sound provided `ComputesTruthTable treeCircuitClass c tt` is a finite universal quantifier `∀ x : Fin n → Bool, eval c x = tt x` over a `Fintype` domain. The `Fin n → Bool` domain is `Fintype` (`Pi.fintype` for `Bool` Fintype range over `Fin n` Fintype index). The body `eval c x = tt x` is `Decidable Eq Bool`. So `Fintype.decidableForallFintype` is applicable. **Sound.**
  - **And-combination:** the conjunction is decidable via `instDecidableAnd`, resolved by `infer_instance`. **Sound.**
  - **Reassembly:** `isTrue` case produces `⟨c, rfl, htarget.1, htarget.2⟩` — explicit witness for the existential, using `rfl : decode n w = some c` from the case-split. `isFalse` case shows that any alleged witness `c'` must be `c` (by `cases hc'` on `decode = some c'` against the known `decode = some c`), then applies `htarget` to derive contradiction. **Sound.**

**Verdict:** `TreeCircuitWitnessCodec.verifiesDecidable` is a **mathematically correct, kernel-checked Decidable instance** for the codec verification relation. The proof is a clean three-case decomposition (decode none / decode some + size / decode some + computes) using standard Mathlib decidability instances and finite-domain decidable quantification. ✓

### 5.3 `treeMCSPSearchRelation_decidable_of_codec` — specialization

**Location:** `PrefixExtensionLanguageNP.lean:127-138`.

```lean
def treeMCSPSearchRelation_decidable_of_codec
    (codec : TreeCircuitWitnessCodec threshold)
    (n) (x) (w) :
    Decidable ((treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec)).relation n x w) := by
  dsimp [treeMCSPSearchProblem, TreeMCSPSearchWitnessEncoding.ofCodec]
  exact TreeCircuitWitnessCodec.verifiesDecidable codec n x w
```

**Soundness check:** `TreeMCSPSearchWitnessEncoding.ofCodec` (`SearchMCSPConcreteTargets.lean:98-105`) sets `verifies := codec.verifies`. After `dsimp` unfolds both `treeMCSPSearchProblem` and `ofCodec`, the goal becomes `Decidable (codec.verifies n x w)`, which is exactly `verifiesDecidable`. **Sound.** ✓

### 5.4 Decidability vs polynomial-time

**Critical caveat.** The constructed `Decidable` instance is **mathematically correct** but **not polynomial-time**:

* `Fintype.decidableForallFintype` over `Fin n → Bool` enumerates all `2^n` Boolean inputs in the worst case.
* The runtime of the decision procedure is therefore at least `O(2^n · poly(circuit_size))`.
* For NP membership, we need a verifier that runs in `poly(M(n))` time. The current Decidable instance is **exponentially too slow** for NP membership in the standard sense.

R1-B1's `TreeMCSPPrefixCoreBudgetProgress` correctly separates `relation_decidable` (proof-relevant, discharged) from `relation_polynomial_time : Prop` (staged). The doc-comment is explicit: *"This is still not a polynomial-time theorem: it is only a decidability result. The runtime and serialization budgets remain separate R1-B1 obligations."*

**This caveat is the central caveat of R1-B1.** The discharged `relation_decidable` is necessary but not sufficient for NP membership.

### 5.5 Classical / axiom check

* **`Classical.choose`?** None. `rg "Classical\." pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` returns no results.
* **`axiom` declaration?** None. No new axioms introduced.
* **Hidden endpoint?** None. The decidability proof routes through standard Mathlib instances only.
* **Fake solver?** None. The case-split on `codec.decode n w` is the codec's actual `Option`-valued decoding function; no oracle or assumed solver is introduced.

### 5.6 Relation decidability audit verdict

**Section §5 verdict: sound and substantive.**

* The generic reduction `treeMCSPSearchRelation_decidable_of_encoding` correctly unfolds `treeMCSPSearchProblem.relation` to `encoding.verifies` via `dsimp`.
* `TreeCircuitWitnessCodec.verifiesDecidable` is a **real Decidable instance** with a clean proof: case-split on decoding, finite-domain decidable quantification for truth-table agreement, `Nat ≤ Nat` decidability for size, and `And.decidable` via `infer_instance`.
* `treeMCSPSearchRelation_decidable_of_codec` correctly specializes the generic reduction to the codec case.
* **This is decidability only, not polynomial-time.**
* No `Classical.choose`, no axiom, no hidden endpoint, no fake solver.

This is the **first substantive Lean theorem-class result** of R1-B1 — it discharges the `relation_decidable` priority for the canonical codec pathway.

---

## 6. Budget-field audit

`TreeMCSPPrefixCoreBudgetProgress` (`PrefixExtensionLanguageNP.lean:148-160`) has five fields:

| Field | Type | Status | Notes |
| --- | --- | --- | --- |
| `parser_polynomial_time` | `Prop` | **staged** | placeholder `Prop`; no concrete proof in this module; future R1-B2 needs to discharge against a concrete `parse` implementation |
| `relation_decidable` | `∀ n x w, Decidable (relation n x w)` | **partially discharged** | proof-relevant field; constructor `ofEncodingDecidable` builds it from `treeMCSPSearchRelation_decidable_of_encoding`, which routes through a Decidable provider; for codec case, `treeMCSPSearchRelation_decidable_of_codec` provides the full instance directly; **discharged for codec case** |
| `relation_polynomial_time` | `Prop` | **staged** | placeholder `Prop`; the codec-case `Decidable` constructed in §5.2 is correct but runs in `Ω(2^n)`; polynomial-time runtime is genuinely missing |
| `witness_length_polynomial` | `Prop` | **staged** | placeholder `Prop`; no concrete polynomial bound on `witnessBits n` proven |
| `remaining_runtime_or_codec_blockers` | `Prop` | **staged** | catch-all placeholder for residual obligations |

**Field discharge summary:**

```text
parser_polynomial_time:               staged
relation_decidable:                   partially discharged (codec case)
relation_polynomial_time:             staged
witness_length_polynomial:            staged
remaining_runtime_or_codec_blockers:  staged
```

**One real discharge (codec case `relation_decidable`); four staged.**

This matches my R1-B operator review §10 expected outcome: *"partial landing of priorities (1)+(2)+partial (3), with the codec_* and runtime fields staying staged"*. R1-B1 delivers exactly this profile.

---

## 7. Does R1-B1 give `PrefixExtensionLanguage_in_NP`?

```text
NO
```

**Reasoning:**

NP membership for `PrefixExtensionLanguage parser` requires:

1. **A polynomial-time verifier** `V(y, w) : Bool` such that `y ∈ L ↔ ∃ w (|w| ≤ poly(|y|)), V(y, w) = true`.
2. **`Decidable` instance for the relation** so the verifier can compute its answer.
3. **Polynomial-time runtime** for the verifier (parsing + prefix agreement check + relation check).
4. **Polynomial witness-length bound** so the existential is over a polynomially-sized witness set.

R1-B1 discharges (2) only, and only for the codec case. R1-B1 does **not** discharge (1), (3), or (4). All three remain as `Prop` placeholders in `TreeMCSPPrefixCoreBudgetProgress`.

**Exact missing items to produce `PrefixExtensionLanguage_in_NP`:**

| Missing item | Located in budget |
| --- | --- |
| Polynomial-time parser implementation | `parser_polynomial_time` (still `Prop`) + no concrete `parse` instance |
| Polynomial-time relation decision procedure | `relation_polynomial_time` (still `Prop`); current Decidable runs in `Ω(2^n)` |
| Polynomial witness-length bound | `witness_length_polynomial` (still `Prop`) |
| (Implicit) Polynomial-time prefix-agreement check | not explicitly named in `TreeMCSPPrefixCoreBudgetProgress` but covered by `parser_polynomial_time` and `prefix_agreement_polynomial_time` in the upstream `PrefixExtensionNPVerifierBudget` |
| (Implicit) Polynomial-time NP-formalism for pnp4 | the repository does not yet have a general polynomial-time predicate or running-time machinery applicable to the verifier |

**The polynomial-time formalism is the architectural gap.** Without it, no theorem of the form `NP (PrefixExtensionLanguage parser)` can be proven in pnp4 — there is no notion of "NP" in pnp4 that would accept the verifier the budget describes. (`Pnp3.ComplexityInterfaces.NP L` exists, but its formalization details would need to align with whatever polynomial-time machinery pnp4 introduces.)

---

## 8. Does this unlock R1-C?

```text
no_R1B2_runtime_budget_needed
```

R1-B1's decidability discharge is genuine forward progress but **not sufficient** to unlock R1-C. R1-C is the self-reduction theorem `PpolyDAG L → BoundedSearchSolver target`, and to chain into `VerifiedNPDAGLowerBoundSource`, we need `NP L` as a **real Lean theorem**, not a staged budget.

**Why opening R1-C now would inherit the fp3b8 wrapper pattern:**

* fp3b8 D0 RED-light identified the failure mode: `TreeMCSPSearchMagnificationSource` contains the `SearchMCSPMagnificationContract` as an unexpanded field. Treating the package as a source theorem moves the missing theorem into a field.
* The analogous failure here: if R1-C proves a self-reduction theorem with `NP L` as a **staged budget hypothesis**, then any downstream `VerifiedNPDAGLowerBoundSource` would carry the unexpanded NP budget as a field.
* **R1-B1 partially mitigates this:** the relation-decidability field is now a real Lean theorem for the codec case. But the polynomial-time fields are still staged. Until they are discharged, R1-C cannot honestly produce `VerifiedNPDAGLowerBoundSource`.

**Conclusion:** R1-B2 (polynomial-time / runtime / serialization budget) is required before R1-C.

---

## 9. Recommended next action

```text
open_R1B2_runtime_serialization_budget
```

Pessimistic frame caveat: this recommendation is **conditional on the operator deciding to continue the contract_expansion track**. The honest alternative (which I flagged in the R1-B1 comparative review §7) is **Option C — stop / step back**.

If continuing:

```text
open_R1B2_runtime_serialization_budget
```

**Alternative:** `operator_decision_needed`. The operator may legitimately decide to:

* (a) **stop** the contract_expansion track at R1-B1, accepting that R1-A + R1-B + R1-B1 land interface infrastructure and that further progress requires a repo-level decision on a polynomial-time formalism;
* (b) **scope a polynomial-time formalism** for pnp4 as a separate larger task (2–4 weeks), independent of R1-B2-cadence dispatches;
* (c) **continue with R1-B2** as described below.

My honest recommendation, if forced to pick one of the menu options: `open_R1B2_runtime_serialization_budget`, **with explicit dual-outcome scope** — the worker may either land the runtime budget or produce a structured failure documenting the polynomial-time formalism gap. Either outcome is informative.

**Not recommended:**

* `open_R1C_shared_DAG_extraction` — premature; would inherit fp3b8 wrapper pattern.
* `repair_R1B1` — R1-B1 is sound and well-scoped. The two caveats (decidability is not polynomial-time; four fields still staged) are intentional staging, not defects.
* `red_light_contract_expansion` — R1-B1 delivers genuine partial progress. Red-lighting at this point would prematurely close a track that has actually moved forward.

---

## 10. If R1-B2 is recommended — proposed seed pack

```text
seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/
```

**Proposed R1-B2 scope (operator suggestion, not in this review's authority to dispatch):**

### 10.1 Authorized deliverables

1. **Concrete parser serialization** for the `(tag, n, x, i, p, pad)` tuple. Specific suggestion: define `parseTreeMCSPPrefix : PrefixBitVec m → Option (PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)` with a fixed bit-layout convention.
2. **`parser_polynomial_time`** as a real Lean theorem, against whatever polynomial-time predicate pnp4 introduces (this may require introducing a minimal polynomial-time predicate first).
3. **`relation_polynomial_time`** as a real Lean theorem. **Critical caveat:** the current `Decidable` runs in `Ω(2^n)`. A polynomial-time version requires either (a) a different decidability strategy that does not enumerate `2^n` Boolean inputs, OR (b) an explicit acknowledgment that the tree-MCSP relation, as currently formulated, does not admit a polynomial-time verifier without further restricting the truth-table representation.
4. **`witness_length_polynomial`** as a real Lean theorem. Since `witnessBits = codec.witnessBits` and `codec : TreeCircuitWitnessCodec`, the bound depends on the codec's encoding choice. A reasonable codec would have `witnessBits n = poly(2^n)` (since tree circuits over `n` variables can have up to `2^n` distinct functions and would need at most poly-many bits to encode), but precise polynomial bounds depend on the codec implementation.
5. **Optionally, a partial `PrefixExtensionNPVerifierBudget` instance** assembled from (2), (3), (4), the codec-case `relation_decidable` from R1-B1, and staged remaining fields.

### 10.2 Forbidden in R1-B2

* No R1-C work, no extraction theorem.
* No `PpolyDAG → BoundedSearchSolver` implication.
* No `noBoundedSolver` reference.
* No `VerifiedNPDAGLowerBoundSource` / `ResearchGapWitness` construction.
* No endpoint / P ≠ NP claim.
* No edits to trust-root files.
* No `Classical.choose` for the runtime bounds (must be real polynomial-time proofs, not classical extractions).

### 10.3 Acceptance criteria

* **Outcome A:** real Lean theorems for (1) + (2). Partial discharge of (3), (4), or (5) is acceptable. **Structured failure required** for any field that cannot be discharged within scope.
* **Outcome B (structured failure):** worker explicitly identifies the polynomial-time formalism gap (no minimal polynomial-time predicate in pnp4; `Fintype.decidableForallFintype` runs in `2^n`; etc.) and proposes either (i) a specific polynomial-time predicate definition for follow-up, or (ii) a justified RED-light recommendation for the contract_expansion track.

### 10.4 Pessimistic prior on R1-B2 outcomes

| Outcome | Prior |
| --- | --- |
| Partial landing of (1) + structured failure on (2)/(3): worker implements a concrete parser but cannot prove polynomial-time without a pnp4 polynomial-time framework | **~45%** |
| Structured failure entirely: worker identifies the polynomial-time formalism gap at the start and produces an Outcome B report | **~30%** |
| Partial landing of (1) + (2) using a hand-rolled minimal polynomial-time predicate | **~15%** |
| Clean landing of (1) + (2) + (3) + (4) + partial (5) | **~5%** |
| Scope creep into R1-C | **~5%** |

**Most likely outcome:** structured failure with explicit identification of the polynomial-time formalism gap. **This is informative**, not a setback: it surfaces the next architectural decision (whether to invest in a pnp4 polynomial-time formalism, or accept that the contract_expansion track stops at decidability-level results).

---

## 11. Output summary

```
Task: R1-B1 operator review
Handle: claudeopus
Branch: main
Commit reviewed: 48429b0 (merged via be60884 as PR #1281)
Review file: seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/reports/R1B1_operator_review_claudeopus.md
Verdict: approve_with_caveats
  Caveats:
    1. Discharged relation_decidable is mathematically correct but NOT polynomial-time (current Decidable runs in Ω(2^n) for Fintype.decidableForallFintype over Fin n → Bool).
    2. Four of five budget fields remain as Prop placeholders.
    3. No PrefixExtensionLanguage_in_NP theorem; should not be claimed by future R1-C work that builds on this.
Scope audit: clean (no extraction theorem, no PpolyDAG→BoundedSearchSolver, no noBoundedSolver, no VerifiedNPDAGLowerBoundSource, no ResearchGapWitness, no endpoint, no R1-C work, no SourceTheorem/gap_from, no P≠NP)
Parser audit: parameterized constructor + obligation package only; no fake serialization; no hidden hardness/promise/lower-bound info. Parser progress is staged but honest.
Relation decidability audit: SOUND and SUBSTANTIVE.
  - treeMCSPSearchRelation_decidable_of_encoding: dsimp + hdec, clean
  - TreeCircuitWitnessCodec.verifiesDecidable: real Decidable via case-split on codec.decode + Fintype.decidableForallFintype over Fin n→Bool + Nat≤Nat decidability + And.decidable
  - treeMCSPSearchRelation_decidable_of_codec: specialization, clean
  - No Classical.choose, no axiom, no hidden endpoint, no fake solver
  - This is decidability only, not polynomial-time
Budget fields discharged:
  parser_polynomial_time: staged
  relation_decidable: partially discharged (codec case real Lean theorem; generic case conditional on Decidable provider)
  relation_polynomial_time: staged
  witness_length_polynomial: staged
  remaining_runtime_or_codec_blockers: staged
PrefixExtensionLanguage_in_NP? NO
  Missing: polynomial-time parser, polynomial-time relation decision, polynomial witness-length bound, and (architectural) polynomial-time formalism for pnp4
R1-C unlocked? NO — R1-B2 runtime/serialization budget needed first; current decidability is exponentially too slow for NP verifier
Recommended next action: open_R1B2_runtime_serialization_budget
  Proposed seed pack: seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/
  Scope: concrete parser, parser_polynomial_time, relation_polynomial_time, witness_length_polynomial, optional partial PrefixExtensionNPVerifierBudget instance
  Forbidden: R1-C work, extraction theorem, endpoint
  Acceptance: structured failure on polynomial-time formalism gap is acceptable and informative
  Pessimistic prior: ~30% structured failure (most likely), ~45% partial landing of parser without polynomial-time, ~20% material discharge, ~5% scope creep
  Honest alternative: operator may legitimately choose 'stop / step back' instead, accepting that R1-A + R1-B + R1-B1 land interface infrastructure and that further progress requires a repo-level polynomial-time formalism decision
Commands run:
  - git fetch / sync to main → be60884
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output
  - Reading: PrefixExtensionLanguageNP.lean (188 LOC), seed pack README, R1-B operator review, SearchMCSPConcreteTargets.lean (codec/verifies/ComputesTruthTable definitions), R1-A review
  - lake build PnP3 Pnp4 → NOT RUN (no Lean toolchain in operator-review env; CI green at upstream merge be60884)
  - ./scripts/check.sh → NOT RUN (same reason)
Scope violations: none
```
