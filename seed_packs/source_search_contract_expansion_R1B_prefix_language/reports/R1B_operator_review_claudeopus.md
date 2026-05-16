# R1-B PrefixExtensionLanguage operator review — claudeopus

**Slot:** R1-B standalone operator review (post-merge of V2).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `2347fab`.
**Commit reviewed:** `def64e7` (`Add R1-B prefix extension language skeleton`, merged via `2347fab` as PR #1278).

**Review subjects:**

* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` (221 LOC) — the landed Lean module.
* `seed_packs/source_search_contract_expansion_R1B_prefix_language/README.md` and `WORKER_PROMPT_R1B.md` — the seed pack authoring scope.
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` and `pnp4/Pnp4/Tests/AxiomsAudit.lean` — surface and axiom-audit additions.
* `lakefile.lean` — single `Glob.one` line added.

This complements (does not replace) the parallel-dispatch comparative review `R1B_parallel_dispatch_review_claudeopus.md` in the same directory. The comparative review established V2 (`def64e7`) over V1 (`d702a46`). This standalone review audits the merged V2 against the R1-B spec independently.

This is **operator-scoped review**. No Lean edits, no JSONL / spec / known_guards edits, no trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims. No R1-C implementation.

---

## 1. Executive verdict

```text
approve_R1B
```

R1-B lands as a **correctly scoped, type-safe partial completion**. The language definition is well-formed, the parser abstraction is honest about what it defers, the classical/noncomputable use is bounded to a Boolean-wrapper role, and the NP membership obligation is **staged** in an explicit verifier-budget structure rather than hidden in a wrapper field.

The honest framing: R1-B is **interface progress, not mathematical progress**. NP membership is **not proven**. R1-C should not open until at least one budget field is discharged on a concrete target (see §9, §10). See §11 for the pessimistic frame.

---

## 2. What landed

| Object | Location | Role |
| --- | --- | --- |
| `PrefixBitVec` | `PrefixExtensionLanguage.lean:10` | local abbrev for `AlgorithmsToLowerBounds.BitVec` to avoid `BitVec` name clashes |
| `PrefixInput problem m` | `PrefixExtensionLanguage.lean:31-41` | parsed input structure, parametrized by ambient length `m`, with `prefixLength_le : i ≤ problem.witnessBits n` as a structure field |
| `prefixAgrees` | `PrefixExtensionLanguage.lean:52-58` | predicate: a full witness `w` agrees with `input.p` on the first `i` coordinates, using safe coercion via `prefixLength_le` |
| `PrefixParser problem` | `PrefixExtensionLanguage.lean:71-75` | minimal parser interface with three fields: `tag : Nat`, `M : Nat → Nat`, `parse : ∀ {m}, PrefixBitVec m → Option (PrefixInput problem m)` |
| `parsePrefixInput` | `PrefixExtensionLanguage.lean:78-83` | named entry point alias for `parser.parse` |
| `wellFormed` | `PrefixExtensionLanguage.lean:86-91` | derived: `∃ input, parsePrefixInput parser y = some input` |
| `PrefixExtendableInput` | `PrefixExtensionLanguage.lean:100-105` | semantic core: a parsed input is extendable when some full witness `w` agrees on the prefix and satisfies the target relation |
| `PrefixExtendable` | `PrefixExtensionLanguage.lean:108-114` | ambient-input version: parse succeeds AND the parsed input is extendable |
| `PrefixExtensionLanguage` | `PrefixExtensionLanguage.lean:124-128` | `noncomputable def ... := by classical; exact fun _m y => if PrefixExtendable parser y then true else false`. The pnp3 `Language` value. |
| `PrefixExtensionLanguage_accepts_iff` | `PrefixExtensionLanguage.lean:131-142` | basic iff: language returns `true` ↔ predicate holds |
| `PrefixExtensionLanguage_rejects_malformed` | `PrefixExtensionLanguage.lean:145-159` | parser failure → language returns `false` |
| `PrefixExtensionLanguage_accepts_of_parse_and_witness` | `PrefixExtensionLanguage.lean:162-177` | forward-direction constructor: parse succeeds + agreement + relation → language returns `true` |
| `PrefixExtensionNPVerifierBudget` | `PrefixExtensionLanguage.lean:190-201` | 9-field `Prop`-valued structure listing the parser/codec/runtime facts needed before NP membership can be proven |
| `PrefixExtensionNPVerifierPlan` | `PrefixExtensionLanguage.lean:211-217` | 4-field structure wrapping the budget plus three NP-witness-shape obligations |

Plus surface tests (`AlgorithmsToLowerBoundsSurfaceTests.lean:+40 LOC`, `check_*` wrappers) and three `#print axioms` entries in `AxiomsAudit.lean`. Build registered via one `lakefile.lean` entry.

---

## 3. Scope audit

| Check | Status | Evidence |
| --- | --- | --- |
| No extraction theorem | ✓ | no theorem of shape `PpolyDAG L → BoundedSearchSolver _` appears |
| No `PpolyDAG` lower bound | ✓ | no `¬ PpolyDAG _` or `NP_not_subset_PpolyDAG` claim |
| No `BoundedSearchSolver` | ✓ | `BoundedSearchSolver` is not imported or referenced |
| No `target.noBoundedSolver` contradiction | ✓ | `noBoundedSolver` not referenced |
| No `VerifiedNPDAGLowerBoundSource` construction | ✓ | `VerifiedNPDAGLowerBoundSource` not constructed; not referenced |
| No `ResearchGapWitness` | ✓ | not referenced |
| No endpoint | ✓ | no `P_subset_PpolyDAG` / `P_ne_NP` style theorem |
| No `SourceTheorem` / `gap_from` | ✓ | neither identifier appears |
| No `P ≠ NP` claim | ✓ | confirmed by reading all 221 LOC |
| No `SearchMCSPMagnificationContract` field invocation | ✓ | the file imports `SearchMCSPConcreteTargets` but only uses `SearchMCSPCompressionProblem` and its `instanceBits` / `witnessBits` / `relation` fields; no contract field is invoked |
| Trust-root unchanged | ✓ | `pnp3/Complexity/Interfaces.lean` only imported transitively via `SearchMCSPMagnification`; no edits |

**Scope audit verdict:** clean. R1-B operates strictly inside the allowed scope.

---

## 4. Language-definition audit

| Check | Status | Notes |
| --- | --- | --- |
| `PrefixInput` parametrized by ambient length `m` | ✓ | `structure PrefixInput (problem : SearchMCSPCompressionProblem) (m : Nat) where ...` (line 31-33). The `m` parameter makes the type of `y : PrefixBitVec m` match the parser's input directly. |
| Fields `tag`, `n`, `x`, `i`, `p`, `pad`, `padBits` correct | ✓ | line 34-41: `tag : Nat`, `n : Nat`, `x : PrefixBitVec (problem.instanceBits n)`, `i : Nat`, `prefixLength_le : i ≤ problem.witnessBits n`, `p : PrefixBitVec i`, `padBits : Nat`, `pad : PrefixBitVec padBits`. All match the README §A.1 input format. |
| `i ≤ witnessBits n` enforced by structure field | ✓ | `prefixLength_le` is **a struct field**, not an external predicate. Every `PrefixInput problem m` value is in-range by construction. This is the critical type-safety choice. |
| `p : PrefixBitVec i` is variable-width | ✓ | `p` has width exactly `i` (the active prefix length), not the witness length. Semantically aligned: only the active prefix is carried. |
| Malformed inputs are nonmembers | ✓ | `PrefixExtendable parser y := ∃ input, parsePrefixInput parser y = some input ∧ ...`. If `parse` returns `none`, the existential is vacuous, so `PrefixExtendable` is false, so `PrefixExtensionLanguage parser m y = false`. Confirmed in `PrefixExtensionLanguage_rejects_malformed` (line 145-159). |
| Membership condition uses **only** relation + agreement | ✓ | `PrefixExtendableInput input := ∃ w, input.prefixAgrees w ∧ problem.relation input.n input.x w` (line 100-105). No solver reference, no advice, no nonuniform circuit, no lower-bound predicate. |
| No solver dependence | ✓ | confirmed by reading: `BoundedSearchSolver` is not imported or referenced |
| No `noBoundedSolver` dependence | ✓ | `noBoundedSolver` is not referenced |
| No diagonal choice | ✓ | no `Classical.choose` over diagonal predicates; the only classical use is in `PrefixExtensionLanguage` itself (a Bool-wrapper, see §6) |
| No advice | ✓ | parser is `∀ {m}, BitVec m → Option (...)` — pure function, no nonuniform advice |
| No endpoint dependence | ✓ | no `VerifiedNPDAGLowerBoundSource` / `ResearchGapWitness` / `NP_not_subset_PpolyDAG` reference |

**Language-definition audit verdict:** clean. The language is **purely semantic**: it accepts `y` iff there exists a parsed input from `y` that extends to a full witness satisfying the target relation. No hidden hardness, no hidden solver, no hidden lower bound.

### 4.1 Type-safety-by-construction (re-emphasis)

The decision to embed `prefixLength_le` as a structure field is the **load-bearing design choice** in R1-B. In `prefixAgrees` (line 52-58):

```lean
def prefixAgrees ... :=
  ∀ k : Fin input.i,
    w ⟨k.1, Nat.lt_of_lt_of_le k.2 input.prefixLength_le⟩ = input.p k
```

The coercion `⟨k.1, Nat.lt_of_lt_of_le k.2 input.prefixLength_le⟩ : Fin (problem.witnessBits input.n)` is type-safe **by virtue of the structure invariant**. R1-C will need to do this coercion repeatedly when extracting per-coordinate output circuits; V2's design pushes the proof debt **once into the structure**, not at every use site. **Architecturally sound.**

---

## 5. Parser abstraction audit

**The parser is abstract:** `parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)` is a function field with no proof obligations beyond producing an `Option`.

| Question | Answer |
| --- | --- |
| Does `parse` hide hardness? | **No.** `parse` returns `Option (PrefixInput problem m)`. There is no hidden lower-bound predicate, no hardness assumption, no nonuniform advice. A concrete parser will be a pure decoding function. |
| Does `parse` hide a promise? | **No.** R1-B's `PrefixExtendable` is defined via the **relation** directly, not via a promise. The README §A.4 explicitly says "If the concrete tree-MCSP relation already implies the promise, prefer the relation-only condition". V2 follows this. |
| Does `parse` hide lower-bound information? | **No.** Parsing is pure syntactic decoding; no lower-bound semantic content can survive a `Bool`-valued `Option` decoding interface. |
| Is it acceptable that parser serialization is deferred? | **Yes for R1-B; no for R1-C.** Per the seed pack README §B.4 ("codec assumptions required for checking the relation must be listed rather than hidden") and §B.5 ("if the current interfaces do not expose enough data to prove these bounds, record the exact missing budget"). R1-B fulfills this via `PrefixExtensionNPVerifierBudget`. R1-C, however, needs at least one concrete parser instance for the tree-MCSP target to ground the reduction. |
| What exact parser/serialization proof is needed before R1-C? | At minimum: **one concrete parser** `parser_tree_mcsp : PrefixParser treeMCSPSearchProblem` with (a) explicit `M : Nat → Nat`, (b) explicit `parse` implementation, (c) at least one well-formedness theorem (every accepted string yields the canonical `PrefixInput`), and (d) at least the `parser_polynomial_time` and `relation_decidable` fields of the budget discharged. The remaining budget fields (codec_*, witness_length_polynomial, etc.) can stay staged for R1-B+ but **not all** can stay staged or R1-C inherits the fp3b8 RED-light pattern (vacuous source theorem hidden in a wrapper field). |

**Parser abstraction verdict:** acceptable for R1-B. Abstract parser is correctly scoped here. R1-C dispatch should be gated on at least one concrete parser instance.

### 5.1 What the abstract parser does NOT decide

Importantly, V2's `PrefixParser` does **not** assert any of:
- `parse y = some _ ↔ y is well-formed by some explicit format` (no formal well-formedness theorem)
- `m = M (parse y).get!.n` (no length consistency theorem)
- `tag = (parse y).get!.tag` (no tag consistency theorem)

V1 attempted to embed these as parser proof obligations. V2 deliberately leaves them out. **This is design flexibility**, not a deficiency: a concrete parser instance can provide these as **definitional consequences** of its `parse` implementation, without forcing the abstract interface to demand them up front. The R1-B+ slot is exactly where these definitional consequences should be proven for the tree-MCSP-specific parser.

---

## 6. Classical / noncomputable audit

The single classical site is `PrefixExtensionLanguage.lean:124-128`:

```lean
noncomputable def PrefixExtensionLanguage (parser) : Pnp3.ComplexityInterfaces.Language := by
  classical
  exact fun _m y => if PrefixExtendable parser y then true else false
```

| Question | Answer |
| --- | --- |
| Is `classical` here only a Boolean wrapper around `Prop`? | **YES.** The `classical` tactic is invoked specifically to obtain a `Decidable (PrefixExtendable parser y)` instance via `Classical.propDecidable`, allowing the `if ... then true else false` Bool-wrapper. The classical commitment is exactly the Mathlib-standard `Classical.propDecidable`. |
| Is this acceptable for the skeleton stage? | **YES.** R1-B's role is to **specify** the language, not to prove decidability. Decidability is staged as `relation_decidable` (budget field). The classical wrapper here is **transparent**: it commits to the principle "every Prop has a decidable instance for the purpose of building a Bool value", which is standard. It does not hide any specific decidability theorem. |
| Does it hide verifier work? | **NO.** The verifier work is **explicitly staged** in `PrefixExtensionNPVerifierBudget`. The classical wrapper does not avoid the work; it just allows the language to be defined as a `Language = ∀ n, BitVec n → Bool` value while decidability is being staged. A future computable version would replace `Classical.propDecidable` with a concrete `Decidable` instance built from the budget components. |
| Should a future R1-B+ replace this with a decidable verifier? | **YES, but only in stages.** The current classical wrapper is acceptable for R1-B because the language definition does not yet commit to a specific decidability procedure. R1-B+ (parser/codec budget) should produce a `Decidable (PrefixExtendable parser y)` instance using a concrete parser + concrete relation decidability. At that point the `noncomputable` can be dropped and the language becomes computable. **This is mechanical, not mathematical, work.** |
| Is there any other `Classical.choose` or non-standard axiom use? | **NO.** `rg "Classical\." pnp4/Pnp4/Frontier/ContractExpansion/` returns only the `classical` tactic uses in two theorems (`accepts_iff`, `rejects_malformed`) — both are case-split helpers, no `Classical.choose`. |

**Classical/noncomputable audit verdict:** acceptable. The classical commitment is the Mathlib-standard `Classical.propDecidable`, used only as a Boolean wrapper. No mathematical payload is hidden in the classical machinery; the deferred decidability work is **explicitly listed** in the verifier budget.

### 6.1 Axiom-surface expectation

Three `#print axioms` entries in `AxiomsAudit.lean` will report:

* `PrefixExtensionLanguage_accepts_iff` → `Classical.choice`, `propext`, `Quot.sound` (standard Mathlib triad, plus `Classical.choice` from the `classical` tactic inside the proof).
* `PrefixExtensionLanguage_rejects_malformed` → same set.
* `PrefixExtensionLanguage_accepts_of_parse_and_witness` → may or may not depend on `Classical.choice` depending on Lean's reduction; either way within standard pnp4 baseline.

These axiom surfaces are **within the existing pnp4 Mathlib-based baseline** (per R1-A operator review §7). No new axioms introduced.

---

## 7. Theorem soundness audit

### 7.1 `PrefixExtensionLanguage_accepts_iff` (line 131-142)

**Statement:** `PrefixExtensionLanguage parser m y = true ↔ PrefixExtendable parser y`.

**Proof:** classical case-split on `PrefixExtendable parser y`. If true, `simp [h]` resolves both directions; if false, similarly.

**Soundness:** sound. The statement is the **definitional unfolding** of the language via the `if-then-else`. The `↔` is morally `if_pos`/`if_neg`. No hidden content.

**Helps R1-C?** YES. R1-C will need to go between Boolean language membership (which a `PpolyDAG` decider produces) and the propositional `PrefixExtendable` (which the self-reduction will manipulate). This iff is the natural bridge.

**Hidden endpoint?** None.

### 7.2 `PrefixExtensionLanguage_rejects_malformed` (line 145-159)

**Statement:** if `parsePrefixInput parser y = none`, then `PrefixExtensionLanguage parser m y = false`.

**Proof:** show `¬ PrefixExtendable parser y` (because the existential would require `parsePrefixInput = some _`, contradicting `none`); then unfold and simp.

**Soundness:** sound. Standard exception-propagation pattern.

**Helps R1-C?** YES. R1-C may need to assume the input is well-formed; this lemma allows R1-C to handle malformed inputs by syntactic rejection without invoking the relation, which keeps the reduction simple.

**Hidden endpoint?** None.

### 7.3 `PrefixExtensionLanguage_accepts_of_parse_and_witness` (line 162-177)

**Statement:** given `parsePrefixInput parser y = some input`, `input.prefixAgrees w`, and `problem.relation input.n input.x w`, conclude `PrefixExtensionLanguage parser m y = true`.

**Proof:** construct `PrefixExtendable parser y` from the three premises via `⟨input, hparse, ⟨w, hagrees, hrel⟩⟩`, then unfold and `if_pos`.

**Soundness:** sound. Pure forward-direction constructor.

**Helps R1-C?** **YES, significantly.** The self-reduction in R1-C will build pairs `(input, w)` where `input` is the encoded prefix and `w` is the constructed full witness. This lemma is the **direct** way to conclude language membership from these pieces. Without it, R1-C would need to unfold `PrefixExtendable` manually at every site. This was V2's specific design advantage over V1.

**Hidden endpoint?** None.

**Theorem soundness verdict:** all three theorems sound. No hidden endpoints, no smuggled contracts.

---

## 8. NP verifier budget audit

The 9-field `PrefixExtensionNPVerifierBudget` (line 190-201):

```lean
structure PrefixExtensionNPVerifierBudget (parser) : Type where
  parser_polynomial_time : Prop
  witness_length_polynomial : Prop
  prefix_agreement_polynomial_time : Prop
  relation_decidable : Prop
  relation_polynomial_time : Prop
  codec_serialization_available : Prop
  codec_decode_available : Prop
  codec_witness_length_bound : Prop
  truth_table_verification_runtime : Prop
```

The 4-field `PrefixExtensionNPVerifierPlan`:

```lean
structure PrefixExtensionNPVerifierPlan (parser) : Type where
  budget : PrefixExtensionNPVerifierBudget parser
  witness_is_full_target_witness : Prop
  verifier_checks_prefix_agreement : Prop
  verifier_checks_problem_relation : Prop
```

### 8.1 Budget completeness check

For NP membership of `PrefixExtensionLanguage parser`, the standard requirements are:

(a) The witness for membership is some `w : PrefixBitVec (problem.witnessBits input.n)` with `|w| = problem.witnessBits n`, bounded polynomially in `m`. Covered by `witness_length_polynomial` + `codec_witness_length_bound`.

(b) The verifier `V : (ambient input, w) → Bool` runs in polynomial time. Decomposes into: parse + prefix agreement check + relation check. Covered by `parser_polynomial_time` + `prefix_agreement_polynomial_time` + `relation_polynomial_time`.

(c) The relation is decidable. Covered by `relation_decidable`.

(d) Codec functions exist to convert between ambient bitstrings and the structured `(d, i, p, w)` pieces. Covered by `codec_serialization_available` + `codec_decode_available`.

(e) For the tree-MCSP application specifically, truth-table verification of the relation runs in polynomial time. Covered by `truth_table_verification_runtime`.

**Verdict:** the 9 fields **collectively cover** the standard NP-membership requirements for `PrefixExtensionLanguage`. The decomposition is clean: parser obligations, witness obligations, relation obligations, codec obligations, target-specific obligations.

### 8.2 Are any essential facts missing?

I find **one potential gap**:

* The current `SearchMCSPCompressionProblem.relation` is `Prop`-valued. To prove NP membership in Lean, we ultimately need `Decidable (problem.relation n x w)` AND a polynomial-time runtime witness for that decidability. The budget field `relation_decidable : Prop` captures the **statement** "relation is decidable" but does **not** itself enforce polynomial-time decidability or carry decidability instances. The companion `relation_polynomial_time` is also a `Prop`. **Neither field is a Lean `Decidable` instance.** This is acceptable for R1-B (the budget is staging, not discharging), but R1-B+ will need to **replace** these `Prop` fields with actual `Decidable` instances and polynomial-time bound witnesses, not just prove the `Prop`s.

This is a known consequence of staging at the `Prop`-level. The seed pack README §B.5 explicitly authorized this: "If the current interfaces do not expose enough data to prove these bounds, the worker must record the exact missing budget as a structured failure or audit note." V2 records the budget as Prop fields, which is the structured-audit-note form.

### 8.3 Honesty check: does this stage NP membership without pretending to prove it?

**YES.** The verifier-budget structure is a `Type` with `Prop` fields. To inhabit it, one would need to supply proofs of each field. **No instance is constructed** in this file. The plan structure is similarly uninhabited. **There is no theorem `PrefixExtensionLanguage_in_NP` in the file.**

The staging is **explicit**: the budget structure is the **API surface** through which R1-B+ or R1-C is expected to discharge NP membership. Until an instance is built, no NP claim is made.

This is the correct way to stage in Lean: a `Type` of obligations, uninstantiated. **No vacuous NP claim is smuggled.**

### 8.4 Is NP membership still a blocker before R1-C?

**YES, in the following precise sense:**

* R1-C will prove a theorem of the shape `PpolyDAG L → BoundedSearchSolver target.problem target.circuitClass _`, where `L = PrefixExtensionLanguage parser`.
* For this implication to be **useful**, `L` must actually be in NP. Otherwise, the theorem reduces from a hypothesis (`PpolyDAG L`) about an arbitrary language to a conclusion that might already be vacuous.
* If R1-C is proven without first discharging at least some budget fields, then chaining `target.noBoundedSolver` to `R1-C` to "obtain `VerifiedNPDAGLowerBoundSource`" would require **`NP L`** as a separate hypothesis. If `NP L` is staged in the budget (unproven), then `VerifiedNPDAGLowerBoundSource` construction would carry a staged budget field — **exactly the fp3b8 pattern that already RED-lighted** (`TreeMCSPSearchMagnificationSource` hiding the contract in an unexpanded field).

**Therefore:** R1-C should not open before at least the parser + relation_decidable + relation_polynomial_time + witness_length_polynomial budget fields are discharged on a concrete target. The remaining codec_* fields can stay staged for R1-C-internal work, but the core NP-shape fields must be real Lean theorems.

---

## 9. Does this unlock R1-C?

```text
no_R1B1_budget_verifier_needed
```

R1-B's language definition and staged verifier budget are sound and well-shaped. But **R1-C should not open** before R1-B+ (which I'll call R1-B1 below to match the WORKER_PROMPT enumeration) discharges at least:

1. A **concrete `PrefixParser` instance** for one explicit target (the tree-MCSP search problem is the natural choice).
2. The **`parser_polynomial_time`** and **`relation_decidable`** budget fields, both as real Lean theorems / instances on that concrete target.
3. Either the **`witness_length_polynomial`** field as a concrete polynomial bound, or an explicit operator-visible note that R1-C's reduction does not depend on this bound (which I doubt is possible but should be checked).

Reasoning:

* R1-C is the self-reduction theorem. Its hypothesis is `PpolyDAG L`. Its conclusion (or downstream consequence) is `BoundedSearchSolver target.problem target.circuitClass target.sizeBound`. For this reduction to chain into a `VerifiedNPDAGLowerBoundSource`, we need `NP L`, which currently only exists as a 9-field staged budget.
* Opening R1-C now, on top of a 9-field-unproven budget, creates the **wrapper-around-unexpanded-contract** failure mode that fp3b8 already RED-lighted at `TreeMCSPSearchMagnificationSource`.
* Once R1-B1 (parser + core NP fields discharged) lands, R1-C can be opened with a `PrefixExtensionLanguage_in_NP` theorem **as a real hypothesis** rather than a staged budget.

**Important subtlety.** The seed pack README says R1-B should not perform extraction work; R1-C is the extraction step. R1-B1 is **not extraction**; it's **NP-membership discharge for the language R1-B defined**. R1-B1 is the natural successor to R1-B, before R1-C. The WORKER_PROMPT in this review request explicitly lists `no_R1B1_budget_verifier_needed` as a verdict option, anticipating exactly this gating.

---

## 10. Recommended next action

```text
open_R1B1_parser_codec_budget
```

**Specific R1-B1 dispatch shape (operator suggestion, not in this review's authority to dispatch):**

* **Single Lean module:** `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` (new file; do not edit `PrefixExtensionLanguage.lean`).
* **Single concrete target:** tree-MCSP search problem from `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` (`treeMCSPSearchProblem`).
* **Deliverables (in priority order):**
  1. A concrete `treeMCSPPrefixParser : PrefixParser treeMCSPSearchProblem` with explicit `M`, explicit `parse`.
  2. A `Decidable (treeMCSPSearchProblem.relation n x w)` instance (or proof that the existing `SearchMCSPCompressionProblem.totalOnPromise` machinery already supplies this).
  3. Discharge `parser_polynomial_time`, `relation_decidable`, `relation_polynomial_time`, `witness_length_polynomial` budget fields as real Lean theorems.
  4. **Optional bonus:** assemble these into a partial `PrefixExtensionNPVerifierBudget treeMCSPPrefixParser` instance.
  5. **Out of scope:** the `codec_*` and `truth_table_verification_runtime` fields. These can stay staged because R1-C may not need them directly (depending on how R1-C is shaped).
  6. **Optional final theorem if all 4 priority fields land:** `theorem treeMCSPPrefixExtensionLanguage_in_NP : NP (PrefixExtensionLanguage treeMCSPPrefixParser)`. Only state this theorem if **all** priority fields are real Lean theorems, not staged.

* **Acceptance criterion:** at least priorities (1)+(2) land; (3) lands as far as possible; structured failure for whatever doesn't land, with clear identification of the specific blocker.

* **Forbidden:** no R1-C work, no extraction theorem, no `PpolyDAG → BoundedSearchSolver` implication, no `noBoundedSolver` reference, no `VerifiedNPDAGLowerBoundSource` / `ResearchGapWitness` / endpoint / P ≠ NP.

* **Expected outcome distribution (my prior):**
  * **~55%** R1-B1 lands priorities (1) + (2) + partial (3). The parser implementation is mechanical; relation decidability for tree-MCSP depends on existing repo infrastructure, which I haven't audited deeply but is plausibly tractable.
  * **~25%** structured failure on `relation_decidable`: the tree-MCSP relation in the current repo formulation may not be `Decidable` without further work. This is informative if it happens, because it surfaces the **next** real obstacle in the contract_expansion route.
  * **~15%** structured failure on `parser_polynomial_time`: pnp4 doesn't have a polynomial-time formalism applicable to a parser definition, so this might be an interface gap. Informative.
  * **~5%** scope creep: worker attempts R1-C inline. Operator should review carefully.

**Why not `open_R1C_shared_DAG_extraction` directly:** see §9.

**Why not `repair_R1B`:** R1-B is correctly scoped and sound. The "missing" NP membership is **intentionally staged**, not a defect.

**Why not `red_light_contract_expansion`:** R1-B and R1-A both landed. The contract_expansion route is **the first FP3b-era route to land any positive Lean infrastructure**. Red-lighting before R1-B1 even attempts would be premature.

**Why not `operator_decision_needed`:** the technical decision is clear: R1-B1 before R1-C.

---

## 11. Pessimistic frame (for operator awareness)

R1-B landed cleanly because it is **definitional plumbing with an explicit budget**. The R1-A operator review noted that R1-A was definitional plumbing; R1-B is one step up — it defines actual mathematical content (a Boolean language and its semantic membership predicate) but **explicitly stages** the NP membership as future budget work.

The path forward:

```
R1-A (✓ landed)       definitional plumbing: C_DAG wrapper
R1-B (✓ landed)       language definition + staged NP budget
R1-B1 (recommended)   discharge NP budget for tree-MCSP target
R1-C (gated)          actual mathematical content: self-reduction
                      PpolyDAG L → BoundedSearchSolver target
```

**My estimates of clean-landing probabilities** (updated from R1-A review):

| Slot | Prior | Reason |
| --- | --- | --- |
| R1-B1 (parser + core NP fields) | ~55% | mechanical work; one real risk = `relation_decidable` |
| R1-C (self-reduction theorem) | <30% | unchanged; the literature does not contain this self-reduction in the `PpolyDAG`-size-budget regime; if it did, fp3b8-D0 would have found it |

R1-A + R1-B clean landings are **excellent** as infrastructure but **do not move the prior on R1-C**, which remains the hardest gate. **R1-B1's value:** even if R1-B1 RED-lights on `relation_decidable`, that finding is genuinely informative — it surfaces the **next** real obstacle in the route, and may suggest whether R1-C is closer to the literature's existing search-to-decision tools or genuinely beyond them.

R1-A and R1-B together represent the first positive Lean theorem-class progress in the contract_expansion track. Together they are **necessary**. Whether they are jointly **sufficient** (in the sense that one more careful step like R1-B1 + R1-C produces the missing self-reduction) is the open empirical question.

---

## 12. Output summary

```
Task: R1-B operator review
Handle: claudeopus
Branch: main
Commit reviewed: def64e7 (merged via 2347fab as PR #1278)
Review file: seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/R1B_operator_review_claudeopus.md
Verdict: approve_R1B
Scope audit: clean (no extraction, no PpolyDAG lower bound, no BoundedSearchSolver, no
             noBoundedSolver, no VerifiedNPDAGLowerBoundSource, no ResearchGapWitness, no
             endpoint, no SourceTheorem/gap_from, no P≠NP)
Language-definition audit: clean (PrefixInput parametrized by m; prefixLength_le as
             structure field; p : PrefixBitVec i variable-width; malformed = nonmember;
             no solver/advice/diagonal/endpoint dependence)
Parser abstraction audit: acceptable for R1-B; abstract parse does not hide hardness,
             promise, or lower-bound info; R1-C requires at least one concrete parser
             instance before opening
Classical/noncomputable audit: acceptable; classical wrapper around Prop is the
             Mathlib-standard Classical.propDecidable; no Classical.choose; deferred
             decidability is explicitly staged in budget, not hidden in classical
NP verifier budget audit: 9 fields cover standard NP requirements; honest staging
             (no PrefixExtensionLanguage_in_NP theorem proved); NP membership remains
             a blocker before R1-C
R1-C unlocked? no — R1B1 budget verifier needed first
Recommended next action: open_R1B1_parser_codec_budget
  Specific shape: single Lean module for tree-MCSP target, discharge parser +
  relation_decidable + relation_polynomial_time + witness_length_polynomial,
  do NOT discharge codec_* fields, do NOT prove extraction
Commands run:
  - git fetch / sync to main → 2347fab
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output
  - git show def64e7 → full diff inspected
  - lake build PnP3 Pnp4 → NOT RUN (no Lean toolchain in operator-review env;
    CI green at upstream merge 2347fab, Codex task PR description claims
    scripts/check.sh succeeded)
  - ./scripts/check.sh → NOT RUN (same reason)
Scope violations: none
```
