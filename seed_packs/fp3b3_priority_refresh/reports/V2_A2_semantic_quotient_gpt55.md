# Route: V2-A.2 semantic quotient

**Handle:** gpt55  
**Report path:** `seed_packs/fp3b3_priority_refresh/reports/V2_A2_semantic_quotient_gpt55.md`  
**Progress classification:** infrastructure / meta-review only. This report does not implement Lean code, does not edit JSONL/spec/trust-root files, and does not introduce a candidate package, `SourceTheorem`, `gap_from`, `ResearchGapWitness`, accepted guard, FP-4 bridge, or final endpoint.

## 1. Route definition

V2-A.2 would be a successor design space for the V2-A provenance filter after two failures:

- bare V2-A is representation-sensitive and syntactic;
- V2-A.1 normalize-then-filter is self-defeating for the structural normalizer class that collapses the tautological seed needed to block NOGO-000008.

The core question is whether V2-A can be made robust under some semantic equivalence relation without becoming a classical Natural Proofs property of Boolean functions.

### A. Full semantic quotient

A **full semantic quotient** would make filter membership depend only on the Boolean function computed at each input length. Equivalently, if two displayed `FormulaCircuit` witnesses have the same truth table at every length, then V2-A.2 must give them the same answer.

Under this interpretation, syntactic quantities from V2-A cannot be read directly from the displayed formula. They must be replaced by extensional invariants such as:

- essential-variable set / semantic support;
- minimum formula size or minimum formula depth over all equivalent formulas;
- existence of an equivalent formula satisfying a V2-A-like syntactic shape;
- nonexistence of an equivalent hardwiring shape.

This would decisively remove the NOGO-000008 tautological-rewrite distinction, because the raw prefix-AND witness and its tautologically seeded rewrite compute the same function. But it also changes the route from a witness-level syntactic predicate into a property of truth tables / Boolean functions. That is exactly the direction where Razborov-Rudich risk becomes acute.

### B. Minimal-formula quotient

A **minimal-formula quotient** would choose, for each Boolean function at each length, a minimum representative under some measure, then apply the original V2-A syntactic checks to that representative. Possible minimization criteria include minimum total size, minimum Boolean-gate count, minimum depth, or lexicographic combinations of these.

This is not the same as full extensional filtering unless the canonicalization is itself invariant and unique up to irrelevant ties. Its intended benefit is that tautological seeds are removed because they are not present in a minimum representative.

However, the route is fragile:

- If a canonical representative is obtained by `Classical.choose`, V2-A.2 may become nonconstructive and opaque.
- If minimization returns a pure AND prefix representation for a genuine non-vacuity witness, the original V2-A mixed-gate clause may reject it, reproducing the V2-A.1 self-defeat in semantic/canonical form.
- If the theorem target only says there exists a minimum representative, it may hide the lower-bound difficulty in the minimization premise rather than prove an admissible provenance fact.

### C. Partial semantic quotient

A **partial semantic quotient** would not quotient by arbitrary Boolean equivalence. Instead it would identify only a narrow, explicitly generated class of local equivalence moves, with the motivating move being tautological seed insertion/removal:

- `C ↦ C ∧ (x ∨ ¬x)`;
- possibly local variants such as `C ∨ (x ∧ ¬x)`;
- perhaps associativity/commutativity/idempotence moves only if they are explicitly bounded and audited.

The key design constraint is that partial quotienting must be **rule-generated and representation-aware**, not truth-table complete. A partial quotient can plausibly say: “ignore this specific known adversarial ornament, but do not reconstruct arbitrary truth tables and do not minimize over all equivalent formulas.”

This option is the only V2-A.2 interpretation that may avoid immediate Natural Proofs re-entry. It is also the least ambitious: it only patches NOGO-000008-class tautology rewrites and does not claim robustness under general semantic rewriting.

## 2. NOGO interaction

### Summary table

| NOGO | A. Full semantic quotient | B. Minimal-formula quotient | C. Partial semantic quotient |
|---|---|---|---|
| NOGO-000006 arbitrary all-essential `ttFormula` payload | uncertain | uncertain | survives |
| NOGO-000007 support-cardinality meta-barrier | uncertain | uncertain | survives |
| NOGO-000008 tautological rewrite attack | survives | survives if minimization removes the seed | survives for covered tautology rules |
| NOGO-000009 normalize-then-filter meta-barrier | uncertain / outside formal scope | uncertain / analogous risk | uncertain / outside formal scope |

### NOGO-000006 — arbitrary all-essential `ttFormula` payload

**A. Full semantic quotient: uncertain.** The old V2-A exclusion used displayed `ttFormula` gate count at a concrete width. Once the predicate is extensional, it cannot reject merely because the supplied witness is the canonical truth-table formula. The same Boolean function may have a much smaller equivalent formula. To preserve the exclusion, V2-A.2 would need a semantic lower bound or a canonical-minimum-size statement. That is much stronger than the existing proof.

**B. Minimal-formula quotient: uncertain.** If the arbitrary all-essential payload has a large minimum formula, then the route may still reject it. But proving this for arbitrary payloads is essentially a lower-bound/minimization claim, not a syntactic audit fact. If minimization finds compact representatives for some payloads, the V2-A gate-count exclusion disappears.

**C. Partial semantic quotient: survives.** If the quotient only ignores tautological seed rewrites and closely bounded local moves, the canonical `ttFormula` payload remains the same displayed hardwiring shape for the existing NOGO-000006 audit. The original gate-count exclusion should remain conceptually available, provided no broad rewrite rules are added that can compress arbitrary truth-table formulas.

### NOGO-000007 — support-cardinality meta-barrier

**A. Full semantic quotient: uncertain.** V2-A originally dodged NOGO-000007 by not being support-cardinality-only: it also inspected displayed gate/depth/mixed-gate syntax. A full extensional quotient cannot rely on displayed syntax. It may still use semantic complexity quantities, but then it must show it is not merely support-cardinality-only in an extensional analogue. That is a new obligation.

**B. Minimal-formula quotient: uncertain.** Minimal size/depth could distinguish functions with the same support size, so the route might still avoid support-cardinality-only collapse. But if the only effectively used invariant is semantic support cardinality plus minimization that collapses the honest witness, the route can either become vacuous or fall back into a support-profile barrier.

**C. Partial semantic quotient: survives.** A rule-generated quotient can preserve V2-A's non-support-cardinality nature because it still looks at formula structure modulo only specified local ornaments. It must nevertheless prove a replacement of `V2_A2_not_support_cardinality_only`, since quotienting tautologies could accidentally identify the current distinguishing pair.

### NOGO-000008 — tautological rewrite attack

**A. Full semantic quotient: survives.** Full extensionality directly identifies the prefix-AND hardwiring witness and the tautologically seeded rewrite. If the excluded prefix-AND function is rejected, the rewrite must be rejected too.

**B. Minimal-formula quotient: survives if minimization removes the seed.** A minimum-size or minimum-gate representative should drop `∧ true` tautological clutter. But this is only reliable if the canonical/minimum representative is proved to be seed-free, not merely chosen nonconstructively among ties.

**C. Partial semantic quotient: survives for covered tautology rules.** This is the most targeted response: add invariance under exactly the seed insertion/removal used in `rewritePrefixAndWitness`. It survives NOGO-000008 only to the extent that the formal theorem covers the adversarial family and natural variants.

### NOGO-000009 — normalize-then-filter meta-barrier

**A. Full semantic quotient: uncertain / outside formal scope.** NOGO-000009 explicitly targets context-uniform bottom-up structural normalizers composed with V2-A. A full semantic quotient is outside that Lean class, but it may reproduce the same failure semantically: eliminating tautological seeds can also eliminate the mixed-gate feature that supplied V2-A non-vacuity.

**B. Minimal-formula quotient: uncertain / analogous risk.** This is the closest semantic analogue of the failed V2-A.1 patch. If the minimal representative of `seededPrefixAndFamily` is just a pure prefix-AND-like formula, the mixed-gate clause kills the non-vacuity witness. Thus NOGO-000009 does not formally kill the route, but it is a strong warning that minimization may be self-defeating.

**C. Partial semantic quotient: uncertain / outside formal scope.** A narrow quotient is not a bottom-up structural normalizer, so NOGO-000009 does not formally apply. Still, if the quotient rule erases the same tautological seed from the non-vacuity witness without replacing that witness or weakening the mixed-gate clause, the route can fail by the same mechanism.

## 3. Natural Proofs / Razborov-Rudich risk

### Does V2-A.2 re-enter the Natural Proofs barrier?

**For a full extensional quotient: likely YES.**

Reason: the original V2-A natural-proofs escape was representation sensitivity. It was explicitly not a property of Boolean functions alone. The existing audit classified V2-A as `representation_sensitive_escape_plausible` because two semantically equal witnesses could receive different filter answers. That same weakness caused NOGO-000008, but it was also the main reason V2-A did not immediately look like a Razborov-Rudich natural property.

A full semantic quotient removes exactly that escape hatch. If V2-A.2 is invariant under all Boolean equivalence, then at each length it defines a property of the truth table / Boolean function. If the property is also constructive from truth tables, large among Boolean functions, and useful against `P/poly`, it satisfies the repository's abstract Natural Proofs triad. The repository's `NaturalProofConditions` file is intentionally minimal, but the conceptual match is direct: full extensionality turns the filter from witness provenance into a Boolean-function property.

This does **not** by itself prove the route impossible. It means the burden shifts: V2-A.2 must either show non-constructivity, non-largeness, or non-usefulness in the Razborov-Rudich sense, or provide an explicit bypass witness. Without such a reason, opening a full semantic-quotient seed pack would be a high-risk detour.

### Minimal-formula quotient risk

Minimal-formula quotienting also has high Natural Proofs risk, but the failure mode is subtler.

If the predicate says “compute or choose a minimum representative, then check V2-A,” then membership is still invariant under Boolean equivalence if the minimization target is semantic. Therefore it is at least trying to define a property of Boolean functions. It may avoid **constructivity** only by being computationally intractable or nonconstructive, but that is not a clean success: a nonconstructive `Classical.choose` canonical representative is bad for an accepted provenance guard because it is hard to audit and can hide assumptions.

Thus minimal-formula quotienting faces a dilemma:

- if the canonical representative is effectively computable from truth tables, Natural Proofs risk increases;
- if it is not computable and relies on nonconstructive choice, it fails as a transparent provenance filter;
- if proving properties of the minimum representative requires lower bounds, the route may hide the main problem inside the canonicalization step.

### Partial semantic quotient risk

A partial semantic quotient **may avoid immediate Natural Proofs re-entry** if it is not truth-table complete.

The precise reason is this: a rule-generated quotient over displayed witnesses can remain a property of **representations modulo a small rewrite system**, not a property of Boolean functions. Two formulas computing the same function need not be equivalent under the partial quotient unless there is an explicit bounded derivation using the allowed local moves. Therefore the filter can be invariant under tautological seed rewrites while still failing full extensionality.

That distinction is not handwaving. The required formal shape would be:

- define a syntactic relation generated by named local equivalence moves;
- prove V2-A.2 invariant under those moves;
- prove the `rewritePrefixAndWitness` attack is related to the excluded prefix-AND witness by that relation;
- prove there exist semantically equal formulas not related by the partial quotient, or at least do **not** claim full Boolean extensionality.

If those conditions are met, V2-A.2 remains representation-sensitive at a coarser granularity. It patches NOGO-000008 without becoming a full truth-table property. However, this is only a “maybe not” for Natural Proofs. The route still needs a fresh natural-proofs audit because a sufficiently broad local rewrite system can silently become complete or effectively truth-table reconstructive.

## 4. Candidate theorem targets if route is viable

Exact theorem-name targets only:

- `V2_A2_invariant_under_tautology_seed`
- `V2_A2_excludes_rewritePrefixAnd`
- `V2_A2_not_support_cardinality_only`
- `V2_A2_nonvacuity_seededPrefixAnd_or_replacement`
- `V2_A2_not_full_semantic_extensional`
- `V2_A2_no_ttFormula_reconstruction_boundary`
- `V2_A2_partial_quotient_respects_V2_A_gate_cap`
- `V2_A2_partial_quotient_distinguishes_semantically_equal_unrelated_formulas`

## 5. Failure modes

At least the following failure modes must be treated as blockers before any accepted-status promotion is considered:

1. **Natural-proof re-entry.** A full semantic quotient turns V2-A into a truth-table / Boolean-function property and likely re-enters Razborov-Rudich territory unless constructivity, largeness, or usefulness is explicitly blocked.
2. **Vacuity via minimization hiding the lower bound.** A minimal representative may delete the mixed OR/NOT structure from the honest/non-vacuity witness, causing the filter to reject all intended witnesses; alternatively, proving that the minimum representative has the needed shape may smuggle in an unproved lower bound.
3. **`Classical.choose` / nonconstructive canonical representative.** A canonical minimum formula chosen nonconstructively can make the guard opaque, non-auditable, and dependent on arbitrary tie-breaking.
4. **Truth-table reconstruction becomes `ttFormula (eval C)`.** If the quotient canonicalizes by reconstructing from a truth table, it recreates the earlier V2-A.1 boundary problem: `ttFormula(eval C)` is exactly the kind of extensional reconstruction that destroys the witness-level syntactic escape and can import arbitrary hardwiring payloads.
5. **Partial quotient creep.** A local rewrite system intended only for tautological seeds may expand until it approximates full Boolean equivalence, silently converting the route into the high-risk full semantic quotient.
6. **NOGO-000006 regression.** Broad semantic rewriting can invalidate the displayed `ttFormula` gate-count exclusion by allowing compact equivalent representatives or by no longer considering the displayed truth-table formula.
7. **NOGO-000007 regression.** If quotienting removes the syntactic features that distinguished V2-A from support-cardinality-only filters, the route can fall back into the support-cardinality meta-barrier.
8. **NOGO-000009 analogue.** Even outside the formal `StructuralNormaliser` class, semantic seed erasure can still collapse V2-A's own seeded non-vacuity witness.

## 6. Recommendation

**Recommendation:** `dispatch_only_meta_review`

Do **not** dispatch `seed_packs/fp3b3_5_v2_a_2_semantic_quotient/` yet as a proof-oriented seed pack. First dispatch a narrow meta-review whose deliverable is a go/no-go decision between these three meanings of V2-A.2:

1. reject full semantic quotient unless a Natural Proofs bypass plan is explicit;
2. reject or heavily constrain minimal-formula quotient unless nonconstructive choice and vacuity are blocked;
3. consider only partial, rule-generated quotienting of tautological-seed rewrites as the plausible successor surface.

If the operator later chooses `dispatch_seed_pack`, the proposed seed pack name is:

`seed_packs/fp3b3_5_v2_a_2_semantic_quotient/`

The seed pack should be scoped as infrastructure / audit formalization, not mainline P-vs-NP progress. It should forbid full extensionality unless paired with an explicit Natural Proofs bypass obligation.

---

## Output summary

**Route:** V2-A.2 semantic quotient  
**Handle:** gpt55  
**Report path:** `seed_packs/fp3b3_priority_refresh/reports/V2_A2_semantic_quotient_gpt55.md`  
**Verdict:** viable only as a narrowly scoped partial semantic quotient; full semantic quotient is high-risk and should not be opened without a Natural Proofs bypass plan.  
**Natural-proofs risk:** high / likely YES for full extensional quotient; medium-high for minimal-formula quotient; lower but still audit-required for partial rule-generated quotient.  
**NOGO-000008 response:** full quotient survives; minimal quotient survives only if seed removal is proved; partial quotient survives for explicitly covered tautological-seed rewrites.  
**NOGO-000009 response:** not formally covered because V2-A.2 is outside the `StructuralNormaliser` class, but minimal and partial semantic seed-erasure variants can reproduce the same self-defeat by killing V2-A non-vacuity.  
**Recommended next action:** `dispatch_only_meta_review`  
**Commands run:** `./scripts/check.sh`  
**Scope violations:** none; markdown report and `.gitkeep` only, no Lean code, no JSONL edits, no spec edits, no trust-root edits, no accepted promotion, no FP-4, no `SourceTheorem`, no `gap_from`, no final endpoint, no candidate package.
