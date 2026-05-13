# M1 candidate — structural normalisation meta-barrier

Slot: M1  
Handle: `m1nova`  
Pack: `fp3b3_4_v2_a_normalise_meta_barrier`  
Outcome recommendation: **`PROCEED to M2` (`PROCEED_TO_M2`)**

## Reading anchors and classification

This is a markdown-only side-track audit exploration; it does not add Lean, edit `fp3b3_3`, or claim mainline `P != NP` progress.  I use the following repository facts.

* `FormulaCircuit` is fixed trust-root syntax with constructors `const`, `input`, `not`, `and`, `or`, plus fixed `eval`, `size`, `depth`, and `support` definitions (`pnp3/Complexity/Interfaces.lean:64-104`).
* V2-A/gpt55 is a displayed-syntax predicate: unbounded support, linear Boolean-gate count, linear depth, and an OR/NOT mix for support at least two (`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/Filter.lean:138-162`).
* `seedGate n h` is `(x₀ ∨ ¬x₀)`, and `seededPrefixAndFamily n` conjoins full prefix-AND with that seed at positive lengths (`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NonVacuity.lean:23-40`).
* NOGO-000008 records that conjoining the same seed to log-width prefix-AND preserves semantics, adds constant overhead, and passes V2-A/gpt55 (`outputs/nogolog.jsonl:8`; `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean:37-53,165-212`).
* fp3b3_3 T1 now requires structural normalisation, seed collapse, constant-negation reductions, and a canonical-output invariant rather than raw-syntax NOT involution (`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/README.md:126-159,177-245`).

## Section A — Predicate class `StructuralNormaliser`

### A.1 Proposed formal shape

The class should not be an arbitrary endofunction `FormulaCircuit n → FormulaCircuit n`.  The useful boundary is **context-uniform bottom-up recursion**: the normaliser recursively normalises children, then applies one local syntactic constructor to the already-normalised children.  Therefore the same `seedGate` subtree has the same image in every context.

```lean
namespace V2_A_NormaliseMetaBarrier

open Pnp3.ComplexityInterfaces
open FormulaCircuit

/-- Allowed local constructors.  `LocalCaseTree` is an M1 placeholder for an
    inductive DSL that can inspect only constructor tags, constants, and
    syntactic equality of already-present child syntax. -/
structure LocalFormulaOps where
  mkNot : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  mkAnd : ∀ {n}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkOr  : ∀ {n}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkNot_eval : ∀ {n} C x, eval (mkNot C) x = eval (not C) x
  mkAnd_eval : ∀ {n} A B x, eval (mkAnd A B) x = eval (and A B) x
  mkOr_eval  : ∀ {n} A B x, eval (mkOr A B) x = eval (or A B) x
  mkNot_size : ∀ {n} C, size (mkNot C) ≤ size (not C)
  mkAnd_size : ∀ {n} A B, size (mkAnd A B) ≤ size (and A B)
  mkOr_size  : ∀ {n} A B, size (mkOr A B) ≤ size (or A B)
  syntacticOnly : LocalCaseTree mkNot ∧ LocalCaseTree₂ mkAnd ∧ LocalCaseTree₂ mkOr

def foldFormula (ops : LocalFormulaOps) : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  | _, const b => const b
  | _, input i => input i
  | _, not C => ops.mkNot (foldFormula ops C)
  | _, and A B => ops.mkAnd (foldFormula ops A) (foldFormula ops B)
  | _, or A B => ops.mkOr (foldFormula ops A) (foldFormula ops B)

structure StructuralNormaliser where
  ops : LocalFormulaOps
  normalise : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  normalise_eq_fold : ∀ {n} (C : FormulaCircuit n), normalise C = foldFormula ops C
  eval_pres : ∀ {n} (C : FormulaCircuit n) (x : Bitstring n), eval (normalise C) x = eval C x
  size_le : ∀ {n} (C : FormulaCircuit n), size (normalise C) ≤ size C
  depth_le_size : ∀ {n} (C : FormulaCircuit n), depth (normalise C) ≤ size C
  context_uniform : ContextUniform normalise normalise_eq_fold
  noTruthTable_noChoose : ComputableLocalDSL ops.syntacticOnly

end V2_A_NormaliseMetaBarrier
```

### A.2 Why this class

`normalise_eq_fold` is the load-bearing constraint.  It rules out semantic quotients and whole-family whitelists while admitting g55-style local simplification.  I intentionally avoid requiring global confluence, a unique canonical representative, or full support preservation in the class statement; those may be proof lemmas, but adding them at M1 risks a vacuous theorem that excludes the intended T1 normaliser.

## Section B — Meta-barrier statement candidate

### B.1 Auxiliary predicates

```lean
namespace V2_A_NormaliseMetaBarrier

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55
open Pnp3.Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness

def normalisedWitness (𝒩 : StructuralNormaliser) {L : Language} (w : InPpolyFormula L) : InPpolyFormula L :=
  { polyBound := w.polyBound, polyBound_poly := w.polyBound_poly,
    family := fun n => 𝒩.normalise (w.family n),
    family_size_le := by intro n; exact Nat.le_trans (𝒩.size_le (w.family n)) (w.family_size_le n),
    correct := by intro n x; trans eval (w.family n) x; exact 𝒩.eval_pres (w.family n) x; exact w.correct n x }

abbrev V2_A_with_normaliser (𝒩 : StructuralNormaliser) {L : Language} (w : InPpolyFormula L) : Prop :=
  ProvenanceFilter_v2_V2_A_gpt55_Filter (normalisedWitness 𝒩 w)

def EliminatesSeedGate (𝒩 : StructuralNormaliser) : Prop :=
  ∀ {n} (h : 1 ≤ n), 𝒩.normalise (seedGate n h) = FormulaCircuit.const true

def EliminatesAndTrue (𝒩 : StructuralNormaliser) : Prop :=
  (∀ {n} (C : FormulaCircuit n), 𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) ∧
  (∀ {n} (C : FormulaCircuit n), 𝒩.ops.mkAnd (FormulaCircuit.const true) C = C)

def PreservesSeededNonVacuity (𝒩 : StructuralNormaliser) : Prop :=
  V2_A_with_normaliser 𝒩 seededPrefixAndWitness

def RejectsRewriteAttack (𝒩 : StructuralNormaliser) : Prop :=
  ¬ V2_A_with_normaliser 𝒩 rewritePrefixAndWitness
```

### B.2 Candidate theorem

```lean
/-- Context-uniform structural seed elimination kills V2-A's own seeded
    non-vacuity witness; therefore the normalised V2-A filter cannot both admit
    that witness and reject NOGO-000008's rewrite witness. -/
theorem v2_a_structural_normalisation_meta_barrier :
    ∀ (𝒩 : StructuralNormaliser),
      EliminatesSeedGate 𝒩 → EliminatesAndTrue 𝒩 →
      ¬ (PreservesSeededNonVacuity 𝒩 ∧ RejectsRewriteAttack 𝒩) := by
  -- M1 statement only.
```

M2 should first prove the stronger intermediate:

```lean
theorem normalise_seededPrefixAndFamily_eq_prefixAnd
    (𝒩 : StructuralNormaliser) (hSeed : EliminatesSeedGate 𝒩) (hAnd : EliminatesAndTrue 𝒩)
    (n : Nat) (h : 1 ≤ n) :
  𝒩.normalise (seededPrefixAndFamily n) =
    𝒩.normalise (prefixAnd n n (Nat.le_refl n))
```

I avoid the initially tempting antecedent `𝒩.normalise (seededPrefixAndFamily n) = seededPrefixAndFamily n`: under bottom-up seed elimination it is already inconsistent for positive `n`.  The real non-vacuity target is admission by the composed filter.

## Section C — Counterexample analysis

### C(1). Trivial-failure candidates: not in `StructuralNormaliser`

1. **Truth-table canonical representative.**  Map `C` to the smallest syntax computing the same truth table.  It may be eval-preserving, but it inspects all `2^n` inputs and likely uses minimising choice, so it fails `noTruthTable_noChoose`.
2. **Semantic quotient by language.**  Choose a representative of the Boolean-function equivalence class of `C`.  This is extensional, not local structural recursion, and is outside V2-A.1.
3. **Whole-family whitelist.**  Collapse `seedGate` and `rewritePrefixAndFamily`, but leave `seededPrefixAndFamily` unchanged.  This is syntactic and decidable, but not context-uniform: the same seed subtree is treated differently in different parents.
4. **Identity normaliser.**  It is structural and size-preserving, but fails `EliminatesSeedGate`; it shows the class is inhabited without satisfying the anti-NOGO antecedent.
5. **Root-only seed eraser.**  Collapse only formulas whose root is literally `seedGate`; do not recurse.  It fails `normalise_eq_fold` and would not remove the seed inside the adversarial rewrite.

### C(2). Vacuous-candidate pitfalls and revisions

1. **Literal preservation of `seededPrefixAndFamily`.**  Together with bottom-up `seedGate ↦ const true`, this is inconsistent for positive lengths.  Revision: use `PreservesSeededNonVacuity` instead.
2. **Class forbids all OR/NOT tautologies globally.**  Then the V2-A mixed-gate clause is doomed by definition.  This bakes in the conclusion and may exclude g55's intended normaliser.
3. **Mandatory full confluence/idempotent canonical form.**  Useful but not part of fp3b3_3 T1 HARD minimum.  If imposed, the theorem may be about an artificially tiny class.
4. **Conclusion `RejectsRewriteAttack 𝒩` alone.**  False for weak structural normalisers.  The intended conclusion negates the simultaneous admit-seeded/reject-rewrite conjunction.
5. **Zero-length contradiction.**  At `n = 0`, `seededPrefixAndFamily` is `const false`; the mixed-gate clause should only be used when support is at least two.

### C(3). g55's intended normaliser

The candidate class is designed to include g55's retry normaliser.  The failure report describes a syntax-directed `canonicalNormalise` with local subtree equality for literal complement detection, local NOT/AND/OR constructors, and planned structural-induction proofs of eval preservation and size non-increase (`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md:6-27`).  The audit verified this as non-forbidden structural recursion and classified the obstruction as local proof engineering, not a structural impossibility (`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md:77-144`).

Concrete prediction: g55r1 can still land T1, but if its normaliser is composed with V2-A/gpt55 as `V2_A_with_normaliser`, the displayed tautological OR/NOT seed disappears from `seededPrefixAndWitness`.  The normalised witness then fails V2-A's mixed-gate clause at support at least two unless T2 changes the non-vacuity witness or the filter design.  This is a barrier to that composition, not a claim that the T1 retry itself is impossible.

### C(4). Plausible existence proof / anti-meta-barrier attempt

The strongest anti-meta-barrier construction is a whole-family whitelist:

```lean
def whitelistNormalise {n} (C : FormulaCircuit n) : FormulaCircuit n :=
  if C is exactly seedGate n h then const true
  else if C is exactly rewritePrefixAndFamily n then adversaryFamily_v_natlog2 n
  else if C is exactly seededPrefixAndFamily n then seededPrefixAndFamily n
  else structurally recurse with local tautology reductions
```

This defeats any loose theorem based only on computable syntactic normalisation: it eliminates the isolated/adversarial seed while preserving the honest seeded witness.  It does **not** defeat the proposed class, because it is not bottom-up context-uniform.  A fold normaliser must normalise the identical `seedGate n h` child to the same `const true` before the parent is processed in both the honest and adversarial families.  Therefore I do not ship a no-viable-statement report.

## Section D — Proof-strategy preview (NOT proof attempt)

Preferred strategy: **adversarial-rewrite / subtree-uniformity argument**.

1. Formalise `LocalCaseTree` as an inductive DSL for allowed local constructors.
2. Prove the DSL evaluator is total and has no truth-table access.
3. Define `foldFormula ops` by structural recursion.
4. Prove every `StructuralNormaliser.normalise` equals the fold.
5. Prove fold congruence for equal recursively normalised children.
6. Specialise congruence to the `seedGate` subtree.
7. Use `EliminatesSeedGate` to rewrite `𝒩.normalise (seedGate n h)` to `const true`.
8. Expand `seededPrefixAndFamily n` for `h : 1 ≤ n`.
9. Its positive branch is `and fullPrefix (seedGate n h)`.
10. Fold expansion gives `mkAnd (𝒩.normalise fullPrefix) (𝒩.normalise seedGate)`.
11. Rewrite the second argument to `const true`.
12. Apply the right half of `EliminatesAndTrue`.
13. Conclude the normalised seeded family equals `𝒩.normalise fullPrefix`.
14. Repeat for `rewritePrefixAndFamily n`, replacing full prefix by log-width prefix.
15. Prove `prefixAnd n n` has no OR gates and no NOT gates.
16. Show the local constructors do not introduce OR/NOT when all input children are AND/input-only.
17. If not derivable from `LocalCaseTree`, add an explicit `NoInventsMixedGatesOnAndOnly` field in M2.
18. Check this field against g55r1; it should hold because the intended simplifier deletes/simplifies gates rather than inventing OR/NOT gates.
19. Establish enough support preservation for `prefixAnd n n` after normalisation.
20. Avoid global support preservation: tautology deletion may legitimately shrink support.
21. A precise field may be `support_pres_on_prefixAnd` only for full prefix conjunctions.
22. Alternatively prove a concrete `n = 2` contradiction, avoiding general support preservation.
23. Use support at least two plus zero OR/NOT to contradict V2-A's mixed-gate clause.
24. Derive `¬ PreservesSeededNonVacuity 𝒩`.
25. Infer `¬ (PreservesSeededNonVacuity 𝒩 ∧ RejectsRewriteAttack 𝒩)`.
26. Keep the rewrite-side lemma as explanatory evidence tying the theorem to NOGO-000008.
27. Mirror the support-cardinality barrier style: narrow structural invariant, witness-level contradiction, no endpoint claim.
28. Treat `n = 0` and `n = 1` separately; use `n ≥ 2` for the mixed-gate contradiction.
29. Re-run Section C if M2 adds either no-invention or prefix-support fields.
30. If those fields exclude g55's intended normaliser, downgrade to HOLD.
31. If g55r1 satisfies them, the M3 theorem should be narrow and non-vacuous.
32. The finite-`n=2` route is less elegant but may avoid overstrengthening the class.
33. The general support route is cleaner but risks proof-engineering debt.
34. In either route, the theorem remains an audit-route side-track result only.
35. Do not add source theorem, gap, candidate package, endpoint language, NOGO entry, or registry changes.
36. Expected core proof size after definitions: two fold-expansion lemmas plus one V2-A mixed-gate contradiction.
37. Check whether `EliminatesAndTrue` should mention `ops.mkAnd` or `normalise (and C true)`.
38. Prefer `ops.mkAnd`: it directly matches the fold expansion after children are normalised.
39. Add wrapper lemmas translating fp3b3_3 T1 statements about `canonicalNormalise (and C true)`.
40. Confirm those wrappers do not require raw-syntax `C`, only already-normalised children.
41. Prove the analogous left-identity wrapper for `and true C`.
42. For `seedGate`, avoid proving semantic tautology; use the HARD-minimum syntactic collapse hypothesis.
43. For support at `n = 2`, compute the two prefix inputs explicitly if the general proof stalls.
44. For the general route, reuse existing prefix-support lemmas rather than introducing a semantic support notion.
45. Keep the final theorem phrased as failure of the conjunction, not as unconditional rejection of all rewrites.
46. Include a non-vacuity sanity lemma showing identity normaliser inhabits the structural class minus seed elimination.
47. Include another sanity lemma showing g55-style constructors satisfy the local DSL assumptions.
48. Do not require commutative canonical ordering of AND/OR; it is irrelevant to the seed argument.
49. Do not require full idempotence; one bottom-up pass is enough for the subtree-uniformity contradiction.
50. M2 deliverable should end with a go/no-go table for each extra hypothesis considered.

## Section E — Recommended next step

**Recommendation: `PROCEED to M2` (`PROCEED_TO_M2`).**  The viable statement is not literal preservation of `seededPrefixAndFamily`; that is vacuous under bottom-up seed elimination.  The viable statement says that any context-uniform structural normaliser strong enough to delete the NOGO-000008 tautology seed and AND-true wrapper necessarily deletes the same visible seed from V2-A's own seeded non-vacuity witness, so the composed V2-A filter cannot both admit the seeded witness and reject the rewrite attack.  The obvious whitelist counterexample defeats looser computable-syntactic classes but fails the proposed fold/context-uniform class.  M2 should sharpen whether explicit `NoInventsMixedGatesOnAndOnly` and prefix-support-preservation hypotheses are needed; if those exclude g55's intended normaliser, downgrade to HOLD rather than M3.
