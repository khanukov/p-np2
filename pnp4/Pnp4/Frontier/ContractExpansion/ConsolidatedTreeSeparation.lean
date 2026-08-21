import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Consolidated conditional separation at a concrete polynomial threshold

Block 13b — the consolidation milestone for the downstream decision→search
extraction.

At a **concrete polynomial threshold** `thresholdPoly k` the growth premise is
already discharged (`polyBoundedInTable_thresholdPoly`, Block 13a), so the whole
verified chain — concrete codec (#1522), conditional source (#1523), growth
reduction, decision→search extraction — collapses to depend on **exactly two**
explicit hypotheses:

* `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))` — a
  genuine `P/poly` circuit lower bound for the concrete tree-MCSP search problem;
* `PrefixExtensionNPWitness (treeMCSPConcretePrefixParser (thresholdPoly k) …)` — a
  concrete NP verifier (TM + runtime + certificate correctness).

This file states that collapsed form once and for all.

## Honest status — what this is, and is **not**

* It **is** a complete, machine-checked, vacuity-free *conditional* chain: the two
  hypotheses above (for some polynomial degree `k`) yield a
  `VerifiedNPDAGLowerBoundSource`, hence `NP ⊄ PpolyDAG`, hence (via the existing
  pnp3 bridge) `P ≠ NP`.  All links are theorems with complete proofs (no proof
  holes) and only the standard axioms.
* It is **not** unconditional progress, and it is **not** a hardness-*magnification*
  result.  The decision→search extraction is formalized in **one direction only** —
  `PpolyDAG (prefix-extension language) → polynomial-size bounded search solver`
  (`boundedSearchSolver_of_PpolyDAG_prefixExtension`, `BoundedSolverFromPpoly.lean`)
  plus its contrapositive
  (`not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`,
  `ExtractedScheduleGrowth.lean`).  The converse (solver ⇒ `PpolyDAG`) is **not**
  formalized, so this is a one-way reduction and *not* an equivalence.  Since the
  instance length is `tableLen n = 2^n`, `NoPolynomialBoundedSearchSolver` is therefore
  *at least as strong as* the full `P/poly` lower bound — "this concrete NP language is
  not in `P/poly`" — and, absent the converse, possibly strictly stronger; it is *not* a
  weak/local bound amplified by a magnification theorem.  The chain makes the target
  **precise, concrete, and verified-conditional**; it does **not** make the open
  mathematics easier.

The two remaining hypotheses are exactly the genuine frontier: a circuit lower bound
(open research) and an NP-verifier construction (engineering/verification).

Scope discipline — consolidation only:

* the two inputs are **explicit hypotheses** — **neither** proved here;
* **no** `SearchMCSPMagnificationContract` change, **no** `P ≠ NP` endpoint wrapper,
  **no** unconditional claim.
-/

/--
**Consolidated verified source at a concrete polynomial threshold.**  For
`thresholdPoly k` the growth premise is discharged, so the verified
DAG-lower-bound source depends on only the two genuinely-open inputs.
-/
noncomputable def verifiedSource_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    (thresholdPoly k) (polyBoundedInTable_thresholdPoly k) hNoPoly hNPWit

/--
**Consolidated conditional separation.**  The same two inputs (at any polynomial
threshold degree `k`) yield the conditional `NP ⊄ PpolyDAG`.  Still strictly
conditional; **not** the `P ≠ NP` endpoint.
-/
theorem NP_not_subset_PpolyDAG_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    (thresholdPoly k) (polyBoundedInTable_thresholdPoly k) hNoPoly hNPWit

end ContractExpansion
end Frontier
end Pnp4
