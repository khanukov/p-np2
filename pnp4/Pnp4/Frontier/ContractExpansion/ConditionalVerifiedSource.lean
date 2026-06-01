import Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Conditional verified DAG-lower-bound source

Block 9e of the downstream decision→search extraction.

The polynomial-target contrapositive (#1511, Block 9d) gives the `¬ PpolyDAG`
half of a `VerifiedNPDAGLowerBoundSource`:

```
TreeMCSPExtractionGrowthAssumptions codec
→ NoPolynomialBoundedSearchSolver codec
→ ¬ PpolyDAG (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))
```

A `VerifiedNPDAGLowerBoundSource` needs one orthogonal extra input — `NP`
membership of the same language — which lives on a *separate* verifier/runtime
track and is **not** proved here.  This file just *packages* the two halves: given
the growth assumptions, the (open) polynomial weak lower bound, **and** an explicit
`NP`-membership hypothesis, it constructs the source record, and (as a convenience)
derives the `NP ⊄ PpolyDAG` separation from it via the existing
`NP_not_subset_PpolyDAG_of_verified_source` bridge.

Everything is **conditional**: all three inputs are explicit hypotheses.  Nothing
new is asserted unconditionally.

Scope discipline — conditional source packaging only:

* `NP`-membership is an **explicit hypothesis** — **not** proved here;
* `NoPolynomialBoundedSearchSolver` (the open weak lower bound) and the growth
  assumptions are **explicit hypotheses** — **not** proved here;
* **no** change to `SearchMCSPMagnificationContract`;
* **no** `P ≠ NP` endpoint theorem and **no** unconditional endpoint claim.
-/

variable {threshold : Nat → Nat}

/--
**Conditional verified DAG-lower-bound source.**

Given, for a tree-circuit witness codec:

1. the explicit polynomial growth assumptions `TreeMCSPExtractionGrowthAssumptions`;
2. the (open) polynomial weak lower bound `NoPolynomialBoundedSearchSolver`;
3. an explicit `NP`-membership proof for the prefix-extension language,

assemble a `VerifiedNPDAGLowerBoundSource`.  The `notInPpolyDAG` field is supplied by
the Block-9d contrapositive
`not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`; the `inNP` field is
exactly the supplied hypothesis.
-/
noncomputable def verifiedSource_of_noPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage
          (treeMCSPConcretePrefixParser threshold codec))) :
    VerifiedNPDAGLowerBoundSource where
  L := PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)
  inNP := hNP
  notInPpolyDAG :=
    not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver
      codec hGrowth hNoPoly

/--
Convenience wrapper: the same three explicit hypotheses yield the canonical
DAG-separation target `NP ⊄ PpolyDAG`, via the existing
`NP_not_subset_PpolyDAG_of_verified_source` bridge applied to the source package.

This is still strictly **conditional** on the `NP`-membership and no-poly-solver
hypotheses; it is **not** the `P ≠ NP` endpoint and asserts nothing unconditionally.
-/
theorem NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage
          (treeMCSPConcretePrefixParser threshold codec))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_verified_source
    (verifiedSource_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly hNP)

end ContractExpansion
end Frontier
end Pnp4
