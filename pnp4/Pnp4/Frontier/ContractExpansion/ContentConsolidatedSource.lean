import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer
import Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation

/-!
# Consolidated conditional source through the content-truthful language — §13 repair, brick R5

Re-routes the consolidated two-input conditional chain through `L'`
(`ContentPrefixExtensionLanguage`), completing the §13 repair at the specification level:

* `inNP` half: the content-truthful NP witness (brick R2) — **achievable** by a length-blind
  idle-sink machine, unlike the length-gated original (§13.1);
* `¬PpolyDAG` half: the **same** open lower-bound hypothesis `NoPolynomialBoundedSearchSolver`,
  via the transferred extraction (brick R4).

`verifiedSourceCT_treePoly` is the repaired analogue of `verifiedSource_treePoly`: at the concrete
polynomial threshold `thresholdPoly k`, the growth premise is discharged and the source depends on
exactly the two genuinely-open inputs — input (1) unchanged, input (2) now the **content-truthful**
witness `ContentPrefixExtensionNPWitness`.  The original length-gated chain is left intact for
reference; the machine track (M5–M11 of §12) should target the CT witness.

**Progress classification (AGENTS.md): Infrastructure** — conditional packaging; both inputs remain
explicit hypotheses; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

variable {threshold : Nat → Nat}

/-- **Conditional verified DAG-lower-bound source through `L'`.**  Growth assumptions + the open
no-polynomial-solver bound + a content-truthful NP witness assemble a
`VerifiedNPDAGLowerBoundSource` whose language is `ContentPrefixExtensionLanguage`. -/
noncomputable def verifiedSourceCT_of_noPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNPWit : ContentPrefixExtensionNPWitness codec) :
    VerifiedNPDAGLowerBoundSource where
  L := ContentPrefixExtensionLanguage codec
  inNP := contentPrefixExtensionLanguage_in_NP_of_witness codec hNPWit
  notInPpolyDAG :=
    not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver
      codec hGrowth hNoPoly

/-- **Consolidated CT source at a concrete polynomial threshold** (the §13-repaired analogue of
`verifiedSource_treePoly`): for `thresholdPoly k` the growth premise is discharged, so the source
depends on only the two genuinely-open inputs — the open lower bound (input (1), unchanged) and the
**content-truthful** NP witness (the repaired input (2)). -/
noncomputable def verifiedSourceCT_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))) :
    VerifiedNPDAGLowerBoundSource :=
  verifiedSourceCT_of_noPolynomialBoundedSearchSolver
    (treeCircuitWitnessCodec (thresholdPoly k))
    (treePolynomialWitnessCodec (thresholdPoly k)
      (polyBoundedInTable_thresholdPoly k)).toGrowthAssumptions
    hNoPoly hNPWit

/-- **Consolidated conditional separation through `L'`.**  The same two inputs yield the
conditional `NP ⊄ PpolyDAG`.  Still strictly conditional; **not** the `P ≠ NP` endpoint. -/
theorem NP_not_subset_PpolyDAG_treePolyCT
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_verified_source
    (verifiedSourceCT_treePoly k hNoPoly hNPWit)

end ContractExpansion
end Frontier
end Pnp4
