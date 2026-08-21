import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer
import Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation

/-!
# Consolidated conditional source through the content-truthful language — repair brick R5

Re-routes the consolidated two-input conditional chain through `L'`
(`ContentPrefixExtensionLanguage`).  This re-routing is all that is done: the specification-side
obligation that would justify calling the repair complete — padding stability of `ContentAccepts` —
is **not** discharged in this slice.  The two halves of the source:

* `inNP` half: the content-truthful NP witness (brick R2) — an **explicit hypothesis**, exactly as
  before.  Its target language has no physical-length gate, so the length-blindness obstruction has
  nothing to attach to; that is a definitional observation, not a positive result.  No verifier
  machine, runtime bound, `TM.accepts` bridge, or padding-stability lemma is constructed anywhere, so
  nothing here shows the witness is satisfiable — nor that `ContentAccepts` is;
* `¬PpolyDAG` half: the **same** open lower-bound hypothesis `NoPolynomialBoundedSearchSolver`,
  via the transferred extraction (brick R4).

`verifiedSourceCT_treePoly` is the repaired analogue of `verifiedSource_treePoly`: at the concrete
polynomial threshold `thresholdPoly k`, the growth premise is discharged and the source depends on
exactly the two genuinely-open inputs — input (1) unchanged, input (2) now the **content-truthful**
witness `ContentPrefixExtensionNPWitness`.  The original length-gated chain is left intact for
reference; a future machine track should target the CT witness.

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

/-- **Consolidated CT source at a concrete polynomial threshold** (the repaired analogue of
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
