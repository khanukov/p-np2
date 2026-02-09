import Magnification.PipelineStatements_Partial
import Magnification.Facts_Magnification_Partial
import Complexity.Interfaces
import Models.Model_PartialMCSP

/-!
  pnp3/Magnification/Bridge_to_Magnification_Partial.lean

  Partial MCSP bridge (formula track only).

  This file mirrors the legacy `Bridge_to_Magnification` but only for the
  partial formula/AC⁰ track.  The OPS trigger is now proved in
  `Facts_Magnification_Partial.lean` after porting locality-lift.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-!
  ### Partial MCSP bridge for formulas
-/

theorem NP_not_subset_Ppoly_from_partial_formulas
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  NP_not_subset_Ppoly := by
  have hHyp : FormulaLowerBoundHypothesisPartial p δ :=
    formula_hypothesis_from_pipeline_partial (p := p) (δ := δ) hδ
  exact OPS_trigger_formulas_partial (p := p) (δ := δ) hHyp

theorem P_ne_NP_from_partial_formulas
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) : P_ne_NP := by
  have hNP : NP_not_subset_Ppoly :=
    NP_not_subset_Ppoly_from_partial_formulas (p := p) (δ := δ) hδ
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

end Magnification
end Pnp3
