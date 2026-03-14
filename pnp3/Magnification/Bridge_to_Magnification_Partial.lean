import Magnification.PipelineStatements_Partial
import Magnification.Facts_Magnification_Partial
import Complexity.Interfaces
import Models.Model_PartialMCSP
import ThirdPartyFacts.PpolyFormula

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-!
  Partial MCSP bridge (formula track only).

  Active target: `NP ⊄ PpolyFormula` from the partial lower-bound pipeline.
  The strengthened route below also exposes `NP ⊄ PpolyReal` when a localized
  realization (`PpolyReal -> PpolyFormula`) is provided.
-/

theorem NP_not_subset_PpolyFormula_from_partial_formulas
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat}
  (hHyp : FormulaLowerBoundHypothesisPartial p δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider) (hNPstrict := hNPstrict) (p := p) (δ := δ) hHyp

/--
Preferred localized `PpolyReal` separation route: uses the internal trivial
realization bridge, so no extra realization/reifier/formulaizer wrappers are
required.
-/
theorem NP_not_subset_PpolyReal_from_partial_formulas
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  {δ : Rat}
  (hHyp : FormulaLowerBoundHypothesisPartial p δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact
    OPS_trigger_formulas_partial_of_provider
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := p)
      (hGapEmbed := ThirdPartyFacts.gapPartialMCSP_ppoly_to_ppolyFormula_of_realization
        p (ThirdPartyFacts.gapPartialMCSP_realization_trivial p))
      (δ := δ) hHyp

/-!
  Semantic bridge entrypoints (non-vacuous Step-C route).
-/

theorem NP_not_subset_PpolyFormula_from_partial_formulas_semantic
  (hProvider : StructuredLocalityProviderPartial_semantic)
  {p : GapPartialMCSPParams} {δ : Rat}
  (hHyp : FormulaLowerBoundHypothesisPartial_semantic p δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation_semantic
      (hProvider := hProvider) (hNPstrict := hNPstrict) (p := p) (δ := δ) hHyp

theorem NP_not_subset_PpolyReal_from_partial_formulas_semantic
  (hProvider : StructuredLocalityProviderPartial_semantic)
  {p : GapPartialMCSPParams}
  {δ : Rat}
  (hHyp : FormulaLowerBoundHypothesisPartial_semantic p δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact
    OPS_trigger_formulas_partial_of_provider_semantic
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := p)
      (hGapEmbed := ThirdPartyFacts.gapPartialMCSP_ppoly_to_ppolyFormula_of_realization
        p (ThirdPartyFacts.gapPartialMCSP_realization_trivial p))
      (δ := δ) hHyp

/--
Semantic bridge with auto-produced semantic lower-bound hypothesis from the
pipeline core.
-/
theorem NP_not_subset_PpolyFormula_from_partial_formulas_semantic_auto
  (hProvider : StructuredLocalityProviderPartial_semantic)
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  have hHyp : FormulaLowerBoundHypothesisPartial_semantic p δ :=
    formula_hypothesis_from_pipeline_partial_semantic (p := p) (δ := δ) hδ
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_semantic
      (hProvider := hProvider) (p := p) (δ := δ) hHyp hNPstrict

/--
Semantic `PpolyReal` bridge with auto-produced semantic lower-bound hypothesis.
-/
theorem NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto
  (hProvider : StructuredLocalityProviderPartial_semantic)
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  have hHyp : FormulaLowerBoundHypothesisPartial_semantic p δ :=
    formula_hypothesis_from_pipeline_partial_semantic (p := p) (δ := δ) hδ
  exact
    NP_not_subset_PpolyReal_from_partial_formulas_semantic
      (hProvider := hProvider) (p := p) (δ := δ) hHyp hNPstrict

end Magnification
end Pnp3
