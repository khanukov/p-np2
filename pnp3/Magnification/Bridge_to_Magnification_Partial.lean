import Magnification.PipelineStatements_Partial
import Magnification.Facts_Magnification_Partial
import Complexity.Interfaces
import Models.Model_PartialMCSP
import ThirdPartyFacts.PpolyFormula

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-!
  Partial MCSP bridge (formula track only).

  Active target: `NP ⊄ PpolyFormula` from the partial lower-bound pipeline.
  The strengthened route below also exposes `NP ⊄ PpolyReal` when a localized
  realization (`PpolyReal -> PpolyFormula`) is provided.
-/

theorem NP_not_subset_PpolyFormula_from_partial_formulas
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp : FormulaLowerBoundHypothesisPartial p δ :=
    formula_hypothesis_from_pipeline_partial (p := p) (δ := δ) hδ
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (δ := δ) hHyp

theorem NP_not_subset_PpolyFormula_from_partial_formulas_default
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_from_partial_formulas
    (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (δ := δ) hδ

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hHyp : FormulaLowerBoundHypothesisPartial p δ :=
    formula_hypothesis_from_pipeline_partial (p := p) (δ := δ) hδ
  exact
    OPS_trigger_formulas_partial_of_provider
      (hProvider := hProvider)
      (p := p)
      (hNP_TM := hNP_TM)
      (hGapEmbed := ThirdPartyFacts.gapPartialMCSP_ppoly_to_ppolyFormula_of_realization p hReal)
      (δ := δ) hHyp

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hNP_TM := hNP_TM)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_of_reifier p hReify)
    (δ := δ) hδ

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hNP_TM := hNP_TM)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_of_formulaizer p hF)
    (δ := δ) hδ

theorem NP_not_subset_PpolyReal_from_partial_formulas_trivial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hNP_TM := hNP_TM)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_trivial p)
    (δ := δ) hδ

/--
Preferred localized `PpolyReal` separation route: uses the internal trivial
realization bridge, so no explicit realization/reifier/formulaizer argument is
required from callers.
-/
theorem NP_not_subset_PpolyReal_from_partial_formulas
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact NP_not_subset_PpolyReal_from_partial_formulas_trivial
    (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (δ := δ) hδ

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_realization
      (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (hReal := hReal) (δ := δ) hδ)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_reifier
      (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (hReify := hReify) (δ := δ) hδ)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
      (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (hF := hF) (δ := δ) hδ)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_trivial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_Language p))
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_trivial
      (hProvider := hProvider) (p := p) (hNP_TM := hNP_TM) (δ := δ) hδ)

end Magnification
end Pnp3
