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
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  have hHyp : FormulaLowerBoundHypothesisPartial p δ :=
    formula_hypothesis_from_pipeline_partial (p := p) (δ := δ) hδ
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider) (hNPstrict := hNPstrict) (p := p) (δ := δ) hHyp

theorem NP_not_subset_PpolyFormula_from_partial_formulas_default
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact NP_not_subset_PpolyFormula_from_partial_formulas
    (hProvider := hProvider) (p := p) (δ := δ) hδ hNPstrict

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  have hHyp : FormulaLowerBoundHypothesisPartial p δ :=
    formula_hypothesis_from_pipeline_partial (p := p) (δ := δ) hδ
  exact
    OPS_trigger_formulas_partial_of_provider
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := p)
      (hGapEmbed := ThirdPartyFacts.gapPartialMCSP_ppoly_to_ppolyFormula_of_realization p hReal)
      (δ := δ) hHyp

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_of_reifier p hReify)
    (δ := δ) hδ hNPstrict

theorem NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_of_formulaizer p hF)
    (δ := δ) hδ hNPstrict

theorem NP_not_subset_PpolyReal_from_partial_formulas_trivial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact NP_not_subset_PpolyReal_from_partial_formulas_with_realization
    (hProvider := hProvider)
    (p := p)
    (hReal := ThirdPartyFacts.gapPartialMCSP_realization_trivial p)
    (δ := δ) hδ hNPstrict

/--
Preferred localized `PpolyReal` separation route: uses the internal trivial
realization bridge, so no explicit realization/reifier/formulaizer argument is
required from callers.
-/
theorem NP_not_subset_PpolyReal_from_partial_formulas
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  intro hNPstrict
  exact NP_not_subset_PpolyReal_from_partial_formulas_trivial
    (hProvider := hProvider) (p := p) (δ := δ) hδ hNPstrict

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_realization
      (hProvider := hProvider) (p := p) (hReal := hReal) (δ := δ) hδ hNPstrict)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_reifier
      (hProvider := hProvider) (p := p) (hReify := hReify) (δ := δ) hδ hNPstrict)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer p)
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
      (hProvider := hProvider) (p := p) (hF := hF) (δ := δ) hδ hNPstrict)

theorem NP_not_subset_PpolyFormula_from_partial_formulas_trivial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  {δ : Rat} (hδ : (0 : Rat) < δ) :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_PpolyReal
    (NP_not_subset_PpolyReal_from_partial_formulas_trivial
      (hProvider := hProvider) (p := p) (δ := δ) hδ hNPstrict)

end Magnification
end Pnp3
