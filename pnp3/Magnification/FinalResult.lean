import Magnification.Bridge_to_Magnification_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces
import ThirdPartyFacts.PpolyFormula

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-- Canonical Partial MCSP parameters used in the final bridge. -/
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
  gap_ok := by decide
  n_large := by decide
  sYES_pos := by decide
  circuit_bound_ok := by native_decide

/--
Active final statement of the partial pipeline:
from the structured provider we derive `NP ⊄ PpolyFormula`.
-/
theorem NP_not_subset_PpolyFormula_final
  (hProvider : StructuredLocalityProviderPartial) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyFormula_final_with_provider
  (hProvider : StructuredLocalityProviderPartial) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_final hProvider

theorem NP_not_subset_PpolyFormula_final_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_with_realization
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hReal := hReal)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyReal_final_with_realization
  (hProvider : StructuredLocalityProviderPartial)
  (hReal : ThirdPartyFacts.GapPartialMCSPFormulaRealization canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyReal_from_partial_formulas_with_realization
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hReal := hReal)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyFormula_final_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_with_reifier
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hReify := hReify)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyReal_final_with_reifier
  (hProvider : StructuredLocalityProviderPartial)
  (hReify : ThirdPartyFacts.GapPartialMCSPFormulaReifier canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyReal_from_partial_formulas_with_reifier
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hReify := hReify)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyFormula_final_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hF := hF)
      (δ := (1 : Rat)) hδ

theorem NP_not_subset_PpolyReal_final_with_formulaizer
  (hProvider : StructuredLocalityProviderPartial)
  (hF : ThirdPartyFacts.GapPartialMCSPFormulaizer canonicalPartialParams) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
      (hProvider := hProvider)
      (p := canonicalPartialParams)
      (hF := hF)
      (δ := (1 : Rat)) hδ

/--
Compatible final wrapper: deduce `P ≠ NP` from the active formula-track
final statement plus an explicit bridge from formula separation to
lightweight non-uniform separation.
-/
theorem P_ne_NP_final
  (hProvider : StructuredLocalityProviderPartial)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_final hProvider
  have hNP : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNP ComplexityInterfaces.P_subset_Ppoly_proof

end Magnification
end Pnp3
