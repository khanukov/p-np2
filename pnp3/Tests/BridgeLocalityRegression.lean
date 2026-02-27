import Magnification.Bridge_to_Magnification_Partial
import Magnification.FinalResult
import Magnification.LocalityLift_Partial
import ThirdPartyFacts.PpolyFormula
import ThirdPartyFacts.PartialLocalityLift

namespace Pnp3.Tests

open Pnp3
open Pnp3.Models
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification
open Pnp3.ThirdPartyFacts

/-!
Regression checks for I-1 / I-3 readiness.

These theorems are compile-time checks only:
1) the localized `PpolyReal -> PpolyFormula` bridge is available internally
   via the trivial formulaizer route;
2) certificate-auto locality lift typechecks without a manually passed
   `hCardHalf` argument.
-/

theorem i1_trivial_realization_available
    (p : GapPartialMCSPParams) :
    GapPartialMCSPFormulaRealization p :=
  gapPartialMCSP_realization_trivial p

theorem i1_trivial_ppolyreal_route_no_manual_embed
    (hProvider : StructuredLocalityProviderPartial_semantic)
    {p : GapPartialMCSPParams} {δ : Rat}
    (hNPstrict : NP_strict (gapPartialMCSP_Language p))
    (hδ : (0 : Rat) < δ) :
    NP_not_subset_PpolyReal := by
  simpa using
    NP_not_subset_PpolyReal_from_partial_formulas_semantic_auto
      (hProvider := hProvider) (p := p) (δ := δ) hδ hNPstrict

theorem i3_certificate_auto_no_manual_hCardHalf
    {p : GapPartialMCSPParams}
    (solver : SmallGeneralCircuitSolver_Partial p)
    [hCert :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
        (p := toFactsParamsPartial p)
        (toFactsGeneralSolverPartial solver)
        (solverDecideFacts (p := p) solver)] :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  simpa using
    (ThirdPartyFacts.locality_lift_partial_of_certificate_auto
      (p := p) solver)

theorem i4_final_wiring_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_of_formulaCertificate
      (hCert := hCert) (hAsym := hAsym) (hNPfam := hNPfam))

theorem i4_final_wiring_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_of_multiswitching_contract
      (hMS := hMS) (hAsym := hAsym) (hNPfam := hNPfam))

theorem i4_final_wiring_constructive_alias
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_constructive
      (hMS := hMS) (hAsym := hAsym) (hNPfam := hNPfam))

theorem i4_final_wiring_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_of_supportBounds
      (hBounds := hBounds) (hAsym := hAsym) (hNPfam := hNPfam))

theorem i4_final_wiring_of_default_supportBounds
    (hDefaultBounds : hasDefaultFormulaSupportRestrictionBoundsPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_of_default_supportBounds
      (hDefaultBounds := hDefaultBounds) (hAsym := hAsym) (hNPfam := hNPfam))

end Pnp3.Tests
