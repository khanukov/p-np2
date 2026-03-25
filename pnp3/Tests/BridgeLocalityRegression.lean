import Magnification.Bridge_to_Magnification_Partial
import Magnification.FinalResult
import Magnification.LocalityLift_Partial
import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.SingletonDensityContradiction
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
    (hNPbridge : AsymptoticNPPullback hAsym)
    (n : Nat) (hn : hAsym.N0 ≤ n) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn))

theorem i4_final_wiring_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPbridge : AsymptoticNPPullback hAsym)
    (n : Nat) (hn : hAsym.N0 ≤ n) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_with_supportBounds
      (hBounds := hBounds)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn))

theorem i4_gap_targeted_payload_contradiction_of_formulaCertificate
    {p : GapPartialMCSPParams}
    (pkg : Pnp3.LowerBounds.AbstractGapTargetedSingletonDensityPayload p)
    (hCert : FormulaCertificateProviderPartial)
    (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    False := by
  exact Pnp3.LowerBounds.false_of_abstractGapTargetedPayload_of_formulaCertificate
    pkg hCert hFormula

theorem i4_gap_targeted_payload_contradiction_of_supportBounds
    {p : GapPartialMCSPParams}
    (pkg : Pnp3.LowerBounds.AbstractGapTargetedSingletonDensityPayload p)
    (hBounds : FormulaSupportRestrictionBoundsPartial)
    (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    False := by
  exact Pnp3.LowerBounds.false_of_abstractGapTargetedPayload_of_supportBounds
    pkg hBounds hFormula

theorem i4_dag_candidateRestriction_alive_small_of_freePositions_small
    {p : GapPartialMCSPParams}
    (hDag : PpolyDAG (gapPartialMCSP_Language p))
    (β : Core.Subcube (Pnp3.LowerBounds.dagCanonicalPayload hDag).n)
    (hSmall :
      ((⟨β⟩ : Core.Restriction (Pnp3.LowerBounds.dagCanonicalPayload hDag).n).freePositions.card) ≤
        Models.Partial.tableLen p.n / 2) :
    (Pnp3.LowerBounds.dagCandidateRestrictionOfSubcube hDag β).alive.card ≤
      Models.Partial.tableLen p.n / 2 := by
  exact
    Pnp3.LowerBounds.dagCandidateRestrictionOfSubcube_alive_small_of_freePositions_small
      hDag β hSmall

theorem i4_dag_candidateRestriction_of_scenarioWitness_forces_yes
    {p : GapPartialMCSPParams}
    (hDag : PpolyDAG (gapPartialMCSP_Language p))
    {β : Core.Subcube (Pnp3.LowerBounds.dagCanonicalPayload hDag).n}
    (hβ : β ∈ Pnp3.LowerBounds.dagScenarioWitness hDag)
    (x : Core.BitVec (Models.partialInputLen p)) :
    gapPartialMCSP_Language p (Models.partialInputLen p)
      ((Pnp3.LowerBounds.dagCandidateRestrictionOfSubcube hDag β).apply x) = true := by
  exact
    Pnp3.LowerBounds.dagCandidateRestrictionOfScenarioWitness_forces_yes
      hDag hβ x

theorem i4_dagScenarioWitness_freePositions_card_eq_zero
    {p : GapPartialMCSPParams}
    (hDag : PpolyDAG (gapPartialMCSP_Language p))
    {β : Core.Subcube (Pnp3.LowerBounds.dagCanonicalPayload hDag).n}
    (hβ : β ∈ Pnp3.LowerBounds.dagScenarioWitness hDag) :
    ((⟨β⟩ : Core.Restriction (Pnp3.LowerBounds.dagCanonicalPayload hDag).n).freePositions.card) = 0 := by
  exact Pnp3.LowerBounds.dagScenarioWitness_freePositions_card_eq_zero hDag hβ

theorem i4_dagCandidateRestriction_of_scenarioWitness_alive_card_eq_zero
    {p : GapPartialMCSPParams}
    (hDag : PpolyDAG (gapPartialMCSP_Language p))
    {β : Core.Subcube (Pnp3.LowerBounds.dagCanonicalPayload hDag).n}
    (hβ : β ∈ Pnp3.LowerBounds.dagScenarioWitness hDag) :
    (Pnp3.LowerBounds.dagCandidateRestrictionOfSubcube hDag β).alive.card = 0 := by
  exact Pnp3.LowerBounds.dagCandidateRestrictionOfScenarioWitness_alive_card_eq_zero hDag hβ

theorem i4_current_singleton_preSingleton_selector_witness
    {p : GapPartialMCSPParams}
    (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty
      (Pnp3.Magnification.AC0LocalityBridge.CurrentSingletonPreSingletonSelectorPackage p) := by
  exact
    ⟨Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package
      hFormula⟩

theorem i4_current_singleton_preSingleton_selector_package_collapses_to_semanticSingletonWitness
    {p : GapPartialMCSPParams}
    (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    (Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package hFormula).Rf =
      Pnp3.Magnification.AC0LocalityBridge.semanticSingletonWitness
        (Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package
          hFormula).f := by
  exact
    Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package_Rf_eq_semanticSingletonWitness
      hFormula

theorem i4_current_singleton_preSingleton_selector_members_have_zero_free_positions
    {p : GapPartialMCSPParams}
    (hFormula : PpolyFormula (gapPartialMCSP_Language p))
    {β : Core.Subcube (Models.partialInputLen p)}
    (hβ :
      β ∈ (Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_package
        hFormula).Rf) :
    ((⟨β⟩ : Core.Restriction (Models.partialInputLen p)).freePositions.card) = 0 := by
  exact
    Pnp3.Magnification.AC0LocalityBridge.current_singleton_preSingleton_selector_freePositions_card_eq_zero
      hFormula hβ

theorem i4_np_not_subset_ppolyDAG_of_dag_stableRestrictionPayload
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hStable :
      ∀ _ : PpolyDAG (gapPartialMCSP_Language p),
        Pnp3.LowerBounds.AbstractGapStableRestrictionPayload p)
    (hBase :
      ∀ hDag : PpolyDAG (gapPartialMCSP_Language p),
        (hStable hDag).base = Pnp3.LowerBounds.dagCanonicalPayload hDag) :
    NP_not_subset_PpolyDAG := by
  exact
    Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestrictionPayload_TM
      W hStable hBase

theorem i4_np_not_subset_ppolyDAG_of_dag_stableRestriction
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hStable : Pnp3.LowerBounds.dag_stableRestriction_producer p) :
    NP_not_subset_PpolyDAG := by
  exact Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM
    W hStable

theorem i4_np_not_subset_ppolyDAG_of_certificateProvider
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hCert : Pnp3.LowerBounds.dagStableRestrictionCertificateProvider p) :
    NP_not_subset_PpolyDAG := by
  exact Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_certificateProvider_TM W hCert

theorem i4_np_not_subset_ppolyDAG_of_invariantProvider
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hInv : Pnp3.LowerBounds.dagStableRestrictionInvariantProvider p) :
    NP_not_subset_PpolyDAG := by
  exact Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_invariantProvider_TM W hInv

theorem i4_np_not_subset_ppolyDAG_final_of_invariantProvider
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hInv : Pnp3.LowerBounds.dagStableRestrictionInvariantProvider p) :
    NP_not_subset_PpolyDAG := by
  exact Pnp3.Magnification.NP_not_subset_PpolyDAG_final_of_invariantProvider_TM W hInv

theorem i4_p_ne_np_final_of_invariantProvider
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hInv : Pnp3.LowerBounds.dagStableRestrictionInvariantProvider p) :
    P_ne_NP := by
  exact Pnp3.Magnification.P_ne_NP_final_of_invariantProvider_TM W hInv

theorem i4_np_not_subset_ppolyDAG_of_formulaCertificate_and_dagToFormula
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hCert : Pnp3.Magnification.FormulaCertificateProviderPartial)
    (hDagToFormula :
      PpolyDAG (gapPartialMCSP_Language p) →
        PpolyFormula (gapPartialMCSP_Language p)) :
    NP_not_subset_PpolyDAG := by
  exact
    Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM
      W
      (Pnp3.LowerBounds.dag_stableRestriction_producer_of_formulaCertificate
        hCert hDagToFormula)

theorem i4_np_not_subset_ppolyDAG_of_supportBounds_and_dagToFormula
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hBounds : Pnp3.Magnification.FormulaSupportRestrictionBoundsPartial)
    (hDagToFormula :
      PpolyDAG (gapPartialMCSP_Language p) →
        PpolyFormula (gapPartialMCSP_Language p)) :
    NP_not_subset_PpolyDAG := by
  exact
    Pnp3.LowerBounds.NP_not_subset_PpolyDAG_of_supportBounds_and_dagToFormula_TM
      W hBounds hDagToFormula

theorem i4_p_ne_np_final_of_supportBounds_and_dagToFormula
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hBounds : Pnp3.Magnification.FormulaSupportRestrictionBoundsPartial)
    (hDagToFormula :
      PpolyDAG (gapPartialMCSP_Language p) →
        PpolyFormula (gapPartialMCSP_Language p)) :
    P_ne_NP := by
  exact
    Pnp3.Magnification.P_ne_NP_final_of_supportBounds_and_dagToFormula_TM
      W hBounds hDagToFormula

theorem i4_p_ne_np_final_of_dag_stableRestrictionPayload
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hStable :
      ∀ _ : PpolyDAG (gapPartialMCSP_Language p),
        Pnp3.LowerBounds.AbstractGapStableRestrictionPayload p)
    (hBase :
      ∀ hDag : PpolyDAG (gapPartialMCSP_Language p),
        (hStable hDag).base = Pnp3.LowerBounds.dagCanonicalPayload hDag) :
    P_ne_NP := by
  exact
    Pnp3.Magnification.P_ne_NP_final_of_dag_stableRestrictionPayload_TM
      W hStable hBase

theorem i4_p_ne_np_final_of_dag_stableRestriction
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hStable : Pnp3.LowerBounds.dag_stableRestriction_producer p) :
    P_ne_NP := by
  exact Pnp3.Magnification.P_ne_NP_final_of_dag_stableRestriction_TM
    W hStable

theorem i4_final_wiring_of_multiswitching
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPbridge : AsymptoticNPPullback hAsym)
    (n : Nat) (hn : hAsym.N0 ≤ n) :
    NP_not_subset_PpolyFormula := by
  simpa using
    (NP_not_subset_PpolyFormula_final_with_multiswitching
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn))

end Pnp3.Tests
