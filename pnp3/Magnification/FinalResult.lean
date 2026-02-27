import Magnification.Bridge_to_Magnification_Partial
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-- Global strict NP witness family for fixed-parameter partial-MCSP languages. -/
def StrictGapNPFamily : Prop :=
  ∀ p : GapPartialMCSPParams,
    ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)

/--
Constructive bridge: explicit TM witnesses for each fixed parameter imply the
global strict NP-family hypothesis.
-/
theorem strictGapNPFamily_of_tmWitnesses
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  StrictGapNPFamily := by
  intro p
  exact gapPartialMCSP_in_NP_TM_of_witness p (hW p)

/--
Asymptotic entry hypothesis for the partial formula track:
explicitly provides parameters and lower-bound hypotheses at all
sizes above a threshold `N0`.
-/
structure AsymptoticFormulaTrackHypothesis where
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  pAt_hyp : ∀ n (hn : N0 ≤ n), FormulaLowerBoundHypothesisPartial (pAt n hn) (1 : Rat)

/--
Asymptotic wrapper: if the partial pipeline lower bound is available at all
sufficiently large sizes, we can instantiate the bridge at any such size.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language (hAsym.pAt hAsym.N0 (le_rfl)))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp : FormulaLowerBoundHypothesisPartial (hAsym.pAt hAsym.N0 (le_rfl)) (1 : Rat) :=
    hAsym.pAt_hyp hAsym.N0 (le_rfl)
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := hAsym.pAt hAsym.N0 (le_rfl)) (δ := (1 : Rat)) hHyp

/--
Strict-track final hook: from strict formula separation obtain `P ≠ NP`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_PpolyFormula
  (hStrict : ComplexityInterfaces.NP_strict_not_subset_PpolyFormula)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_NP_strict_not_subset_PpolyFormula
      hStrict hFormulaToPpoly

/--
Strict-track final hook: from strict non-uniform separation obtain `P ≠ NP`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_Ppoly
  (hStrict : ComplexityInterfaces.NP_strict_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_NP_strict_not_subset_Ppoly hStrict

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
Primary final statement (asymptotic entry): from the structured provider and
asymptotic formula-track hypothesis we derive `NP ⊄ PpolyFormula`.

Scope note:
this theorem is a formula-separation endpoint of the AC0-target magnification
route; it is not a standalone global non-uniform separation claim.
-/
theorem NP_not_subset_PpolyFormula_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
    hProvider hAsym (hNPfam (hAsym.pAt hAsym.N0 (le_rfl)))

/--
Primary asymptotic final formula-separation statement.

This default-engine form removes direct provider arguments from the active
final theorem interface.

Scope note:
despite the `PpolyFormula` codomain, this interface is still tied to the AC0
pipeline assumptions (`AsymptoticFormulaTrackHypothesis` + provider packaging).
-/
theorem NP_not_subset_PpolyFormula_final
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from an explicit formula-certificate package.
-/
theorem NP_not_subset_PpolyFormula_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Constructive final formula-separation endpoint from an explicit multi-switching
support-bounds contract.
-/
theorem NP_not_subset_PpolyFormula_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_multiswitching_contract hMS)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Canonical constructive final formula-separation route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem NP_not_subset_PpolyFormula_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_of_multiswitching_contract
      (hMS := hMS) (hAsym := hAsym) (hNPfam := hNPfam)

/--
Constructive final formula-separation route from support-based bounds.
-/
theorem NP_not_subset_PpolyFormula_final_of_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_of_multiswitching_contract
      (hMS := multiswitching_contract_of_formula_support_bounds hBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Constructive final formula-separation route from default support-bounds
availability (`Nonempty` wrapper).
-/
theorem NP_not_subset_PpolyFormula_final_of_default_supportBounds
  (hDefaultBounds : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_of_supportBounds
      (hBounds := defaultFormulaSupportRestrictionBoundsPartial hDefaultBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Compatible final wrapper: deduce `P ≠ NP` from the active formula-track
final statement plus an explicit bridge from formula separation to
lightweight non-uniform separation.

Scope note:
this is a conditional wrapper over the AC0-side formula-separation route; it is
not an unconditional in-repo `P ≠ NP` theorem.
-/
theorem P_ne_NP_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_final_with_provider hProvider hAsym hNPfam
  have hNP : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNP ComplexityInterfaces.P_subset_Ppoly_proof

/--
Active conditional final `P ≠ NP` wrapper.

This default-engine form removes direct provider arguments from the interface,
but still depends on the explicit bridge `hFormulaToPpoly`.

Scope note:
the route is AC0-centric up to `NP_not_subset_PpolyFormula`; the last step to
`NP_not_subset_Ppoly` is externalized by design.
-/
theorem P_ne_NP_final
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from an explicit formula-certificate
package.
-/
theorem P_ne_NP_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Constructive final `P ≠ NP` wrapper from an explicit multi-switching
support-bounds contract.
-/
theorem P_ne_NP_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_multiswitching_contract hMS)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Canonical constructive final `P ≠ NP` route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem P_ne_NP_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Constructive final `P ≠ NP` route from support-based bounds.
-/
theorem P_ne_NP_final_of_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hMS := multiswitching_contract_of_formula_support_bounds hBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Constructive final `P ≠ NP` route from default support-bounds availability
(`Nonempty` wrapper).
-/
theorem P_ne_NP_final_of_default_supportBounds
  (hDefaultBounds : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_supportBounds
      (hBounds := defaultFormulaSupportRestrictionBoundsPartial hDefaultBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

end Magnification
end Pnp3
