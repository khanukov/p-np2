import Magnification.Bridge_to_Magnification_Partial
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces
import Complexity.PsubsetPpolyDAG_Internal
import Complexity.Simulation.Circuit_Compiler

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
Explicit assumptions package for the switching/shrinkage side:
it provides the structured locality provider consumed by the bridge.
-/
structure SwitchingAssumptions : Type where
  provider : StructuredLocalityProviderPartial

/--
Explicit assumptions package for the anti-checker side of the final route.
-/
structure AntiCheckerAssumptions : Type where
  asymptotic : AsymptoticFormulaTrackHypothesis
  strictNPFamily : StrictGapNPFamily

/--
Top-level explicit assumptions package for the magnification final statements.

This keeps imported assumptions grouped and auditable at theorem boundaries.
-/
structure MagnificationAssumptions : Type where
  switching : SwitchingAssumptions
  antiChecker : AntiCheckerAssumptions

/-- Build switching assumptions from an explicit provider. -/
def switchingAssumptions_of_provider
    (hProvider : StructuredLocalityProviderPartial) :
    SwitchingAssumptions := ⟨hProvider⟩

/-- Build switching assumptions from a formula-certificate provider. -/
def switchingAssumptions_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial) :
    SwitchingAssumptions :=
  switchingAssumptions_of_provider
    (structuredLocalityProviderPartial_of_formulaCertificate hCert)

/-- Build switching assumptions from an explicit multi-switching contract. -/
def switchingAssumptions_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    SwitchingAssumptions :=
  switchingAssumptions_of_provider
    (structuredLocalityProviderPartial_of_multiswitching_contract hMS)

/-- Build anti-checker assumptions from explicit asymptotic and NP-family data. -/
def antiCheckerAssumptions_mk
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    AntiCheckerAssumptions :=
  ⟨hAsym, hNPfam⟩

/--
Build anti-checker assumptions from explicit asymptotic data and
TM witnesses for each fixed-parameter gap-language instance.
-/
def antiCheckerAssumptions_of_tmWitnesses
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
    AntiCheckerAssumptions :=
  antiCheckerAssumptions_mk hAsym (strictGapNPFamily_of_tmWitnesses hW)

/-- Merge switching and anti-checker packages into magnification assumptions. -/
def magnificationAssumptions_mk
    (hSwitch : SwitchingAssumptions)
    (hAnti : AntiCheckerAssumptions) :
    MagnificationAssumptions :=
  ⟨hSwitch, hAnti⟩

/-- Build magnification assumptions from a formula-certificate provider package. -/
def magnificationAssumptions_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_formulaCertificate hCert)
    (antiCheckerAssumptions_mk hAsym hNPfam)

/-- Build magnification assumptions from an explicit multi-switching contract. -/
def magnificationAssumptions_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_multiswitching_contract hMS)
    (antiCheckerAssumptions_mk hAsym hNPfam)

/--
Build magnification assumptions from an explicit multi-switching contract plus
TM witnesses for each fixed-parameter gap-language instance.
-/
def magnificationAssumptions_of_tmWitnesses
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_multiswitching_contract hMS)
    (antiCheckerAssumptions_of_tmWitnesses hAsym hW)

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

This is the active audit-facing entrypoint: all external assumptions are passed
explicitly via `MagnificationAssumptions`.
-/
theorem NP_not_subset_PpolyFormula_final
  (hMag : MagnificationAssumptions) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := hMag.switching.provider)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPfam := hMag.antiChecker.strictNPFamily)

/--
Certificate-first provider wiring from an explicit formula-certificate package.
-/
theorem NP_not_subset_PpolyFormula_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPfam)

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
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPfam)

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
Constructive final formula-separation route from explicit TM witnesses
for each fixed-parameter gap-language instance.

This wrapper internalizes the conversion
`(∀ p, GapPartialMCSP_TMWitness p) → StrictGapNPFamily` via
`strictGapNPFamily_of_tmWitnesses`.
-/
theorem NP_not_subset_PpolyFormula_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hW)

/--
Primary final statement on the nontrivial non-uniform class `PpolyReal`.

Unlike `...PpolyFormula...` wrappers, this endpoint does not require any
formula-to-lightweight-`P/poly` bridge assumption.
-/
theorem NP_not_subset_PpolyReal_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hHyp : FormulaLowerBoundHypothesisPartial (hAsym.pAt hAsym.N0 (le_rfl)) (1 : Rat) :=
    hAsym.pAt_hyp hAsym.N0 (le_rfl)
  exact
    NP_not_subset_PpolyReal_from_partial_formulas
      (hProvider := hProvider)
      (p := hAsym.pAt hAsym.N0 (le_rfl))
      (δ := (1 : Rat))
      hHyp
      (hNPfam (hAsym.pAt hAsym.N0 (le_rfl)))

/--
Primary asymptotic final `PpolyReal`-separation statement.
-/
theorem NP_not_subset_PpolyReal_final
  (hMag : MagnificationAssumptions) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := hMag.switching.provider)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPfam := hMag.antiChecker.strictNPFamily)

/--
Certificate-first provider wiring for final `PpolyReal` separation.
-/
theorem NP_not_subset_PpolyReal_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPfam)

/--
Constructive final `PpolyReal`-separation endpoint from an explicit
multi-switching support-bounds contract.
-/
theorem NP_not_subset_PpolyReal_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPfam)

/--
Canonical constructive final `PpolyReal`-separation route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem NP_not_subset_PpolyReal_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_of_multiswitching_contract
      (hMS := hMS) (hAsym := hAsym) (hNPfam := hNPfam)

/--
Constructive final `PpolyReal`-separation route from explicit TM witnesses.
-/
theorem NP_not_subset_PpolyReal_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hW)

/--
Compatible DAG-track final wrapper.

This route targets the canonical non-uniform class (`PpolyDAG`) and therefore
uses explicit assumptions:
1) `NP ⊄ PpolyDAG`
2) `P ⊆ PpolyDAG`.
-/
theorem P_ne_NP_final_with_provider
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts :
    Complexity.Simulation.PsubsetPpolyInternalContractsIteratedCanonical) :
  ComplexityInterfaces.P_ne_NP := by
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_of_iteratedCanonicalContracts
      hPpolyContracts
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Active conditional final `P ≠ NP` wrapper.

This is the audit-facing endpoint:
`MagnificationAssumptions` carries the imported AC0-side assumptions explicitly,
while the DAG-side separation assumption remains a separate argument.
-/
theorem P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  -- Keep AC0-side imports explicit at the final theorem boundary even though
  -- the current DAG endpoint consumes only `hNPDag` on the separation side.
  let _ := hMag
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_internal
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Certificate-first final `P ≠ NP` wiring from an explicit formula-certificate
package.
-/
theorem P_ne_NP_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPfam)
      hNPDag

/--
Constructive final `P ≠ NP` wrapper from an explicit multi-switching
support-bounds contract.
-/
theorem P_ne_NP_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPfam)
      hNPDag

/--
Canonical constructive final `P ≠ NP` route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem P_ne_NP_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      (hNPDag := hNPDag)

/--
Constructive final `P ≠ NP` route from explicit TM witnesses and
an explicit real-track non-uniform inclusion assumption.

This internalizes strictness of the gap language family using
`strictGapNPFamily_of_tmWitnesses`.
-/
theorem P_ne_NP_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hW)
      hNPDag

end Magnification
end Pnp3
