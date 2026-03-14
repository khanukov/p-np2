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

/--
Asymptotic entry hypothesis for the partial formula track:
explicitly provides parameters and lower-bound hypotheses at all
sizes above a threshold `N0`.
-/
structure AsymptoticFormulaTrackHypothesis where
  spec : GapPartialMCSPAsymptoticSpec
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  pAt_hyp : ∀ n (hn : N0 ≤ n), FormulaLowerBoundHypothesisPartial (pAt n hn) (1 : Rat)

/--
Asymptotic NP bridge package:
1) strict NP witness for the global asymptotic language;
2) fixed-parameter strict NP witness stream along `pAt`.
-/
structure AsymptoticNPPullback (hAsym : AsymptoticFormulaTrackHypothesis) : Type where
  strictAsymptotic :
    ComplexityInterfaces.NP_strict
      (gapPartialMCSP_AsymptoticLanguage hAsym.spec)
  strictFixed :
    ∀ n (hn : hAsym.N0 ≤ n),
      ComplexityInterfaces.NP_strict
        (gapPartialMCSP_Language (hAsym.pAt n hn))

/-- Concrete TM-witness stream for fixed-parameter languages along `pAt`. -/
def GapPartialMCSPFixedTMWitnessFamily
    (hAsym : AsymptoticFormulaTrackHypothesis) : Type 1 :=
  ∀ n (hn : hAsym.N0 ≤ n), GapPartialMCSP_TMWitness (hAsym.pAt n hn)

/-- Build an asymptotic NP bridge from a strict asymptotic TM witness. -/
def asymptoticNPPullback_of_tmWitness
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
    (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym) :
    AsymptoticNPPullback hAsym :=
  { strictAsymptotic := gapPartialMCSP_Asymptotic_in_NP_TM_of_witness hAsym.spec hWAsym
    strictFixed := fun n hn =>
      gapPartialMCSP_in_NP_TM_of_witness (hAsym.pAt n hn) (hWFixed n hn) }

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
  npBridge : AsymptoticNPPullback asymptotic

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

/-- Build anti-checker assumptions from explicit asymptotic and NP-bridge data. -/
def antiCheckerAssumptions_mk
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPbridge : AsymptoticNPPullback hAsym) :
    AntiCheckerAssumptions :=
  ⟨hAsym, hNPbridge⟩

/--
Build anti-checker assumptions from explicit asymptotic data and
a concrete fixed-parameter TM-witness stream along `pAt`.
-/
def antiCheckerAssumptions_of_tmWitnesses
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
    (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym) :
    AntiCheckerAssumptions :=
  antiCheckerAssumptions_mk hAsym
    (asymptoticNPPullback_of_tmWitness hAsym hWAsym hWFixed)

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
    (hNPbridge : AsymptoticNPPullback hAsym) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_formulaCertificate hCert)
    (antiCheckerAssumptions_mk hAsym hNPbridge)

/-- Build magnification assumptions from an explicit multi-switching contract. -/
def magnificationAssumptions_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPbridge : AsymptoticNPPullback hAsym) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_multiswitching_contract hMS)
    (antiCheckerAssumptions_mk hAsym hNPbridge)

/--
Build magnification assumptions from an explicit multi-switching contract plus
an explicit asymptotic TM witness plus a concrete fixed-parameter
TM-witness stream along `pAt`.
-/
def magnificationAssumptions_of_tmWitnesses
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
    (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym) :
    MagnificationAssumptions :=
  magnificationAssumptions_mk
    (switchingAssumptions_of_multiswitching_contract hMS)
    (antiCheckerAssumptions_of_tmWitnesses hAsym hWAsym hWFixed)

/--
Asymptotic wrapper: if the partial pipeline lower bound is available at all
sufficiently large sizes, we can instantiate the bridge at any such size.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language (hAsym.pAt n hn))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp : FormulaLowerBoundHypothesisPartial (hAsym.pAt n hn) (1 : Rat) :=
    hAsym.pAt_hyp n hn
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := hAsym.pAt n hn) (δ := (1 : Rat)) hHyp

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
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hNPstrict : ComplexityInterfaces.NP_strict
      (gapPartialMCSP_Language (hAsym.pAt n hn)) :=
    hNPbridge.strictFixed n hn
  exact NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
    hProvider hAsym n hn hNPstrict

/--
Primary asymptotic final formula-separation statement.

This is the active audit-facing entrypoint: all external assumptions are passed
explicitly via `MagnificationAssumptions`.
-/
theorem NP_not_subset_PpolyFormula_final
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := hMag.switching.provider)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/--
Certificate-first provider wiring from an explicit formula-certificate package.
-/
theorem NP_not_subset_PpolyFormula_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPbridge)
      (n := n)
      (hn := hn)

/--
Constructive final formula-separation endpoint from an explicit multi-switching
support-bounds contract.
-/
theorem NP_not_subset_PpolyFormula_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPbridge)
      (n := n)
      (hn := hn)

/--
Canonical constructive final formula-separation route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem NP_not_subset_PpolyFormula_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_of_multiswitching_contract
      (hMS := hMS) (hAsym := hAsym) (hNPbridge := hNPbridge) (n := n) (hn := hn)

/--
Constructive final formula-separation route from an explicit asymptotic TM
witness plus a concrete fixed-parameter TM-witness stream along `pAt`.
-/
theorem NP_not_subset_PpolyFormula_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
  (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hWAsym hWFixed)
      (n := n)
      (hn := hn)

/--
Primary final statement on the nontrivial non-uniform class `PpolyReal`.

Unlike `...PpolyFormula...` wrappers, this endpoint does not require any
formula-to-lightweight-`P/poly` bridge assumption.
-/
theorem NP_not_subset_PpolyReal_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  have hHyp : FormulaLowerBoundHypothesisPartial (hAsym.pAt n hn) (1 : Rat) :=
    hAsym.pAt_hyp n hn
  have hNPstrict : ComplexityInterfaces.NP_strict
      (gapPartialMCSP_Language (hAsym.pAt n hn)) :=
    hNPbridge.strictFixed n hn
  exact
    NP_not_subset_PpolyReal_from_partial_formulas
      (hProvider := hProvider)
      (p := hAsym.pAt n hn)
      (δ := (1 : Rat))
      hHyp
      hNPstrict

/--
Primary asymptotic final `PpolyReal`-separation statement.
-/
theorem NP_not_subset_PpolyReal_final
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := hMag.switching.provider)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/--
Certificate-first provider wiring for final `PpolyReal` separation.
-/
theorem NP_not_subset_PpolyReal_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPbridge)
      (n := n)
      (hn := hn)

/--
Constructive final `PpolyReal`-separation endpoint from an explicit
multi-switching support-bounds contract.
-/
theorem NP_not_subset_PpolyReal_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPbridge)
      (n := n)
      (hn := hn)

/--
Canonical constructive final `PpolyReal`-separation route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem NP_not_subset_PpolyReal_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_of_multiswitching_contract
      (hMS := hMS) (hAsym := hAsym) (hNPbridge := hNPbridge) (n := n) (hn := hn)

/--
Constructive final `PpolyReal`-separation route from an explicit asymptotic TM
witness plus a concrete fixed-parameter TM-witness stream along `pAt`.
-/
theorem NP_not_subset_PpolyReal_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
  (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hWAsym hWFixed)
      (n := n)
      (hn := hn)

/--
Compatible DAG-track final wrapper.

This route targets the canonical non-uniform class (`PpolyDAG`) and therefore
uses explicit assumptions:
1) `NP ⊄ PpolyDAG`
2) linear-route internal `P ⊆ PpolyDAG` closure contracts.
-/
theorem P_ne_NP_final_with_provider
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts :
    Complexity.Simulation.PsubsetPpolyCompiledRuntimeLinearOutputContracts) :
  ComplexityInterfaces.P_ne_NP := by
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts
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
  (hNPbridge : AsymptoticNPPullback hAsym)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_formulaCertificate hCert hAsym hNPbridge)
      hNPDag

/--
Constructive final `P ≠ NP` wrapper from an explicit multi-switching
support-bounds contract.
-/
theorem P_ne_NP_final_of_multiswitching_contract
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_multiswitching_contract hMS hAsym hNPbridge)
      hNPDag

/--
Canonical constructive final `P ≠ NP` route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem P_ne_NP_final_constructive
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (hNPDag := hNPDag)

/--
Constructive final `P ≠ NP` route from an explicit asymptotic TM witness and
a concrete fixed-parameter TM-witness stream along `pAt`.
-/
theorem P_ne_NP_final_constructive_of_tmWitnesses
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hWAsym : GapPartialMCSP_Asymptotic_TMWitness hAsym.spec)
  (hWFixed : GapPartialMCSPFixedTMWitnessFamily hAsym)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hMag := magnificationAssumptions_of_tmWitnesses hMS hAsym hWAsym hWFixed)
      hNPDag

end Magnification
end Pnp3
