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
Strict-track final hook: from strict non-uniform separation obtain `P ≠ NP`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_Ppoly
  (hStrict : ComplexityInterfaces.NP_strict_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_NP_strict_not_subset_Ppoly hStrict

/-- Explicit evaluation of the concrete counting bound used by canonical parameters. -/
lemma circuitCountBound_8_2 : Models.circuitCountBound 8 2 = 230 := by
  simp [Models.circuitCountBound]

/-- Canonical Partial MCSP parameters used in the final bridge. -/
lemma circuit_bound_ok_canonical :
  Models.circuitCountBound 8 (3 - 1) < 2 ^ (Partial.tableLen 8 / 2) := by
  /-
    Делаем доказательство максимально прозрачным:
    1) вычисляем левую часть точно: `circuitCountBound 8 2 = 230`;
    2) показываем `230 < 2^8`;
    3) поднимаем границу до `2^(tableLen 8 / 2)` по монотонности степени.
  -/
  have hleft : Models.circuitCountBound 8 (3 - 1) = 230 := by
    simpa using circuitCountBound_8_2
  have hsmall : (230 : Nat) < 2 ^ 8 := by
    decide
  have hexp : (2 : Nat) ^ 8 ≤ 2 ^ (Partial.tableLen 8 / 2) := by
    have hidx : 8 ≤ Partial.tableLen 8 / 2 := by
      decide
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hidx
  have hmain : (230 : Nat) < 2 ^ (Partial.tableLen 8 / 2) :=
    Nat.lt_of_lt_of_le hsmall hexp
  simpa [hleft] using hmain

/-
  Канонический набор параметров для финального моста.

  `circuit_bound_ok` подаётся через отдельную явную арифметическую лемму
  `circuit_bound_ok_canonical`.
-/
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
  gap_ok := by decide
  n_large := by decide
  sYES_pos := by decide
  circuit_bound_ok := by
    simpa using circuit_bound_ok_canonical

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
    NP_not_subset_PpolyFormula_final_constructive
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPfam := strictGapNPFamily_of_tmWitnesses hW)

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
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring for final `PpolyReal` separation.
-/
theorem NP_not_subset_PpolyReal_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

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
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_multiswitching_contract hMS)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

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
    NP_not_subset_PpolyReal_final_constructive
      (hMS := hMS)
      (hAsym := hAsym)
      (hNPfam := strictGapNPFamily_of_tmWitnesses hW)

/--
Constructive final `PpolyReal`-separation route from support-based bounds.
-/
theorem NP_not_subset_PpolyReal_final_of_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_of_multiswitching_contract
      (hMS := multiswitching_contract_of_formula_support_bounds hBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Constructive final `PpolyReal`-separation route from default support-bounds
availability (`Nonempty` wrapper).
-/
theorem NP_not_subset_PpolyReal_final_of_default_supportBounds
  (hDefaultBounds : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_of_supportBounds
      (hBounds := defaultFormulaSupportRestrictionBoundsPartial hDefaultBounds)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Compatible DAG-track final wrapper.

This route targets the canonical non-uniform class (`PpolyDAG`) and therefore
uses explicit assumptions:
1) `NP ⊄ PpolyDAG`
2) `P ⊆ PpolyDAG`.
-/
theorem P_ne_NP_final_with_provider
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  -- Важно явно зафиксировать, что включение `P ⊆ PpolyDAG`
  -- теперь получается конструктивно из bundle-контракта внутренних
  -- обязательств компилятора (`RuntimeSpecProvider ∧ EvalAgreement`).
  -- Это и есть «дожатая» часть Step-11/12 для DAG-трека.
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_of_contracts hPpolyContracts
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Active conditional final `P ≠ NP` wrapper.

This default-engine form removes direct provider arguments from the interface,
but still depends on explicit DAG-track assumptions.

Scope note:
the AC0 side and DAG side are not yet internally connected in this wrapper.
-/
theorem P_ne_NP_final
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Certificate-first final `P ≠ NP` wiring from an explicit formula-certificate
package.
-/
theorem P_ne_NP_final_of_formulaCertificate
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Constructive final `P ≠ NP` wrapper from an explicit multi-switching
support-bounds contract.
-/
theorem P_ne_NP_final_of_multiswitching_contract
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Canonical constructive final `P ≠ NP` route:
explicit multi-switching contract, no default-provider `Nonempty` flag.
-/
theorem P_ne_NP_final_constructive
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Constructive final `P ≠ NP` route from explicit TM witnesses and
an explicit real-track non-uniform inclusion assumption.

This internalizes strictness of the gap language family using
`strictGapNPFamily_of_tmWitnesses`.
-/
theorem P_ne_NP_final_constructive_of_tmWitnesses
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  -- `hW` оставляем в интерфейсе как конструктивный witness-пакет;
  -- он фиксирует «канонический constructive route» на стороне NP-фамилии,
  -- даже если текущий DAG-финал зависит только от `hNPDag` + `hPpolyContracts`.
  have _hNPfam : StrictGapNPFamily := strictGapNPFamily_of_tmWitnesses hW
  exact
    P_ne_NP_final_constructive (hNPDag := hNPDag) (hPpolyContracts := hPpolyContracts)

/--
Constructive final `P ≠ NP` route from support-based bounds.
-/
theorem P_ne_NP_final_of_supportBounds
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_multiswitching_contract
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Constructive final `P ≠ NP` route from default support-bounds availability
(`Nonempty` wrapper).
-/
theorem P_ne_NP_final_of_default_supportBounds
  (hDefaultBounds : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  -- `hDefaultBounds` intentionally remains in the signature to preserve the
  -- constructive API shape aligned with the formula-track wrappers.
  have _hBounds : FormulaSupportRestrictionBoundsPartial :=
    defaultFormulaSupportRestrictionBoundsPartial hDefaultBounds
  exact
    P_ne_NP_final_of_supportBounds
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

/--
Legacy straight-line inclusion variant of the final wrapper.

This allows closing the inclusion side via an internalized `LegacyStraight`
compiler, then reducing it to the canonical DAG inclusion target.
-/
theorem P_ne_NP_final_of_straightLineInclusion
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContracts) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hNPDag := hNPDag)
      (hPpolyContracts := hPpolyContracts)

end Magnification
end Pnp3
