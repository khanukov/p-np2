import Magnification.Bridge_to_Magnification_Partial
import Magnification.AsymptoticFormulaCollapse
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Magnification.PipelineStatements_Partial
import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.RouteBSourceClosure
import LowerBounds.AsymptoticDAGBarrier
import LowerBounds.SingletonDensityContradiction
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
  sliceEq :
    ∀ n (hn : N0 ≤ n),
      ∀ x : Core.BitVec (Models.partialInputLen (pAt n hn)),
        gapPartialMCSP_AsymptoticLanguage spec
            (Models.partialInputLen (pAt n hn)) x =
          gapPartialMCSP_Language (pAt n hn)
            (Models.partialInputLen (pAt n hn)) x

/--
Asymptotic NP bridge package:
strict NP witness for the global asymptotic language.
-/
structure AsymptoticNPPullback (hAsym : AsymptoticFormulaTrackHypothesis) : Type where
  strictAsymptotic :
    ComplexityInterfaces.NP_strict
      (gapPartialMCSP_AsymptoticLanguage hAsym.spec)

/--
Explicit assumptions package for the switching/shrinkage side:
it carries the strengthened A9 multi-switching contract (including semantic
linkage), from which support-bounds and the structured provider are derived
internally.
-/
structure SwitchingAssumptions : Type where
  multiswitching : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract

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

/--
Family-specific entrypoint for the singleton `β`-route decision layer.

This theorem does not prove the comparison inequality on its own. It packages
the exact arithmetic hypothesis currently missing from the generic asymptotic
API and feeds it into the current singleton-source decision theorem on the
chosen fixed slice `pAt n hn`.
-/
theorem empty_witness_admissible_for_asymptotic_slice_of_nat_cmp
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n)
  (hFormula : ComplexityInterfaces.PpolyFormula
    (gapPartialMCSP_Language (hAsym.pAt n hn)))
  (hCmp :
    Models.circuitCountBound (hAsym.pAt n hn).n (hAsym.pAt n hn).sYES *
      3 ^ Models.Partial.tableLen (hAsym.pAt n hn).n *
      (Models.partialInputLen (hAsym.pAt n hn) + 2)
    ≤
      4 ^ Models.Partial.tableLen (hAsym.pAt n hn).n) :
  AC0LocalityBridge.CurrentSingletonRouteWitnessProp hFormula := by
  exact
    AC0LocalityBridge.empty_witness_admissible_for_current_singleton_route_of_nat_cmp
      (p := hAsym.pAt n hn)
      hFormula
      hCmp

/--
Asymptotic formula collapse, routed through a fixed-slice bridge.

This theorem is the active bridge-shaped entrypoint in `codex-refactoring`:
the fixed-slice collapse side is internalized from provider + lower-bound data,
while the asymptotic-to-slice conversion remains an explicit bridge parameter.
-/
theorem asymptotic_formula_collapse
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False := by
  let p : GapPartialMCSPParams := hAsym.pAt n hn
  have hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_semantic
      (p := p) (δ := (1 : Rat)) (hδ := by norm_num)
  have hFixedCollapse :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False :=
    fixed_formula_collapse_of_provider (hProvider := hProvider) (p := p) (δ := (1 : Rat)) hHyp
  exact
    asymptotic_formula_collapse_of_slice_agreement
      (spec := hAsym.spec)
      (p := p)
      hFixedCollapse
      (hAsym.sliceEq n hn)

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
  have hCollapse :
      ComplexityInterfaces.PpolyFormula
        (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False :=
    asymptotic_formula_collapse hProvider hAsym n hn
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse
      (spec := hAsym.spec)
      (hNPstrict := hNPbridge.strictAsymptotic)
      hCollapse

/--
Provider-free wrapper at the formula endpoint boundary:
derive the structured locality provider internally from support-based bounds.
-/
theorem NP_not_subset_PpolyFormula_final_with_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hBounds)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Provider-free wrapper at the formula endpoint boundary:
derive support-bounds and the structured locality provider internally from the
strengthened A9 multi-switching contract.
-/
theorem NP_not_subset_PpolyFormula_final_with_multiswitching
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_supportBounds
      (hBounds := formula_support_bounds_from_multiswitching hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

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
    NP_not_subset_PpolyFormula_final_with_multiswitching
      (hMS := hMag.switching.multiswitching)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/--
Primary final statement on the nontrivial non-uniform class `PpolyReal`.

In the current strict interface this endpoint is a thin corollary of the
formula-separation route, because `PpolyReal` and `PpolyFormula` share the same
concrete witness model.
-/
theorem NP_not_subset_PpolyReal_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    ComplexityInterfaces.NP_not_subset_PpolyReal_of_PpolyFormula
      (NP_not_subset_PpolyFormula_final_with_provider
        (hProvider := hProvider)
        (hAsym := hAsym)
        (hNPbridge := hNPbridge)
        (n := n)
        (hn := hn))

/--
Provider-free wrapper at the `PpolyReal` endpoint boundary:
derive the structured locality provider internally from support-based bounds.
-/
theorem NP_not_subset_PpolyReal_final_with_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hBounds)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Provider-free wrapper at the `PpolyReal` endpoint boundary:
derive support-bounds and the structured locality provider internally from the
strengthened A9 multi-switching contract.
-/
theorem NP_not_subset_PpolyReal_final_with_multiswitching
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_supportBounds
      (hBounds := formula_support_bounds_from_multiswitching hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Primary asymptotic final `PpolyReal`-separation statement.
-/
theorem NP_not_subset_PpolyReal_final
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_multiswitching
      (hMS := hMag.switching.multiswitching)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/-- One-gate constant-false DAG used off the target asymptotic slice. -/
private def constFalseDag (n : Nat) : ComplexityInterfaces.DagCircuit n where
  gates := 1
  gate := fun _ => ComplexityInterfaces.DagGate.const false
  output := ComplexityInterfaces.DagWire.gate ⟨0, by simp⟩

@[simp] private theorem constFalseDag_size {n : Nat} :
    ComplexityInterfaces.DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.size]

@[simp] private theorem constFalseDag_eval {n : Nat}
    (x : ComplexityInterfaces.Bitstring n) :
    ComplexityInterfaces.DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

/-- Monotone padding used to restrict an asymptotic DAG witness to one slice. -/
private theorem dag_poly_bound_lift (n c : Nat) :
    n ^ c + c ≤ n ^ (c + 2) + (c + 2) := by
  by_cases hn : n = 0
  · subst hn
    cases c <;> simp
  · have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpow : n ^ c ≤ n ^ (c + 2) := by
      simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right c 2)
    have hc : c ≤ c + 2 := by omega
    exact Nat.add_le_add hpow hc

/--
Constructive asymptotic-to-fixed bridge from pointwise slice agreement at the
target length `partialInputLen p`.
-/
private theorem ppolyDAG_fixed_of_asymptotic_slice
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hSliceEq :
      ∀ x : Core.BitVec (partialInputLen p),
        gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
          gapPartialMCSP_Language p (partialInputLen p) x) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) →
      ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hAsym
  rcases hAsym with ⟨w, _⟩
  rcases w.polyBound_poly with ⟨c, hc⟩
  refine ⟨{
    polyBound := fun n => n ^ (c + 2) + (c + 2)
    polyBound_poly := ?_
    family := fun m =>
      if hm : m = partialInputLen p then
        w.family m
      else
        constFalseDag m
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · refine ⟨c + 2, ?_⟩
    intro n
    rfl
  · intro m
    by_cases hm : m = partialInputLen p
    · have hTarget : w.polyBound m ≤ m ^ (c + 2) + (c + 2) := by
        exact le_trans (hc m) (dag_poly_bound_lift m c)
      exact by
        simpa [hm] using le_trans (w.family_size_le m) hTarget
    · have hConst :
        ComplexityInterfaces.DagCircuit.size (constFalseDag m) ≤
          m ^ (c + 2) + (c + 2) := by
        rw [constFalseDag_size]
        have hTwo : 2 ≤ c + 2 := by omega
        exact le_trans hTwo (Nat.le_add_left (c + 2) (m ^ (c + 2)))
      simpa [hm] using hConst
  · intro m x
    by_cases hm : m = partialInputLen p
    · cases hm
      have hAsymCorrect :
          ComplexityInterfaces.DagCircuit.eval
              (w.family (partialInputLen p)) x =
            gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x :=
        w.correct (partialInputLen p) x
      have hEq :
          gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
            gapPartialMCSP_Language p (partialInputLen p) x :=
        hSliceEq x
      simpa using Eq.trans hAsymCorrect hEq
    · have hFixedFalse : gapPartialMCSP_Language p m x = false := by
        simp [gapPartialMCSP_Language, hm]
      simp [hm, hFixedFalse]

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

This is the honest DAG-track endpoint:
it uses only DAG-side separation plus the internalized inclusion theorem.

AC0/magnification assumptions live on a separate route
(`NP_not_subset_PpolyFormula_final*` / `NP_not_subset_PpolyReal_final*`)
until an explicit bridge to DAG separation is formalized.
-/
theorem P_ne_NP_final_dag_only
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_internal
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Collapse the asymptotic DAG language once one fixed slice is known to avoid
`PpolyDAG`.

This is the shortest honest integration route from `MagnificationAssumptions`
to DAG separation:
1. choose any concrete asymptotic slice `pAt n hn`,
2. prove fixed-slice collapse there,
3. transport it back to the asymptotic language using slice agreement.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  let p : GapPartialMCSPParams := hMag.antiChecker.asymptotic.pAt n hn
  have hCollapseAsym :
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_AsymptoticLanguage hMag.antiChecker.asymptotic.spec) → False :=
    fun hAsymDag =>
      hCollapseFixed
        (ppolyDAG_fixed_of_asymptotic_slice
          (spec := hMag.antiChecker.asymptotic.spec)
          (p := p)
          (hMag.antiChecker.asymptotic.sliceEq n hn)
          hAsymDag)
  exact
    ⟨gapPartialMCSP_AsymptoticLanguage hMag.antiChecker.asymptotic.spec,
      hMag.antiChecker.npBridge.strictAsymptotic,
      hCollapseAsym⟩

/--
Companion `P ≠ NP` endpoint from the same fixed-slice collapse input.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
      (hMag := hMag) (n := n) (hn := hn) hCollapseFixed)

/--
Asymptotic DAG separation from the fixed-slice stable-restriction producer.

Compared with the older `_TM` wrappers, this route uses the global NP witness
already packaged in `MagnificationAssumptions` and therefore no longer needs a
separate fixed-slice TM witness.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
    (hMag := hMag) (n := n) (hn := hn)
  exact LowerBounds.not_ppolyDAG_of_dag_stableRestriction hStable

/--
Companion `P ≠ NP` endpoint from the same fixed-slice stable-restriction
producer.
-/
theorem P_ne_NP_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
      (hMag := hMag) (n := n) (hn := hn) hStable)

/--
Asymptotic DAG separation from the localized Route-B source-closure package on
one concrete asymptotic slice.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
    (hMag := hMag) (n := n) (hn := hn)
  exact LowerBounds.dag_stableRestriction_producer_of_sourceClosure hSrc

/--
Companion `P ≠ NP` endpoint from the same asymptotic fixed-slice
source-closure package.
-/
theorem P_ne_NP_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
      (hMag := hMag) (n := n) (hn := hn) hSrc)

/--
Asymptotic DAG separation from the named Route-B blocker on one concrete
asymptotic slice.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
    (hMag := hMag) (n := n) (hn := hn)
  exact
    LowerBounds.dagRouteBSourceClosure_of_blocker
      (p := hMag.antiChecker.asymptotic.pAt n hn) hBlocker

/--
Companion `P ≠ NP` endpoint from the same asymptotic fixed-slice blocker.
-/
theorem P_ne_NP_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
      (hMag := hMag) (n := n) (hn := hn) hBlocker)


/--
Package-shaped final wrapper kept for CI/signature policy compatibility.

Logical payload remains DAG-only (`hNPDag` + internal inclusion); `hMag` is a
context package argument and is not consumed until a formal bridge from
magnification assumptions to DAG separation is added.
-/
theorem P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  let _ := hMag
  exact P_ne_NP_final_dag_only hNPDag

end Magnification
end Pnp3
