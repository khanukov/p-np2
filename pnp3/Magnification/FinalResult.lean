import Magnification.Bridge_to_Magnification_Partial
import Magnification.AsymptoticFormulaCollapse
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Magnification.PipelineStatements_Partial
import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.DAGUnconditionalBlocker
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

/-!
Thin DAG weak-route wrappers (active mainline surface):

- source theorem target:
  `SmallDAGImpliesPromiseYesSubcubeAt` / `SmallDAGImpliesPromiseYesSubcubeStatement`
- weak terminal consumer:
  `SmallDAGImpliesAcceptedFamilyAt` / `SmallDAGImpliesAcceptedFamilyStatement`
- asymptotic no-small-DAG endpoint:
  `MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound)`.

These wrappers intentionally keep the final file oriented to the weak accepted-family
route without forcing the stronger restriction-provider contracts as the only
frontier.
-/

/--
Final-surface wrapper: global no-small-DAG closure from the weak accepted-family
statement.

This is the theorem-level bridge used by the new weak mainline:
`AcceptedFamilyCertificateAt` is treated as terminal consumer, and the closure
to per-slice impossibility of small DAG solvers is entirely mechanical.
-/
theorem noSmallDAG_surface_of_acceptedFamilyStatement
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hAccepted : LowerBounds.SmallDAGImpliesAcceptedFamilyStatement F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.no_dag_solver_of_acceptedFamily F SizeBound hAccepted

/--
Final-surface wrapper: global no-small-DAG closure from the one-sided YES-centered
source statement.

This keeps the nearest-term source target explicit in `FinalResult`:
`SmallDAGImpliesPromiseYesSubcubeStatement` is reduced immediately to the same
no-solver endpoint.
-/
theorem noSmallDAG_surface_of_promiseYesSubcubeStatement
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hYes : LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.no_dag_solver_of_promise_yes_subcube F SizeBound hYes

/--
Final-surface wrapper for the parallel structured-image backup route:

`PRGImageAcceptanceAt provider -> no small DAG solver`.

This keeps the backup producer compiled at the same endpoint level as the
promise-YES and accepted-family mainline wrappers.
-/
theorem noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hPrg : LowerBounds.prgImageAcceptanceAtProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices F SizeBound hPrg

/--
Final-surface wrapper for distributional easy-image PRG providers, with
internal counting closure and explicit epsilon-smallness side condition.
-/
theorem noSmallDAG_surface_of_easyImagePRGAtProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hEasy : LowerBounds.easyImagePRGAtProviderOnSlices F SizeBound)
  (hEpsSmall :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : LowerBounds.SmallDAGWitnessOnSlice
        (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
        (hEasy n β ε W).epsilon <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat))) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_easyImagePRGAtProviderOnSlices
    F SizeBound hEasy hEpsSmall

/--
Final-surface wrapper from source-level easy-image fooling providers.
-/
theorem noSmallDAG_surface_of_smallDAGEasyImageFoolingSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyImageFoolingSourceProviderOnSlices
    F SizeBound hSource

/-- Final-surface wrapper for the minimal canonical distributional source. -/
theorem noSmallDAG_surface_of_smallDAGEasyDistSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyDistSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices
    F SizeBound hSource

/--
Final-surface wrapper for one-sided easy-HSG source providers.

This is the preferred weak mainline endpoint because downstream contradiction
uses only one-sided lower transfer.
-/
theorem noSmallDAG_surface_of_smallDAGEasyHSGSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyHSGSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
    F SizeBound hSource

/--
Final-surface wrapper from upstream average-case/hardness source providers.
-/
theorem noSmallDAG_surface_of_smallDAGAverageCaseHardnessSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hAvg : LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGAverageCaseHardnessSourceProviderOnSlices
    F SizeBound hAvg

/--
Final-surface wrapper for the strong restriction/shrinkage fallback stack.

This theorem intentionally routes the stronger extraction+numerics contract into
the same weak accepted-family terminal closure, so the fallback remains
compatible with the weak mainline rather than reintroducing a separate endpoint.
-/
theorem noSmallDAG_surface_of_restrictionFallbackOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hExtract : LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
  (hNumeric :
    LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact
    LowerBounds.noSmallDAG_of_restrictionExtractionAndNumericProviderOnSlices_via_acceptedFamily
      F SizeBound hExtract hNumeric

/--
Asymptotic weak-route wrapper from eventual accepted-family production.
-/
theorem magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily
    (F : LowerBounds.GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyAccepted :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nAcc : Nat, ∀ n ≥ nAcc, LowerBounds.SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) :
    LowerBounds.MagnificationStyleNoSmallDAG (LowerBounds.SmallDAGSolver F SizeBound) := by
  exact LowerBounds.magnificationStyleNoSmallDAG_of_eventually_acceptedFamily
    F SizeBound ε β0 hε hβ0 hEventuallyAccepted

/--
Asymptotic weak-route wrapper from eventual one-sided YES-subcube production.
-/
theorem magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube
    (F : LowerBounds.GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyYes :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nYes : Nat, ∀ n ≥ nYes, LowerBounds.SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) :
    LowerBounds.MagnificationStyleNoSmallDAG (LowerBounds.SmallDAGSolver F SizeBound) := by
  exact LowerBounds.magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube
    F SizeBound ε β0 hε hβ0 hEventuallyYes

/--
Thin bridge wrapper (variant-1 style): a single global `PpolyDAG` witness on an
asymptotic language `bridge.L` implies the eventual small-solver surface for
the chosen slice family `F`.

This wrapper intentionally stops at `EventuallySmallDAGSolverSurface`; it does
not yet claim DAG separation by itself.  Its purpose is to expose the new
global-to-slice quantifier plumbing at the `FinalResult` boundary.
-/
theorem eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hDagGlobal : ComplexityInterfaces.PpolyDAG bridge.L) :
    LowerBounds.EventuallySmallDAGSolverSurface F := by
  exact LowerBounds.eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness
    F bridge ε β0 hε hβ0 hDagGlobal

/--
Thin contradiction wrapper at the global-witness bridge boundary:
if magnification-style no-small-solver is available uniformly for every
canonical witness-derived size-bound family, then the bridged global language
cannot belong to `PpolyDAG`.

This theorem keeps the result bridge-local (`¬ PpolyDAG bridge.L`) and avoids
claiming full class separation prematurely.
-/
theorem not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNoSmall :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                ¬ LowerBounds.SmallDAGSolver
                    F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge hNoSmall

/--
Thin bridge-local contradiction wrapper instantiated with the weak
accepted-family source theorem.
-/
theorem not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesAcceptedFamilyStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge hAcceptedWeak

/--
Thin bridge-local contradiction wrapper instantiated with the nearer-term
promise-YES weak source theorem.
-/
theorem not_globalPpolyDAG_surface_of_promiseYesWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_promiseYesWeakRoute
      F bridge hYesWeak

/--
Thin bridge-local contradiction wrapper instantiated with the PRG-image
accepted-image route.

This follows exactly the same bridge template as the accepted-family/promise-YES
wrappers: we first collapse the stronger source-side producer to the weak
accepted-family statement, then reuse the canonical bridge-local contradiction
schema without adding any new quantifier plumbing.
-/
theorem not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hPrgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.prgImageAcceptanceAtProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge ?_
  intro hInDag
  exact
    LowerBounds.smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider
      F
      (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
      (hPrgWeak hInDag)

/--
Thin bridge-local contradiction wrapper instantiated with the distributional
easy-image PRG route (plus epsilon-smallness side condition).
-/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge ?_
  intro hInDag
  refine ⟨(1 / 4 : Rat), by positivity, (1 / 2 : Rat), by positivity, ?_⟩
  intro β hβPos hβLt
  refine ⟨0, ?_⟩
  intro n hn
  exact LowerBounds.noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices
    F
    (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
    (hEasyWeak hInDag)
    n β (1 / 4)

/--
Thin bridge-local contradiction wrapper instantiated with the one-sided easy-HSG
weak route.
-/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyHSGWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge ?_
  intro hInDag
  refine ⟨(1 / 4 : Rat), by positivity, (1 / 2 : Rat), by positivity, ?_⟩
  intro β hβPos hβLt
  refine ⟨0, ?_⟩
  intro n hn
  exact LowerBounds.noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
    F
    (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
    (hEasyHSGWeak hInDag)
    n β (1 / 4)

/--
Weak-route wrapper directly from upstream average-case/hardness sources.
-/
theorem not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hAvgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hAvgWeak hInDag))

/--
Thin bridge-local contradiction wrapper instantiated with the stronger
restriction-extraction+numeric fallback route.

The route is intentionally wired through the same accepted-family bridge schema
to avoid introducing another endpoint-specific contradiction theorem.
-/
theorem not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hFallbackWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ hExtract :
          LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag),
          LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) hExtract) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge ?_
  intro hInDag
  rcases hFallbackWeak hInDag with ⟨hExtract, hNumeric⟩
  exact
    LowerBounds.smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider
      F
      (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
      hExtract
      hNumeric

/--
Class-level wrapper: accepted-family weak route + explicit NP witness on
`bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesAcceptedFamilyStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    LowerBounds.NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute
      F bridge hNP hAcceptedWeak

/--
Fallback class-level wrapper from the canonical support-half family.

This packages the old Route-A2 accepted-family fallback into the asymptotic
bridge endpoint without restating the accepted-family weak-route plumbing.
-/
theorem not_globalPpolyDAG_surface_of_supportHalfBoundFamily
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : LowerBounds.SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute
      F bridge
      (LowerBounds.gateG1_routeA2_acceptedFamily_of_supportHalfBoundFamily
        F hSupportHalf)

/--
Fallback class-level wrapper from the canonical support-half family to
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : LowerBounds.SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute
      F bridge hNP
      (LowerBounds.gateG1_routeA2_acceptedFamily_of_supportHalfBoundFamily
        F hSupportHalf)

/--
Class-level wrapper: promise-YES weak route + explicit NP witness on
`bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    LowerBounds.NP_not_subset_PpolyDAG_of_promiseYesWeakRoute
      F bridge hNP hYesWeak

/--
Class-level wrapper: PRG-image accepted-image weak route + explicit NP witness
on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hPrgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.prgImageAcceptanceAtProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute
      F bridge hPrgWeak

/--
Class-level wrapper: distributional easy-image PRG weak route + explicit NP
witness on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_easyImagePRGWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hEasyWeak

/--
Backward-compatible alias (old name) to the source-first weak-route wrapper.
-/
theorem not_globalPpolyDAG_surface_of_easyImagePRGWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hEasyWeak

/--
Renamed source-first class-level wrapper.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_easyImagePRGWeakRoute
      F bridge hNP hEasyWeak

/--
Class-level wrapper from one-sided easy-HSG weak route.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyHSGWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge hEasyHSGWeak

/--
Class-level wrapper directly from upstream average-case/hardness weak route.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAvgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge hNP
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hAvgWeak hInDag))

/-- Backward-compatible alias under previous source-wrapper name. -/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute F bridge hEasyWeak

/-- Backward-compatible alias under previous source-wrapper name. -/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute F bridge hNP hEasyWeak

/--
Bridge from the single canonical source-theorem debt to global non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyImageSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyImage_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hCanonical

/--
Bridge from the canonical one-sided easy-HSG source debt to global
non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyHSGSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyHSG_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyHSGSourceProviderOnSlices
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hCanonical hInDag))

/--
Bridge from canonical easy-density source debt to global non-inclusion.

This is the density-first mainline wrapper: density debt is compiled to the
canonical one-sided easy-HSG debt internally, then the existing HSG closure is
reused unchanged.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyDensity_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyHSGSourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_easyHSG_source_on_slices_of_canonical_smallDAG_easyDensity_source_on_slices
        F hCanonical)

/--
Bridge from witness-indexed canonical easy-density debt to global non-inclusion.

Compared with
`not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
this route bypasses the all-circuits density object and uses the witness-level
transfer closure directly.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  have hNoSmall :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                ¬ LowerBounds.SmallDAGSolver
                    F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
    intro hInDag
    refine ⟨(1 / 8 : Rat), by norm_num, (1 : Rat), by norm_num, ?_⟩
    intro β hβ hβlt
    refine ⟨0, ?_⟩
    intro n hn
    exact
      (LowerBounds.noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices
        F hCanonical hInDag n β (1 / 8 : Rat))
  exact
    not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies
      F bridge hNoSmall

/--
Bridge from canonical average-case/hardness source debt to global contradiction.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGAvgHardnessSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_avgHardness_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
      F bridge hCanonical

/--
Density-first class-level wrapper:
canonical easy-density source debt + NP witness on `bridge.L` imply
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hCanonical : LowerBounds.canonical_smallDAG_easyDensity_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
      F bridge hCanonical

/--
Density-first class-level wrapper for the witness-indexed canonical debt:
if we can prove witness-indexed canonical easy-density sources on all slices,
then together with an NP witness on `bridge.L` we derive
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hCanonical : LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
      F bridge hCanonical

/--
Bridge from witness-uniform-lower canonical debt to global non-inclusion.

This theorem is a thin composition:
`witnessUniformLower` debt -> witness-easy-density debt -> global contradiction.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hUniform : LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
        F hUniform)

/--
Class-level wrapper from witness-uniform-lower canonical debt.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hUniform : LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
      F bridge hUniform

/--
Bridge from quarter-bounded witness-transfer debt to global non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hQuarterTr : LowerBounds.canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter
        F hQuarterTr)

/--
Class-level wrapper from quarter-bounded witness-transfer debt.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hQuarterTr : LowerBounds.canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
      F bridge hQuarterTr

/--
Class-level wrapper: stronger restriction-extraction+numeric fallback route +
explicit NP witness on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hFallbackWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ hExtract :
          LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag),
          LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) hExtract) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
      F bridge hFallbackWeak

/-!
Current DAG endpoint ledger for this file:

- `P_ne_NP_final` remains conditional on explicit DAG separation
  `hNPDag : NP_not_subset_PpolyDAG`.
- The stable-restriction, certificate-provider, invariant-provider, and
  support-bounds wrappers below are compiled stronger sufficient routes and
  compatibility/audit surfaces.
- The generic accepted-family weak endpoint is now already formalized at the
  slice level (`AcceptedFamilyCertificateAt`) and at the asymptotic barrier
  schema level (`SmallDAGImpliesAcceptedFamilyAt` /
  `SmallDAGImpliesAcceptedFamilyStatement`); the nearer-term chosen mainline
  theorem target is the one-sided promise-aware schema
  `SmallDAGImpliesPromiseYesSubcubeAt` /
  `SmallDAGImpliesPromiseYesSubcubeStatement`, and
  `YesSubcubeCertificateAt` is wired as a stronger structured producer into
  that route.
- This file now exposes thin asymptotic weak-route wrappers (`magnificationStyle*`)
  consuming eventual accepted-family / promise-YES-subcube statements directly.
  The remaining open step is the actual DAG-side source theorem producing those
  eventual statements from strict small-DAG semantics.
-/

/--
Final DAG-separation wrapper specialized to the stronger stable-restriction
route.

This wrapper is kept as a compiled sufficient condition and audit surface: if
one can prove that
every DAG solver for the fixed `gapPartialMCSP` slice yields a small stable
restriction for the canonical DAG payload, then the lower-bound layer already
produces `NP ⊄ PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload
        (LowerBounds.dagCanonicalPayload hDag)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM W hStable

/--
Final DAG-separation wrapper specialized to the new DAG-native Route-B
certificate provider.

Compared with `NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM`, this
form packages the source-side obligation as explicit per-DAG certificates
(`DAGStableRestrictionCertificate`) instead of raw probe witnesses. It remains
a stronger optional route rather than the intended theorem-minimal blocker.
-/
theorem NP_not_subset_PpolyDAG_final_of_certificateProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hCert : LowerBounds.dagStableRestrictionCertificateProvider p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_certificateProvider_TM W hCert

/--
End-to-end `P ≠ NP` wrapper specialized to the same DAG stable-restriction
producer obligation.

This remains a stronger compatibility wrapper. The roadmap does not treat the
producer-side proof of `hStable` as the only honest remaining theorem-level
blocker.
-/
theorem P_ne_NP_final_of_dag_stableRestriction_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload
        (LowerBounds.dagCanonicalPayload hDag)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM W hStable)

/--
End-to-end `P ≠ NP` wrapper specialized to the DAG-native Route-B certificate
provider.
-/
theorem P_ne_NP_final_of_certificateProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hCert : LowerBounds.dagStableRestrictionCertificateProvider p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_certificateProvider_TM W hCert)

/--
Final DAG-separation wrapper specialized to a DAG-side locality-invariant
provider (the stronger Route-B source contract).
-/
theorem NP_not_subset_PpolyDAG_final_of_invariantProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hInv : LowerBounds.dagStableRestrictionInvariantProvider p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_invariantProvider_TM W hInv

/--
End-to-end `P ≠ NP` wrapper for the same DAG-side locality-invariant provider.
-/
theorem P_ne_NP_final_of_invariantProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hInv : LowerBounds.dagStableRestrictionInvariantProvider p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_invariantProvider_TM W hInv)

/--
Final DAG-separation wrapper specialized to the localized Route-B source
closure package (`LowerBounds.DAGRouteBSourceClosure`).

This keeps the endpoint surface simple: all source-side DAG work is packaged in
one structure and consumed here without introducing additional endpoint APIs.
-/
theorem NP_not_subset_PpolyDAG_final_of_sourceClosure_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hSrc : LowerBounds.DAGRouteBSourceClosure p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_sourceClosure_TM W hSrc

/--
Companion `P ≠ NP` endpoint for the same localized Route-B source closure
package.
-/
theorem P_ne_NP_final_of_sourceClosure_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hSrc : LowerBounds.DAGRouteBSourceClosure p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_sourceClosure_TM W hSrc)

/--
Direct final DAG-separation wrapper from the named Route-B blocker gate.

This avoids exposing intermediate source packaging at call sites when one wants
to state end-to-end implications in blocker-first form.
-/
theorem NP_not_subset_PpolyDAG_final_of_blocker_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBlocker : LowerBounds.dagRouteBSourceBlocker p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_blocker_TM W hBlocker

/--
Companion `P ≠ NP` final wrapper from the same named Route-B blocker gate.
-/
theorem P_ne_NP_final_of_blocker_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBlocker : LowerBounds.dagRouteBSourceBlocker p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_blocker_TM W hBlocker)

/--
Final DAG-separation wrapper specialized to the support-bounds + DAG→formula
bridge route.

This is intentionally a thin endpoint around the new lower-bound closure lemma:
it does not add new assumptions beyond the support-bounds package and the
functional DAG→formula bridge.
-/
theorem NP_not_subset_PpolyDAG_final_of_supportBounds_and_dagToFormula_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
  (hDagToFormula :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_supportBounds_and_dagToFormula_TM
    W hBounds hDagToFormula

/--
Companion `P ≠ NP` endpoint for the same support-bounds + DAG→formula route.
-/
theorem P_ne_NP_final_of_supportBounds_and_dagToFormula_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
  (hDagToFormula :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_supportBounds_and_dagToFormula_TM
      W hBounds hDagToFormula)


/--
Final DAG-separation wrapper specialized to the packaged stable-restriction
route.

Just like the lower-bound theorem below it, this is only a thin corollary of
the probe-form final route: packaged payloads are converted back to the single
probe obligation and the existing final theorem is reused unchanged.
-/
theorem NP_not_subset_PpolyDAG_final_of_dag_stableRestrictionPayload_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ _ : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.AbstractGapStableRestrictionPayload p)
  (hBase :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      (hStable hDag).base = LowerBounds.dagCanonicalPayload hDag) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM W
    (LowerBounds.dag_stableRestrictionGoal_of_stableRestrictionPayload
      hStable hBase)


/--
End-to-end `P ≠ NP` wrapper specialized to the packaged DAG stable-restriction
producer obligation.

Again this is just a thin corollary of the probe-form final route.
-/
theorem P_ne_NP_final_of_dag_stableRestrictionPayload_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ _ : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.AbstractGapStableRestrictionPayload p)
  (hBase :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      (hStable hDag).base = LowerBounds.dagCanonicalPayload hDag) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_of_dag_stableRestriction_TM W
    (LowerBounds.dag_stableRestrictionGoal_of_stableRestrictionPayload
      hStable hBase)


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
