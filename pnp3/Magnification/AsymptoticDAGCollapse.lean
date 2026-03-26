import Models.Model_PartialMCSP
import Complexity.Interfaces
import Mathlib.Tactic

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-- One-gate constant-false DAG used off the target slice in the bridge. -/
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

/-- Monotone padding used to turn an asymptotic DAG witness into a fixed-slice one. -/
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
Asymptotic DAG collapse through an explicit slice bridge.

This is the exact DAG analogue of the formula-side helper: once an asymptotic
DAG witness can be restricted to one fixed slice, any fixed-slice contradiction
immediately propagates to the global asymptotic language.
-/
theorem asymptotic_dag_collapse_of_slice_bridge
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hCollapseFixed :
      ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False)
    (hSliceBridge :
      ComplexityInterfaces.PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) →
        ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) → False := by
  intro hAsymDag
  exact hCollapseFixed (hSliceBridge hAsymDag)

/--
Constructive asymptotic-to-fixed bridge from pointwise slice agreement at the
target length `partialInputLen p`.

Compared with the formula bridge, the only extra bookkeeping is that the
off-slice fallback circuit has DAG size `2` rather than `1`, so the new
polynomial bound is padded to `n^(c+2) + (c+2)`.
-/
theorem ppolyDAG_fixed_of_asymptotic_slice
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
Asymptotic DAG collapse from fixed-slice collapse plus explicit slice
agreement.
-/
theorem asymptotic_dag_collapse_of_slice_agreement
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hCollapseFixed :
      ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False)
    (hSliceEq :
      ∀ x : Core.BitVec (partialInputLen p),
        gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
          gapPartialMCSP_Language p (partialInputLen p) x) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) → False := by
  apply asymptotic_dag_collapse_of_slice_bridge (spec := spec) (p := p) hCollapseFixed
  exact ppolyDAG_fixed_of_asymptotic_slice (spec := spec) (p := p) hSliceEq

/--
Canonical `NP ⊄ PpolyDAG` wrapper from asymptotic DAG collapse.
-/
theorem NP_not_subset_PpolyDAG_of_asymptotic_dag_collapse
    (spec : GapPartialMCSPAsymptoticSpec)
    (hNPstrict : ComplexityInterfaces.NP_strict
      (gapPartialMCSP_AsymptoticLanguage spec))
    (hCollapse :
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_AsymptoticLanguage spec) → False) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact ⟨gapPartialMCSP_AsymptoticLanguage spec, hNPstrict, hCollapse⟩

end Magnification
end Pnp3
