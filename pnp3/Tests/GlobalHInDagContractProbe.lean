import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems

namespace Pnp3
namespace Tests
namespace GlobalHInDagContractProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds

noncomputable section

/-- A tiny fallback DAG used away from the active encoded input length. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

private theorem constFalseDag_size {n : Nat} :
    DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, DagCircuit.size]

private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/-- The global polynomial-size DAG family contract for the asymptotic language. -/
structure GlobalAsymptoticDAGWitness
    (hAsym : AsymptoticFormulaTrackHypothesis) where
  family : ∀ N : Nat, DagCircuit N
  coeff : Nat
  exponent : Nat
  size_bound : ∀ N : Nat,
    DagCircuit.size (family N) ≤ coeff * N ^ exponent + coeff
  decides_global :
    ∀ N : Nat, ∀ x : Bitstring N,
      DagCircuit.eval (family N) x =
        Models.gapPartialMCSP_AsymptoticLanguage hAsym.spec N x

/-- Global polynomial size-bound predicate derived from a global family contract. -/
def globalPolyDAGSizeBound
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym) :
    Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s =>
    s ≤ W.coeff *
      ((eventualGapSliceFamily_of_asymptotic hAsym).encodedLen n β) ^ W.exponent
      + W.coeff

/-- Global version of `AsymptoticPromiseYesWeakRouteEventually`. -/
def AsymptoticPromiseYesWeakRouteEventually_global
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ W : GlobalAsymptoticDAGWitness hAsym,
    ∃ ε β0 : Rat, 0 < ε ∧ 0 < β0 ∧
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ n0 : Nat,
          (eventualGapSliceFamily_of_asymptotic hAsym).N0 ≤ n0 ∧
            ∀ n ≥ n0,
              SmallDAGImpliesPromiseYesSubcubeAtEventually
                (eventualGapSliceFamily_of_asymptotic hAsym)
                (globalPolyDAGSizeBound W)
                n β ε

/--
Forward projection from one global DAG-family contract to per-slice `InPpolyDAG`.

This definition is noncomputable because it packages size/equality reasoning over
an abstract family of circuits provided by `W`.
-/
def globalWitness_to_hInDag
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym)
    (n : Nat) (β : Rat) :
    InPpolyDAG
      (Models.gapPartialMCSP_Language
        ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)) := by
  let p := (eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β
  let activeLen := Models.partialInputLen p
  refine
    { polyBound := fun m =>
        m ^ (DagCircuit.size (W.family activeLen) + 2) +
          (DagCircuit.size (W.family activeLen) + 2)
      polyBound_poly := by
        refine ⟨DagCircuit.size (W.family activeLen) + 2, ?_⟩
        intro m
        rfl
      family := fun m =>
        if h : m = activeLen then h ▸ W.family activeLen else constFalseDag m
      family_size_le := by
        intro m
        by_cases hm : m = activeLen
        · subst hm
          have hk : DagCircuit.size (W.family activeLen) ≤ DagCircuit.size (W.family activeLen) + 2 := by omega
          simpa using le_trans hk (Nat.le_add_left _ _)
        · simp [hm, constFalseDag_size]
          omega
      correct := by
        intro m x
        by_cases hm : m = activeLen
        · subst hm
          simp
          calc
            DagCircuit.eval (W.family activeLen) x
                = gapPartialMCSP_AsymptoticLanguage hAsym.spec activeLen x :=
                  W.decides_global activeLen x
            _ = gapPartialMCSP_Language p activeLen x := by
                  simpa [p, activeLen, eventualGapSliceFamily_of_asymptotic]
                    using hAsym.sliceEq (max n hAsym.N0) (Nat.le_max_right _ _) x
        · have hneq : m ≠ partialInputLen p := by simpa [activeLen] using hm
          have hnot : ¬(m = partialInputLen ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)) := by
            simpa [p] using hneq
          simp [hm, constFalseDag_eval, gapPartialMCSP_Language, hnot] }end

end GlobalHInDagContractProbe
end Tests
end Pnp3
