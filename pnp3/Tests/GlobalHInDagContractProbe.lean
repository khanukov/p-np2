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

/-- Constant-false DAG used on inactive lengths in the slice projection. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

/-- Size of `constFalseDag` is the fixed constant `2`. -/
private theorem constFalseDag_size {n : Nat} :
    DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, DagCircuit.size]

/-- Evaluation of `constFalseDag` is uniformly `false`. -/
private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/--
The global polynomial-size DAG family contract for the asymptotic language.

A single family and one global polynomial envelope `(coeff, exponent)` must work
simultaneously for all input lengths.
-/
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

/--
Global polynomial size-bound predicate derived from one global witness.

The epsilon argument is intentionally ignored to preserve compatibility with
Phase III barrier theorem signatures.
-/
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
Project a global asymptotic DAG witness to per-slice `InPpolyDAG`.

This definition is noncomputable because it packages a semantic family witness
inside `InPpolyDAG` and uses classical branching over input-length equality.
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
    { polyBound := fun m => if m = activeLen then DagCircuit.size (W.family activeLen) else 2
      polyBound_poly := ?_
      family := fun m => if h : m = activeLen then h ▸ W.family activeLen else constFalseDag m
      family_size_le := ?_
      correct := ?_ }
  · refine ⟨DagCircuit.size (W.family activeLen) + 2, ?_⟩
    intro m
    by_cases hm : m = activeLen
    · simp [polyBound, hm]
      omega
    · simp [polyBound, hm]
      omega
  · intro m
    by_cases hm : m = activeLen
    · simp [hm]
    · simp [hm, constFalseDag_size]
  · intro m x
    by_cases hm : m = activeLen
    · subst hm
      have hGlobal := W.decides_global activeLen x
      have hSliceEq :=
        hAsym.sliceEq (max n hAsym.N0) (Nat.le_max_right n hAsym.N0) x
      simpa [p, activeLen, eventualGapSliceFamily_of_asymptotic,
        GapSliceFamilyEventually.encodedLen] using hGlobal.trans hSliceEq
    · simp [hm, constFalseDag_eval, Models.gapPartialMCSP_Language]

end GlobalHInDagContractProbe
end Tests
end Pnp3
