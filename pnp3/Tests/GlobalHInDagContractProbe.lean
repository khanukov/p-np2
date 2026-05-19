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

/-- Constant-false DAG used on non-active lengths in the projection witness. -/
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

/--
The global polynomial-size DAG family contract for the asymptotic language.
A single pair `(coeff, exponent)` controls all input lengths.
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
Global polynomial size-bound predicate derived from
`GlobalAsymptoticDAGWitness`. The epsilon parameter is intentionally unused to
match the route signature.
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
Forward projection from a global asymptotic DAG family to per-slice `InPpolyDAG`.
The construction is noncomputable because it packages Type-level witnesses.
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
        if m = activeLen then DagCircuit.size (W.family activeLen) else 2
      polyBound_poly := ?_
      family := fun m =>
        if h : m = activeLen then h ▸ W.family activeLen else constFalseDag m
      family_size_le := ?_
      correct := ?_ }
  · refine ⟨DagCircuit.size (W.family activeLen) + 2, ?_⟩
    intro m
    by_cases hm : m = activeLen
    · simp [hm]
    · simp [hm]
  · intro m
    by_cases hm : m = activeLen
    · simp [hm]
    · simp [hm, constFalseDag_size]
  · intro m x
    by_cases hm : m = activeLen
    · subst hm
      simp only [dif_pos rfl]
      calc
        DagCircuit.eval (W.family activeLen) x
            = Models.gapPartialMCSP_AsymptoticLanguage hAsym.spec activeLen x :=
              W.decides_global activeLen x
        _ = Models.gapPartialMCSP_Language p activeLen x := by
              simpa [p, activeLen, eventualGapSliceFamily_of_asymptotic]
                using hAsym.sliceEq (max n hAsym.N0) (Nat.le_max_right _ _) x
    · simp [hm, constFalseDag_eval, Models.gapPartialMCSP_Language, p, activeLen]

end GlobalHInDagContractProbe
end Tests
end Pnp3
