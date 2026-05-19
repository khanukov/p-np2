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

/-- A tiny off-slice fallback DAG that always returns `false`. -/
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

/-- The global polynomial-size DAG family contract for the asymptotic
language. -/
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

/-- Global polynomial size-bound predicate derived from a global contract. -/
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
Project a global asymptotic-family DAG contract to a per-slice `InPpolyDAG`
witness.  The proof transports the global language witness to canonical slice
lengths, then reuses the standard off-length constant-false completion.
-/
def globalWitness_to_hInDag
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym)
    (n : Nat) (β : Rat) :
    InPpolyDAG
      (Models.gapPartialMCSP_Language
        ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)) := by
  let F := eventualGapSliceFamily_of_asymptotic hAsym
  let bridge : AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F :=
    { L := Models.gapPartialMCSP_AsymptoticLanguage hAsym.spec
      sliceEq := by
        intro n β x
        simpa [F, eventualGapSliceFamily_of_asymptotic,
          GapSliceFamilyEventually.encodedLen]
          using (F.sliceEq n β x) }
  let hDagGlobal : PpolyDAG bridge.L := by
    refine ⟨{ polyBound := fun N => W.coeff * N ^ W.exponent + W.coeff
              polyBound_poly := ?_
              family := W.family
              family_size_le := W.size_bound
              correct := W.decides_global }, trivial⟩
    refine ⟨W.coeff + W.exponent + 1, ?_⟩
    intro N
    have hmul : W.coeff * N ^ W.exponent ≤ N ^ (W.coeff + W.exponent + 1) := by
      by_cases hCoeffZero : W.coeff = 0
      · simp [hCoeffZero]
      · have hCoeffPos : 0 < W.coeff := Nat.pos_of_ne_zero hCoeffZero
        have hNpow : N ^ W.exponent ≤ N ^ (W.coeff + W.exponent + 1) := by
          refine Nat.pow_le_pow_right ?_ ?_
          · exact Nat.zero_le _
          · omega
        exact le_trans (Nat.mul_le_mul_right _ hNpow) (by
          have : W.coeff ≤ N ^ (W.coeff + W.exponent + 1) := by
            by_cases hNZero : N = 0
            · subst hNZero
              simp at hCoeffPos
            · have hNPos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hNZero)
              have hPowPos : 1 ≤ N ^ (W.coeff + W.exponent + 1) := Nat.one_le_pow _ hNPos
              exact le_trans (Nat.succ_le_of_lt hCoeffPos) hPowPos
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right (N ^ W.exponent) this)
    exact le_trans (Nat.add_le_add hmul (Nat.le_refl _)) (by
      have : W.coeff ≤ N ^ (W.coeff + W.exponent + 1) + (W.coeff + W.exponent + 1) := by
        exact Nat.le_add_right _ _
      omega)
  have hSlice :
      PpolyDAG
        (Models.gapPartialMCSP_Language (F.paramsOf n β)) :=
    ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths F bridge hDagGlobal n β
  rcases hSlice with ⟨hIn, -⟩
  exact hIn

end GlobalHInDagContractProbe
end Tests
end Pnp3
