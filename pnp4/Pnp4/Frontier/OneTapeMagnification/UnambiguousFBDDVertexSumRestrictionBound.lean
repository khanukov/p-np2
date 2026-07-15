import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPerVertexRestrictionBound
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Even-degree and vertex-sum restriction bounds for a finite uFBDD

This module takes the already-formalized squared bound for one fixed vertex
at even degree `2 * m`, unsquares it over the nonnegative rationals, and then
applies the ordinary triangle inequality to the finite sum over all vertices.
The resulting bound is the honest
`Fintype.card B.Vertex * p ^ m` estimate for the displayed vertex sum.

This module itself does **not** identify the full high-degree Fourier
remainder of a program with that vertex sum.  The separate exact regrouping
and its program-level high-degree consequence are supplied by
`UnambiguousFBDDHighDegreeRegrouping` and
`UnambiguousFBDDOneRoundHighDegreeBound`.
-/

namespace FiniteBooleanVertexSumRestrictionBound

open scoped BigOperators
open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound

/-! ## Elementary exact finite-sum inequalities -/

/-- Nonnegative rationals may be compared by comparing their squares. -/
theorem le_of_sq_le_sq_of_nonneg {a b : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsq : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  rcases ha.eq_or_lt with haZero | haPos
  · nlinarith
  · nlinarith

/-- The absolute value of a finite sum, averaged over a nonempty finite seed
space, is at most the sum of the averaged absolute values. -/
theorem finiteAverage_abs_finset_sum_le_sum_finiteAverage_abs
    {Seed Index : Type*} [Fintype Seed] [Nonempty Seed]
    (indices : Finset Index) (f : Index → Seed → ℚ) :
    finiteAverage (fun seed => |∑ index ∈ indices, f index seed|) ≤
      ∑ index ∈ indices, finiteAverage (fun seed => |f index seed|) := by
  calc
    finiteAverage (fun seed => |∑ index ∈ indices, f index seed|) ≤
        finiteAverage (fun seed => ∑ index ∈ indices, |f index seed|) := by
      apply finiteAverage_mono
      intro seed
      exact Finset.abs_sum_le_sum_abs (fun index => f index seed) indices
    _ = ∑ index ∈ indices,
          finiteAverage (fun seed => |f index seed|) := by
      exact finiteAverage_finset_sum indices
        (fun index seed => |f index seed|)

/-- `Fintype` specialization of the exact averaged triangle inequality. -/
theorem finiteAverage_abs_fintype_sum_le_sum_finiteAverage_abs
    {Seed Index : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Index]
    (f : Index → Seed → ℚ) :
    finiteAverage (fun seed => |∑ index : Index, f index seed|) ≤
      ∑ index : Index, finiteAverage (fun seed => |f index seed|) := by
  simpa using
    (finiteAverage_abs_finset_sum_le_sum_finiteAverage_abs
      (Seed := Seed) (Finset.univ : Finset Index) f)

/-- A uniform bound on every averaged summand yields the corresponding
cardinality-times-bound estimate for the averaged absolute finite sum. -/
theorem finiteAverage_abs_fintype_sum_le_card_mul_of_bound
    {Seed Index : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Index]
    (f : Index → Seed → ℚ) (bound : ℚ)
    (hbound : ∀ index, finiteAverage (fun seed => |f index seed|) ≤ bound) :
    finiteAverage (fun seed => |∑ index : Index, f index seed|) ≤
      (Fintype.card Index : ℚ) * bound := by
  calc
    finiteAverage (fun seed => |∑ index : Index, f index seed|) ≤
        ∑ index : Index, finiteAverage (fun seed => |f index seed|) :=
      finiteAverage_abs_fintype_sum_le_sum_finiteAverage_abs f
    _ ≤ ∑ _index : Index, bound := by
      apply Finset.sum_le_sum
      intro index _
      exact hbound index
    _ = (Fintype.card Index : ℚ) * bound := by simp

end FiniteBooleanVertexSumRestrictionBound

namespace FiniteUnambiguousFBDD

open scoped BigOperators
open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanVertexSumRestrictionBound

/-! ## The displayed contribution of one vertex -/

/-- The masked uniform average of the compatible degree-`k` prefix slice
times the suffix Laplacian at one fixed vertex. -/
noncomputable def vertexRestrictionContribution
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) (k : Nat)
    (base mask : Fin n → Bool) : ℚ :=
  finiteAverage (fun uniform : Fin n → Bool =>
    B.ratCompatiblePrefixHomogeneousSlice vertex k
        (maskedInput base mask uniform) *
      B.suffixLaplacian vertex (maskedInput base mask uniform))

/-! ## Even-degree unsquaring -/

/-- At even degree `2 * m`, the squared per-vertex restriction theorem
unsquares to the exact `p ^ m` scale.  All source moment hypotheses and the
syntactic read-once premise remain explicit. -/
theorem vertexRestrictionContribution_evenDegree_absMoment_le_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) (vertex : B.Vertex)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n (2 * m),
        ∀ beta ∈ degreeSupports n (2 * m),
          alpha ≠ beta →
            finiteAverage (fun d : DSeed =>
              FiniteBooleanFourier.character alpha (D d) *
                FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n (2 * m),
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ (2 * m)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      |B.vertexRestrictionContribution vertex (2 * m)
        (D seed.1) (T seed.2)|) ≤
      p ^ m := by
  let moment : ℚ := finiteAverage (fun seed : DSeed × TSeed =>
    |B.vertexRestrictionContribution vertex (2 * m)
      (D seed.1) (T seed.2)|)
  have hmomentNonneg : 0 ≤ moment := by
    apply finiteAverage_nonneg
    intro seed
    exact abs_nonneg _
  have hpowNonneg : 0 ≤ p ^ m := pow_nonneg hp m
  have hsquareRaw : moment ^ 2 ≤ p ^ (2 * m) := by
    simpa only [moment, vertexRestrictionContribution] using
      (B.prefixSlice_mul_suffixLaplacian_restriction_absMoment_sq_le_pow
        (k := 2 * m) hreadOnce vertex D T p hp hDOrthogonal hTMask)
  have hsquare : moment ^ 2 ≤ (p ^ m) ^ 2 := by
    calc
      moment ^ 2 ≤ p ^ (2 * m) := hsquareRaw
      _ = (p ^ m) ^ 2 := by rw [Nat.mul_comm 2 m, pow_mul]
  change moment ≤ p ^ m
  exact le_of_sq_le_sq_of_nonneg hmomentNonneg hpowNonneg hsquare

/-! ## The honest sum over all vertices -/

/-- The average absolute value of the displayed sum of all per-vertex
contributions is at most `card(Vertex) * p ^ m` at even degree `2 * m`.

This theorem uses only the exact finite-sum triangle inequality and the common
per-vertex hypotheses.  The separate regrouping module proves when this
displayed sum equals the signed masked average of the program's high-degree
Fourier tail. -/
theorem vertexRestrictionContribution_sum_evenDegree_absMoment_le_card_mul_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n (2 * m),
        ∀ beta ∈ degreeSupports n (2 * m),
          alpha ≠ beta →
            finiteAverage (fun d : DSeed =>
              FiniteBooleanFourier.character alpha (D d) *
                FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n (2 * m),
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ (2 * m)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      |∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex (2 * m)
          (D seed.1) (T seed.2)|) ≤
      (Fintype.card B.Vertex : ℚ) * p ^ m := by
  refine finiteAverage_abs_fintype_sum_le_card_mul_of_bound
    (Seed := DSeed × TSeed) (Index := B.Vertex)
    (fun vertex seed =>
      B.vertexRestrictionContribution vertex (2 * m)
        (D seed.1) (T seed.2)) (p ^ m) ?_
  intro vertex
  exact B.vertexRestrictionContribution_evenDegree_absMoment_le_pow
    hreadOnce vertex D T p hp hDOrthogonal hTMask

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
