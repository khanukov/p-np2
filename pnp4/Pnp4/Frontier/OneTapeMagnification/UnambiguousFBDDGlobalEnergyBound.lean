import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDVertexSumRestrictionBound
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Global-energy bound for the uFBDD vertex decomposition

The earlier per-vertex argument discards the Fourier energy of each compatible
prefix indicator and then applies an `L¹` triangle inequality over vertices.
This module retains that energy.  Cauchy--Schwarz over the vertex set and the
exact restriction second-moment identity give a global `L²` estimate.

The factor `4` records the sharp pointwise bound `|suffixLaplacian| ≤ 1 / 2`.
The factor `Fintype.card B.Vertex` remains: no orthogonality between different
vertices is asserted or used here.

The theorem below concerns the displayed sum of vertex contributions.  Using
that sum as the actual program high-degree tail is a separate regrouping step;
the existing regrouping theorem additionally assumes semantic unambiguity and
that every accepting path reads every input.
-/

namespace FiniteUnambiguousFBDD

open scoped BigOperators
open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanFourierEnergy

/-- Total degree-`k` Fourier energy of all compatible-prefix indicators. -/
noncomputable def prefixDegreeEnergySum {n : Nat}
    (B : FiniteUnambiguousFBDD n) (k : Nat) : ℚ :=
  ∑ vertex : B.Vertex,
    degreeEnergy k
      (fun input => B.ratCompatiblePrefixIndicator input vertex)

/-- For one fixed vertex and restriction, the sharp `1 / 2` suffix bound
controls the square of the product contribution by one quarter of the square
of the restricted prefix slice. -/
theorem four_mul_vertexRestrictionContribution_sq_le_prefixAverage_sq
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) (vertex : B.Vertex)
    (base mask : Fin n → Bool) :
    4 * (B.vertexRestrictionContribution vertex k base mask) ^ 2 ≤
      (finiteAverage (fun uniform : Fin n → Bool =>
        B.ratCompatiblePrefixHomogeneousSlice vertex k
          (maskedInput base mask uniform))) ^ 2 := by
  have hfactor :
      B.vertexRestrictionContribution vertex k base mask =
        finiteAverage (fun uniform : Fin n → Bool =>
          B.ratCompatiblePrefixHomogeneousSlice vertex k
            (maskedInput base mask uniform)) *
        finiteAverage (fun uniform : Fin n → Bool =>
          B.suffixLaplacian vertex (maskedInput base mask uniform)) := by
    exact finiteAverage_mul_maskedInput_eq_mul
      (B.ratCompatiblePrefixHomogeneousSlice_dependsOnlyOn_preVars vertex)
      (B.suffixLaplacian_dependsOnlyOn_postVars vertex)
      (B.preVars_disjoint_postVars hreadOnce vertex) base mask
  let prefixAverage : ℚ :=
    finiteAverage (fun uniform : Fin n → Bool =>
      B.ratCompatiblePrefixHomogeneousSlice vertex k
        (maskedInput base mask uniform))
  let suffixAverage : ℚ :=
    finiteAverage (fun uniform : Fin n → Bool =>
      B.suffixLaplacian vertex (maskedInput base mask uniform))
  have hsuffix : |suffixAverage| ≤ (1 : ℚ) / 2 := by
    exact B.abs_finiteAverage_suffixLaplacian_maskedInput_le_half
      vertex base mask
  have hsuffixSq : 4 * suffixAverage ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg suffixAverage]
  rw [hfactor]
  change 4 * (prefixAverage * suffixAverage) ^ 2 ≤ prefixAverage ^ 2
  calc
    4 * (prefixAverage * suffixAverage) ^ 2 =
        (4 * suffixAverage ^ 2) * prefixAverage ^ 2 := by ring
    _ ≤ 1 * prefixAverage ^ 2 :=
      mul_le_mul_of_nonneg_right hsuffixSq (sq_nonneg prefixAverage)
    _ = prefixAverage ^ 2 := one_mul _

/-- Exact global second-moment estimate for the displayed sum of vertex
restriction contributions.  It retains the aggregate prefix Fourier energy
instead of bounding every vertex energy by one.

The only source-distribution assumptions are the explicit degree-`k`
orthogonality and exact mask-survival identities. -/
theorem four_mul_vertexRestrictionContribution_sum_secondMoment_le
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    4 * finiteAverage (fun seed : DSeed × TSeed =>
      (∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex k
          (D seed.1) (T seed.2)) ^ 2) ≤
      (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k := by
  have hpointwise (seed : DSeed × TSeed) :
      4 * (∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex k
          (D seed.1) (T seed.2)) ^ 2 ≤
        (Fintype.card B.Vertex : ℚ) *
          ∑ vertex : B.Vertex,
            (finiteAverage (fun uniform : Fin n → Bool =>
              B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 := by
    have hsum :
        (∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2 ≤
          (Fintype.card B.Vertex : ℚ) *
            ∑ vertex : B.Vertex,
              (B.vertexRestrictionContribution vertex k
                (D seed.1) (T seed.2)) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset B.Vertex))
          (f := fun vertex =>
            B.vertexRestrictionContribution vertex k
              (D seed.1) (T seed.2)))
    have hcomponents :
        4 * (∑ vertex : B.Vertex,
          (B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2) ≤
          ∑ vertex : B.Vertex,
            (finiteAverage (fun uniform : Fin n → Bool =>
              B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro vertex _
      exact B.four_mul_vertexRestrictionContribution_sq_le_prefixAverage_sq
        hreadOnce vertex (D seed.1) (T seed.2)
    calc
      4 * (∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2 ≤
          4 * ((Fintype.card B.Vertex : ℚ) *
            ∑ vertex : B.Vertex,
              (B.vertexRestrictionContribution vertex k
                (D seed.1) (T seed.2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (Fintype.card B.Vertex : ℚ) *
          (4 * ∑ vertex : B.Vertex,
            (B.vertexRestrictionContribution vertex k
              (D seed.1) (T seed.2)) ^ 2) := by ring
      _ ≤ (Fintype.card B.Vertex : ℚ) *
          ∑ vertex : B.Vertex,
            (finiteAverage (fun uniform : Fin n → Bool =>
              B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 :=
        mul_le_mul_of_nonneg_left hcomponents (by positivity)
  have hprefixSecondMoment (vertex : B.Vertex) :
      finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          B.ratCompatiblePrefixHomogeneousSlice vertex k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
        p ^ k * degreeEnergy k
          (fun input => B.ratCompatiblePrefixIndicator input vertex) := by
    simpa only [ratCompatiblePrefixHomogeneousSlice, degreeEnergy] using
      (homogeneousPolynomial_restriction_secondMoment_eq
        D T p
        (FiniteBooleanFourier.coefficient (fun input =>
          B.ratCompatiblePrefixIndicator input vertex))
        hDOrthogonal hTMask)
  calc
    4 * finiteAverage (fun seed : DSeed × TSeed =>
        (∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        4 * (∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2) := by
      rw [finiteAverage_const_mul]
    _ ≤ finiteAverage (fun seed : DSeed × TSeed =>
        (Fintype.card B.Vertex : ℚ) *
          ∑ vertex : B.Vertex,
            (finiteAverage (fun uniform : Fin n → Bool =>
              B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) :=
      finiteAverage_mono hpointwise
    _ = (Fintype.card B.Vertex : ℚ) *
        ∑ vertex : B.Vertex,
          finiteAverage (fun seed : DSeed × TSeed =>
            (finiteAverage (fun uniform : Fin n → Bool =>
              B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) := by
      rw [finiteAverage_const_mul, finiteAverage_finset_sum]
    _ = (Fintype.card B.Vertex : ℚ) *
        ∑ vertex : B.Vertex,
          (p ^ k * degreeEnergy k
            (fun input => B.ratCompatiblePrefixIndicator input vertex)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro vertex _
      exact hprefixSecondMoment vertex
    _ = (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k := by
      simp only [prefixDegreeEnergySum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro vertex _
      ring

/-- The square of the mean absolute vertex sum is bounded by the same global
energy expression, by Cauchy--Schwarz in the restriction seed. -/
theorem four_mul_vertexRestrictionContribution_sum_absMoment_sq_le
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    4 * (finiteAverage (fun seed : DSeed × TSeed =>
      |∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex k
          (D seed.1) (T seed.2)|)) ^ 2 ≤
      (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k := by
  calc
    4 * (finiteAverage (fun seed : DSeed × TSeed =>
        |∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)|)) ^ 2 ≤
        4 * finiteAverage (fun seed : DSeed × TSeed =>
          (∑ vertex : B.Vertex,
            B.vertexRestrictionContribution vertex k
              (D seed.1) (T seed.2)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (finiteAverage_abs_sq_le_average_sq (fun seed : DSeed × TSeed =>
          ∑ vertex : B.Vertex,
            B.vertexRestrictionContribution vertex k
              (D seed.1) (T seed.2))) (by norm_num)
    _ ≤ (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k :=
      B.four_mul_vertexRestrictionContribution_sum_secondMoment_le
        hreadOnce D T p hDOrthogonal hTMask

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
