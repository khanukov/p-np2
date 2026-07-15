import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDHighDegreeRegrouping
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDVertexSumRestrictionBound

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Program-level one-round high-degree bound for finite uFBDDs

This module combines two previously separate facts:

* the exact pointwise regrouping of the high-degree Fourier tail as
  `∑ vertex, H_vertex * G_vertex`; and
* the restriction-moment bound for the sum of the corresponding masked
  uniform averages.

The resulting theorem controls the absolute value of the **signed uniform
average** of the degree-`> 2 * m` tail after one masked restriction.  It does
not bound the uniform average of the pointwise absolute tail, cancel the
low-degree Fourier part, or establish a full one-round fooling theorem.
-/

namespace FiniteUnambiguousFBDD

open scoped BigOperators
open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanVertexSumRestrictionBound

/-! ## Exact masked regrouping after the uniform fill -/

/-- Averaging the exact pointwise high-degree regrouping over the uniform
fill commutes with the finite vertex sum.  Thus the signed masked high-degree
average is exactly the sum of the already-defined per-vertex restriction
contributions. -/
theorem ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      ratHighDegreeFourierTail B.ratAcceptanceIndicator k
        (maskedInput base mask uniform)) =
      ∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex k base mask := by
  calc
    finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail B.ratAcceptanceIndicator k
          (maskedInput base mask uniform)) =
        finiteAverage (fun uniform : Fin n → Bool =>
          ∑ vertex : B.Vertex,
            B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput base mask uniform) *
              B.suffixLaplacian vertex
                (maskedInput base mask uniform)) := by
      apply finiteAverage_congr
      intro uniform
      exact
        B.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
          hreadOnce hunambiguous hreadsAll (maskedInput base mask uniform)
    _ = ∑ vertex : B.Vertex,
        B.vertexRestrictionContribution vertex k base mask := by
      simpa [vertexRestrictionContribution] using
        (finiteAverage_finset_sum
          (Seed := Fin n → Bool)
          (Finset.univ : Finset B.Vertex)
          (fun vertex uniform =>
            B.ratCompatiblePrefixHomogeneousSlice vertex k
                (maskedInput base mask uniform) *
              B.suffixLaplacian vertex
                (maskedInput base mask uniform)))

/-! ## Program-level even-degree high-tail estimate -/

/-- Honest program-level consequence for one masked restriction round.

At cutoff `2 * m`, the outer average over the `D` and `T` seeds of the
absolute signed uniform-average high-degree tail is at most
`card(Vertex) * p ^ m`.  Besides the syntactic uFBDD assumptions, the theorem
retains the exact degree-`2 * m` character-orthogonality and mask-survival
hypotheses used by the underlying restriction moment bound. -/
theorem ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
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
      |finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail B.ratAcceptanceIndicator (2 * m)
          (maskedInput (D seed.1) (T seed.2) uniform))|) ≤
      (Fintype.card B.Vertex : ℚ) * p ^ m := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        |finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail B.ratAcceptanceIndicator (2 * m)
            (maskedInput (D seed.1) (T seed.2) uniform))|) =
        finiteAverage (fun seed : DSeed × TSeed =>
          |∑ vertex : B.Vertex,
            B.vertexRestrictionContribution vertex (2 * m)
              (D seed.1) (T seed.2)|) := by
      apply finiteAverage_congr
      intro seed
      rw [B.ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
        hreadOnce hunambiguous hreadsAll]
    _ ≤ (Fintype.card B.Vertex : ℚ) * p ^ m :=
      B.vertexRestrictionContribution_sum_evenDegree_absMoment_le_card_mul_pow
        hreadOnce D T p hp hDOrthogonal hTMask

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

/-- Exact masked high-degree regrouping for the mandatory canonical uFBDD. -/
theorem mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n timeSteps blockSize k : Nat) (hblockSize : 0 < blockSize)
    (base mask : Fin n → Bool) :
    FiniteBooleanRestrictionMoment.finiteAverage
        (fun uniform : Fin n → Bool =>
          FiniteUnambiguousFBDD.ratHighDegreeFourierTail
            (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator
            k (FiniteBooleanRestrictionMoment.maskedInput base mask uniform)) =
      ∑ vertex :
          (mandatoryCanonicalUFBDD machine n timeSteps blockSize).Vertex,
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).vertexRestrictionContribution
          vertex k base mask := by
  apply
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
      machine n timeSteps blockSize
  · exact mandatoryCanonicalUFBDD_isUnambiguous
      machine n timeSteps blockSize hblockSize
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n timeSteps blockSize currentInput path

/-- Program-level one-round even-degree high-tail bound for the mandatory
canonical uFBDD.  This remains a high-degree-only statement: no low-degree
cancellation or iterative restriction claim is included. -/
theorem mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n timeSteps blockSize m : Nat) (hblockSize : 0 < blockSize)
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hDOrthogonal :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n (2 * m),
        ∀ beta ∈ FiniteBooleanRestrictionMoment.degreeSupports n (2 * m),
          alpha ≠ beta →
            FiniteBooleanRestrictionMoment.finiteAverage
              (fun d : DSeed =>
                FiniteBooleanFourier.character alpha (D d) *
                  FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n (2 * m),
        FiniteBooleanRestrictionMoment.finiteAverage
          (fun t : TSeed =>
            FiniteBooleanRestrictionMoment.maskAllZeroIndicator alpha (T t)) =
          p ^ (2 * m)) :
    FiniteBooleanRestrictionMoment.finiteAverage
        (fun seed : DSeed × TSeed =>
          |FiniteBooleanRestrictionMoment.finiteAverage
            (fun uniform : Fin n → Bool =>
              FiniteUnambiguousFBDD.ratHighDegreeFourierTail
                (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator
                (2 * m)
                (FiniteBooleanRestrictionMoment.maskedInput
                  (D seed.1) (T seed.2) uniform))|) ≤
      (Fintype.card
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).Vertex : ℚ) *
        p ^ m := by
  apply
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
      machine n timeSteps blockSize
  · exact mandatoryCanonicalUFBDD_isUnambiguous
      machine n timeSteps blockSize hblockSize
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n timeSteps blockSize currentInput path
  · exact hp
  · exact hDOrthogonal
  · exact hTMask

end OneTapeMagnification
end Frontier
end Pnp4
