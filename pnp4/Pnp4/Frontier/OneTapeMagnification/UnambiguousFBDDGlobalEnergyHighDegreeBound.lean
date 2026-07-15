import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDGlobalEnergyBound
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundHighDegreeBound

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Program-level global-energy high-degree bound

`UnambiguousFBDDGlobalEnergyBound` controls the exact sum of the vertex
restriction contributions, while `UnambiguousFBDDOneRoundHighDegreeBound`
identifies that sum with the masked uniform average of the program's actual
high-degree Fourier tail.  This module performs the missing composition.

The result improves the earlier `L¹` estimate by retaining the total
degree-`k` compatible-prefix Fourier energy.  It is still not size-free: the
factor `Fintype.card B.Vertex` is exactly the Cauchy--Schwarz loss isolated in
the underlying global-energy theorem.
-/

namespace FiniteUnambiguousFBDD

open scoped BigOperators
open FiniteBooleanRestrictionMoment

/-- Program-level second-moment estimate obtained by composing exact
high-tail regrouping with the global compatible-prefix energy bound. -/
theorem four_mul_ratHighDegreeFourierTail_maskedAverage_secondMoment_le
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
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
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail B.ratAcceptanceIndicator k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k := by
  calc
    4 * finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail B.ratAcceptanceIndicator k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      4 * finiteAverage (fun seed : DSeed × TSeed =>
        (∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)) ^ 2) := by
        congr 1
        apply finiteAverage_congr
        intro seed
        rw [B.ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
          hreadOnce hunambiguous hreadsAll]
    _ ≤ (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k :=
      B.four_mul_vertexRestrictionContribution_sum_secondMoment_le
        hreadOnce D T p hDOrthogonal hTMask

/-- Program-level square bound for the mean absolute signed high-tail
average.  This is the directly composable form used by later fooling bounds. -/
theorem four_mul_ratHighDegreeFourierTail_maskedAverage_absMoment_sq_le
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
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
      |finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail B.ratAcceptanceIndicator k
          (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k := by
  calc
    4 * (finiteAverage (fun seed : DSeed × TSeed =>
        |finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail B.ratAcceptanceIndicator k
            (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 =
      4 * (finiteAverage (fun seed : DSeed × TSeed =>
        |∑ vertex : B.Vertex,
          B.vertexRestrictionContribution vertex k
            (D seed.1) (T seed.2)|)) ^ 2 := by
        congr 2
        apply finiteAverage_congr
        intro seed
        rw [B.ratHighDegreeFourierTail_maskedAverage_eq_sum_vertexRestrictionContribution
          hreadOnce hunambiguous hreadsAll]
    _ ≤ (Fintype.card B.Vertex : ℚ) * p ^ k *
        B.prefixDegreeEnergySum k :=
      B.four_mul_vertexRestrictionContribution_sum_absMoment_sq_le
        hreadOnce D T p hDOrthogonal hTMask

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

/-- Global-energy second-moment bound for the mandatory canonical uFBDD. -/
theorem mandatoryCanonicalUFBDD_four_mul_ratHighDegreeFourierTail_maskedAverage_secondMoment_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n timeSteps blockSize k : Nat) (hblockSize : 0 < blockSize)
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
        ∀ beta ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
          alpha ≠ beta →
            FiniteBooleanRestrictionMoment.finiteAverage
              (fun d : DSeed =>
                FiniteBooleanFourier.character alpha (D d) *
                  FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
        FiniteBooleanRestrictionMoment.finiteAverage
          (fun t : TSeed =>
            FiniteBooleanRestrictionMoment.maskAllZeroIndicator alpha (T t)) =
          p ^ k) :
    4 * FiniteBooleanRestrictionMoment.finiteAverage
        (fun seed : DSeed × TSeed =>
          (FiniteBooleanRestrictionMoment.finiteAverage
            (fun uniform : Fin n → Bool =>
              FiniteUnambiguousFBDD.ratHighDegreeFourierTail
                (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator
                k
                (FiniteBooleanRestrictionMoment.maskedInput
                  (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      (Fintype.card
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).Vertex : ℚ) *
        p ^ k *
          (mandatoryCanonicalUFBDD machine n timeSteps blockSize).prefixDegreeEnergySum k := by
  apply
    FiniteUnambiguousFBDD.four_mul_ratHighDegreeFourierTail_maskedAverage_secondMoment_le
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
      machine n timeSteps blockSize
  · exact mandatoryCanonicalUFBDD_isUnambiguous
      machine n timeSteps blockSize hblockSize
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n timeSteps blockSize currentInput path
  · exact hDOrthogonal
  · exact hTMask

/-- Global-energy absolute-moment bound for the mandatory canonical uFBDD. -/
theorem mandatoryCanonicalUFBDD_four_mul_ratHighDegreeFourierTail_maskedAverage_absMoment_sq_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n timeSteps blockSize k : Nat) (hblockSize : 0 < blockSize)
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
        ∀ beta ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
          alpha ≠ beta →
            FiniteBooleanRestrictionMoment.finiteAverage
              (fun d : DSeed =>
                FiniteBooleanFourier.character alpha (D d) *
                  FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ FiniteBooleanRestrictionMoment.degreeSupports n k,
        FiniteBooleanRestrictionMoment.finiteAverage
          (fun t : TSeed =>
            FiniteBooleanRestrictionMoment.maskAllZeroIndicator alpha (T t)) =
          p ^ k) :
    4 * (FiniteBooleanRestrictionMoment.finiteAverage
        (fun seed : DSeed × TSeed =>
          |FiniteBooleanRestrictionMoment.finiteAverage
            (fun uniform : Fin n → Bool =>
              FiniteUnambiguousFBDD.ratHighDegreeFourierTail
                (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator
                k
                (FiniteBooleanRestrictionMoment.maskedInput
                  (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      (Fintype.card
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).Vertex : ℚ) *
        p ^ k *
          (mandatoryCanonicalUFBDD machine n timeSteps blockSize).prefixDegreeEnergySum k := by
  apply
    FiniteUnambiguousFBDD.four_mul_ratHighDegreeFourierTail_maskedAverage_absMoment_sq_le
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
      machine n timeSteps blockSize
  · exact mandatoryCanonicalUFBDD_isUnambiguous
      machine n timeSteps blockSize hblockSize
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n timeSteps blockSize currentInput path
  · exact hDOrthogonal
  · exact hTMask

end OneTapeMagnification
end Frontier
end Pnp4
