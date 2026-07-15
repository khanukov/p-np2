import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyAcceptedInputFourier

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual accepted-model mass under a Boolean restriction

The accepted-input pair expansion is most useful geometrically when its
Fourier expression is translated back to residual model mass.  For a fixed
base and mask, `residualAcceptedMass` is the exact probability that a uniform
completion of the live coordinates is accepted.  The strict high-degree tail
is exactly this residual mass minus its low-degree Fourier predictor.

This is the semantic insertion surface for a last-common-prefix or residual
model-count argument.  The identities below are unconditional finite
equalities.  They do not assert concentration of residual mass and therefore
do not prove the missing small-seed selector correlation bound.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanFullIndependenceRestriction
open FiniteUnambiguousFBDD
open DPTWStructuredFullFieldCorrelation

namespace FiniteBooleanResidualMass

/-- Exact conditional average of an arbitrary rational Boolean-cube function
under one fixed affine mask. -/
noncomputable def maskedAverage {n : Nat}
    (f : (Fin n -> Bool) -> Rat) (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    f (maskedInput base mask uniform))

/-- Conditional low-degree Fourier predictor under the same fixed mask. -/
noncomputable def maskedLowDegreePredictor {n : Nat}
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    ratLowDegreeFourierPart f cutoff (maskedInput base mask uniform))

/-- The conditional high tail is exactly residual conditional mass minus its
low-degree predictor. -/
theorem highTailAverage_eq_maskedAverage_sub_lowDegreePredictor
    {n : Nat} (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    finiteAverage (fun uniform : Fin n -> Bool =>
      ratHighDegreeFourierTail f cutoff
        (maskedInput base mask uniform)) =
      maskedAverage f base mask -
        maskedLowDegreePredictor f cutoff base mask := by
  unfold maskedAverage maskedLowDegreePredictor
  rw [← finiteAverage_sub]
  apply finiteAverage_congr
  intro uniform
  exact ratHighDegreeFourierTail_eq_sub_lowDegreePart f
    (maskedInput base mask uniform)

/-- Second-moment form of the generic residual-mass identity. -/
theorem deviation_secondMoment_eq_highTailSecondMoment
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (maskedAverage f (D seed.1) (T seed.2) -
        maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n -> Bool =>
          ratHighDegreeFourierTail f cutoff
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) := by
  apply finiteAverage_congr
  intro seed
  rw [highTailAverage_eq_maskedAverage_sub_lowDegreePredictor]

end FiniteBooleanResidualMass

namespace FiniteUnambiguousFBDD

/-- Inputs accepted by an arbitrary finite uFBDD. -/
def AcceptedModel {n : Nat} (B : FiniteUnambiguousFBDD n) : Type :=
  {input : Fin n -> Bool // B.Accepts input}

instance acceptedModelFintype {n : Nat} (B : FiniteUnambiguousFBDD n) :
    Fintype B.AcceptedModel := by
  classical
  unfold AcceptedModel
  infer_instance

/-- Point indicator of one input accepted by the uFBDD. -/
noncomputable def ratAcceptedPointIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (input : Fin n -> Bool) : Rat :=
  if input = accepted.1 then 1 else 0

/-- Conditional mass of one accepted input under a fixed mask. -/
noncomputable def acceptedPointMaskedMass {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    B.ratAcceptedPointIndicator accepted (maskedInput base mask uniform))

/-- Sum of the conditional masses of all inputs accepted by the uFBDD. -/
noncomputable def residualAcceptedMass {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) : Rat :=
  ∑ accepted : B.AcceptedModel,
    B.acceptedPointMaskedMass accepted base mask

/-- The uFBDD indicator is exactly the sum of the point indicators of its
accepted inputs.  No path-unambiguity premise is needed for this set-level
identity. -/
theorem ratAcceptanceIndicator_eq_sum_acceptedPoints
    {n : Nat} (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool) :
    B.ratAcceptanceIndicator input =
      ∑ accepted : B.AcceptedModel,
        B.ratAcceptedPointIndicator accepted input := by
  classical
  by_cases haccepts : B.Accepts input
  · let chosen : B.AcceptedModel := ⟨input, haccepts⟩
    unfold ratAcceptanceIndicator
    rw [if_pos haccepts]
    symm
    calc
      (∑ accepted : B.AcceptedModel,
          B.ratAcceptedPointIndicator accepted input) =
          B.ratAcceptedPointIndicator chosen input := by
        apply Finset.sum_eq_single chosen
        · intro accepted _ hne
          have hinput : input ≠ accepted.1 := by
            intro heq
            apply hne
            apply Subtype.ext
            exact heq.symm
          simp [FiniteUnambiguousFBDD.ratAcceptedPointIndicator, hinput]
        · simp
      _ = 1 := by
        simp [FiniteUnambiguousFBDD.ratAcceptedPointIndicator, chosen]
  · unfold ratAcceptanceIndicator
    rw [if_neg haccepts]
    symm
    apply Finset.sum_eq_zero
    intro accepted _
    have hinput : input ≠ accepted.1 := by
      intro heq
      apply haccepts
      simpa [heq] using accepted.2
    simp [FiniteUnambiguousFBDD.ratAcceptedPointIndicator, hinput]

/-- The generic conditional average of the uFBDD indicator is its exact
residual accepted-model mass. -/
theorem maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    FiniteBooleanResidualMass.maskedAverage B.ratAcceptanceIndicator
        base mask =
      B.residualAcceptedMass base mask := by
  classical
  unfold FiniteBooleanResidualMass.maskedAverage residualAcceptedMass
  calc
    finiteAverage (fun uniform : Fin n -> Bool =>
        B.ratAcceptanceIndicator (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n -> Bool =>
        ∑ accepted : B.AcceptedModel,
          B.ratAcceptedPointIndicator accepted
            (maskedInput base mask uniform)) := by
        apply finiteAverage_congr
        intro uniform
        exact B.ratAcceptanceIndicator_eq_sum_acceptedPoints
          (maskedInput base mask uniform)
    _ = ∑ accepted : B.AcceptedModel,
        B.acceptedPointMaskedMass accepted base mask := by
      rw [finiteAverage_fintype_sum]
      rfl

end FiniteUnambiguousFBDD

namespace FiniteLayeredQueryProgramFamily

local instance familyIndexFintypeForResidualMass {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Fintype family.Index :=
  family.indexFintype

/-- Conditional mass of one accepted input after fixing the false-mask
coordinates to `base` and completing all true-mask coordinates uniformly. -/
noncomputable def acceptedPointMaskedMass {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel)
    (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    family.ratAcceptedPointIndicator accepted
      (maskedInput base mask uniform))

/-- Total accepted residual mass under a fixed base and mask.  Unambiguity is
not required: `AcceptedModel` already indexes the inputs accepted by the
Boolean union, rather than component witnesses. -/
noncomputable def residualAcceptedMass {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (base mask : Fin n -> Bool) : Rat :=
  ∑ accepted : family.AcceptedModel,
    family.acceptedPointMaskedMass accepted base mask

/-- Low-degree conditional predictor for one accepted point. -/
noncomputable def acceptedPointLowDegreePredictor {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (cutoff : Nat)
    (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    ratLowDegreeFourierPart
      (family.ratAcceptedPointIndicator accepted) cutoff
      (maskedInput base mask uniform))

/-- Low-degree conditional predictor for the selector indicator. -/
noncomputable def selectorLowDegreePredictor {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (cutoff : Nat)
    (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    ratLowDegreeFourierPart
      family.selectorFBDD.ratAcceptanceIndicator cutoff
      (maskedInput base mask uniform))

/-- The uniform conditional acceptance probability is exactly the sum of the
residual masses of the accepted inputs. -/
theorem selector_maskedAverage_eq_residualAcceptedMass
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (base mask : Fin n -> Bool) :
    finiteAverage (fun uniform : Fin n -> Bool =>
      family.selectorFBDD.ratAcceptanceIndicator
        (maskedInput base mask uniform)) =
      family.residualAcceptedMass base mask := by
  classical
  calc
    finiteAverage (fun uniform : Fin n -> Bool =>
        family.selectorFBDD.ratAcceptanceIndicator
          (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n -> Bool =>
        ∑ accepted : family.AcceptedModel,
          family.ratAcceptedPointIndicator accepted
            (maskedInput base mask uniform)) := by
        apply finiteAverage_congr
        intro uniform
        exact family.selector_ratAcceptanceIndicator_eq_sum_acceptedPoints
          (maskedInput base mask uniform)
    _ = ∑ accepted : family.AcceptedModel,
        family.acceptedPointMaskedMass accepted base mask := by
      rw [finiteAverage_fintype_sum]
      rfl
    _ = family.residualAcceptedMass base mask := rfl

/-- The atomic high-tail contribution is residual point mass minus its exact
low-degree predictor. -/
theorem acceptedPointHighTailAverage_eq_maskedMass_sub_lowDegreePredictor
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    family.acceptedPointHighTailAverage accepted cutoff base mask =
      family.acceptedPointMaskedMass accepted base mask -
        family.acceptedPointLowDegreePredictor accepted cutoff base mask := by
  unfold acceptedPointHighTailAverage acceptedPointMaskedMass
    acceptedPointLowDegreePredictor
  rw [← finiteAverage_sub]
  apply finiteAverage_congr
  intro uniform
  exact ratHighDegreeFourierTail_eq_sub_lowDegreePart
    (family.ratAcceptedPointIndicator accepted)
    (maskedInput base mask uniform)

/-- The selector high tail is exactly the deviation of its residual accepted
mass from the low-degree conditional predictor. -/
theorem selector_highTailAverage_eq_residualAcceptedMass_sub_lowDegreePredictor
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (cutoff : Nat) (base mask : Fin n -> Bool) :
    finiteAverage (fun uniform : Fin n -> Bool =>
      ratHighDegreeFourierTail
        family.selectorFBDD.ratAcceptanceIndicator cutoff
        (maskedInput base mask uniform)) =
      family.residualAcceptedMass base mask -
        family.selectorLowDegreePredictor cutoff base mask := by
  rw [← family.selector_maskedAverage_eq_residualAcceptedMass base mask]
  unfold selectorLowDegreePredictor
  rw [← finiteAverage_sub]
  apply finiteAverage_congr
  intro uniform
  exact ratHighDegreeFourierTail_eq_sub_lowDegreePart
    family.selectorFBDD.ratAcceptanceIndicator
    (maskedInput base mask uniform)

/-- Exact second-moment form of the residual-mass identity.  This is the
quantity that a selector-specific pair charge must bound under the structured
base and mask sources. -/
theorem residualAcceptedMass_deviation_secondMoment_eq_highTailSecondMoment
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (family : FiniteLayeredQueryProgramFamily n) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (family.residualAcceptedMass (D seed.1) (T seed.2) -
        family.selectorLowDegreePredictor cutoff
          (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n -> Bool =>
          ratHighDegreeFourierTail
            family.selectorFBDD.ratAcceptanceIndicator cutoff
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) := by
  apply finiteAverage_congr
  intro seed
  rw [family.selector_highTailAverage_eq_residualAcceptedMass_sub_lowDegreePredictor]

end FiniteLayeredQueryProgramFamily

end

end OneTapeMagnification
end Frontier
end Pnp4
