import Pnp4.Frontier.OneTapeMagnification.FiniteResidualAcceptedModelCount
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual rejected inputs as an exact complementary count

For a fixed base and mask, the frozen cylinder contains exactly one input for
each assignment to the live coordinates.  Its accepting inputs are in
bijection with the compatible `AcceptedModel`s of an unambiguous FBDD, while
the remaining inputs are rejected.  Consequently the normalized rejected
count is exactly one minus the normalized residual accepted-model count.

This is only a numeric complement bridge.  A rejected input has no
`AcceptedModel`, hence no canonical accepting trace is supplied here; in
particular, this file proves no reverse-LCP or capacity statement for rejected
inputs and does not construct a nonaccepting compiler.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteResidualAcceptedModelCount
open DPTWStructuredFieldCoordinatePrimitive

namespace FiniteUnambiguousFBDD

local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-! ## The frozen cylinder -/

/-- All inputs which agree with the base on the coordinates frozen by the
mask. -/
def frozenCompatibleInputs {n : Nat} (base mask : Fin n -> Bool) :
    Finset (Fin n -> Bool) :=
  Finset.univ.filter fun input => FrozenCompatible input base mask

@[simp]
theorem mem_frozenCompatibleInputs {n : Nat} (base mask input : Fin n -> Bool) :
    input ∈ frozenCompatibleInputs base mask <->
      FrozenCompatible input base mask := by
  simp [frozenCompatibleInputs]

/-- The canonical global input obtained from an assignment to precisely the
live coordinates. -/
def frozenInputOfLivePattern {n : Nat} (base mask : Fin n -> Bool)
    (pattern : LocalAssignment (liveSupport mask)) : Fin n -> Bool :=
  maskedInput base mask (extendAssignment (liveSupport mask) pattern)

/-- Different live patterns produce different inputs in the frozen
cylinder. -/
theorem frozenInputOfLivePattern_injective {n : Nat}
    (base mask : Fin n -> Bool) :
    Function.Injective (frozenInputOfLivePattern base mask) := by
  intro left right heq
  have hleft :=
    ((maskedInput_eq_target_iff
      (frozenInputOfLivePattern base mask left) base mask
      (extendAssignment (liveSupport mask) left)).1 rfl).2
  have hright :=
    ((maskedInput_eq_target_iff
      (frozenInputOfLivePattern base mask left) base mask
      (extendAssignment (liveSupport mask) right)).1 heq.symm).2
  simpa using hleft.trans hright.symm

/-- Every compatible input, and only such an input, is obtained from its
unique live pattern. -/
theorem image_univ_frozenInputOfLivePattern_eq_frozenCompatibleInputs
    {n : Nat} (base mask : Fin n -> Bool) :
    (Finset.univ : Finset (LocalAssignment (liveSupport mask))).image
        (frozenInputOfLivePattern base mask) =
      frozenCompatibleInputs base mask := by
  classical
  ext input
  constructor
  · intro hinput
    rcases Finset.mem_image.1 hinput with ⟨pattern, _hpattern, rfl⟩
    apply (mem_frozenCompatibleInputs base mask _).2
    exact
      ((maskedInput_eq_target_iff
        (frozenInputOfLivePattern base mask pattern) base mask
        (extendAssignment (liveSupport mask) pattern)).1 rfl).1
  · intro hinput
    have hcompatible :=
      (mem_frozenCompatibleInputs base mask input).1 hinput
    apply Finset.mem_image.2
    refine ⟨livePattern input base mask, Finset.mem_univ _, ?_⟩
    exact (maskedInput_eq_target_iff input base mask
      (extendAssignment (liveSupport mask)
        (livePattern input base mask))).2
      ⟨hcompatible, restrictAssignment_extendAssignment _ _⟩

/-- A frozen cylinder has exactly `2^|live|` inputs. -/
theorem frozenCompatibleInputs_card {n : Nat}
    (base mask : Fin n -> Bool) :
    (frozenCompatibleInputs base mask).card =
      2 ^ (liveSupport mask).card := by
  classical
  calc
    (frozenCompatibleInputs base mask).card =
        ((Finset.univ : Finset (LocalAssignment (liveSupport mask))).image
          (frozenInputOfLivePattern base mask)).card := by
            rw [image_univ_frozenInputOfLivePattern_eq_frozenCompatibleInputs]
    _ = (Finset.univ : Finset
        (LocalAssignment (liveSupport mask))).card :=
      Finset.card_image_of_injective _
        (frozenInputOfLivePattern_injective base mask)
    _ = 2 ^ (liveSupport mask).card := by
      simp [Fintype.card_bool]

/-! ## Accepting and rejected parts of the cylinder -/

/-- Compatible accepting inputs, stated as literal inputs rather than as
accepted-model subtypes. -/
def compatibleAcceptedInputs {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : Finset (Fin n -> Bool) :=
  (frozenCompatibleInputs base mask).filter B.Accepts

@[simp]
theorem mem_compatibleAcceptedInputs {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask input : Fin n -> Bool) :
    input ∈ B.compatibleAcceptedInputs base mask <->
      FrozenCompatible input base mask ∧ B.Accepts input := by
  simp [compatibleAcceptedInputs]

/-- Compatible rejected inputs in the fixed frozen cylinder. -/
def compatibleRejectedInputs {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : Finset (Fin n -> Bool) :=
  (frozenCompatibleInputs base mask).filter fun input => ¬ B.Accepts input

@[simp]
theorem mem_compatibleRejectedInputs {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask input : Fin n -> Bool) :
    input ∈ B.compatibleRejectedInputs base mask <->
      FrozenCompatible input base mask ∧ ¬ B.Accepts input := by
  simp [compatibleRejectedInputs]

/-- Literal number of compatible rejected inputs. -/
def residualRejectedInputCount {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : Nat :=
  (B.compatibleRejectedInputs base mask).card

/-- Forgetting the acceptance proof maps compatible accepted models exactly
onto the compatible accepting inputs. -/
theorem image_compatibleAcceptedModels_eq_compatibleAcceptedInputs
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    (B.compatibleAcceptedModels base mask).image
        (fun accepted : B.AcceptedModel => accepted.1) =
      B.compatibleAcceptedInputs base mask := by
  classical
  ext input
  constructor
  · intro hinput
    rcases Finset.mem_image.1 hinput with
      ⟨accepted, haccepted, rfl⟩
    apply (B.mem_compatibleAcceptedInputs base mask accepted.1).2
    exact ⟨(B.mem_compatibleAcceptedModels base mask accepted).1 haccepted,
      accepted.property⟩
  · intro hinput
    have hproperties :=
      (B.mem_compatibleAcceptedInputs base mask input).1 hinput
    let accepted : B.AcceptedModel := ⟨input, hproperties.2⟩
    apply Finset.mem_image.2
    refine ⟨accepted, ?_, rfl⟩
    exact (B.mem_compatibleAcceptedModels base mask accepted).2 hproperties.1

/-- The input presentation and the existing `AcceptedModel` presentation
have the same cardinality. -/
theorem compatibleAcceptedInputs_card_eq_residualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    (B.compatibleAcceptedInputs base mask).card =
      B.residualAcceptedModelCount base mask := by
  classical
  calc
    (B.compatibleAcceptedInputs base mask).card =
        ((B.compatibleAcceptedModels base mask).image
          (fun accepted : B.AcceptedModel => accepted.1)).card := by
            rw [image_compatibleAcceptedModels_eq_compatibleAcceptedInputs]
    _ = (B.compatibleAcceptedModels base mask).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    _ = B.residualAcceptedModelCount base mask := rfl

/-- The accepting and rejected counts partition the entire frozen cylinder. -/
theorem residualAcceptedModelCount_add_residualRejectedInputCount_eq_pow_live
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    B.residualAcceptedModelCount base mask +
        B.residualRejectedInputCount base mask =
      2 ^ (liveSupport mask).card := by
  classical
  calc
    B.residualAcceptedModelCount base mask +
        B.residualRejectedInputCount base mask =
      (B.compatibleAcceptedInputs base mask).card +
        (B.compatibleRejectedInputs base mask).card := by
          rw [B.compatibleAcceptedInputs_card_eq_residualAcceptedModelCount]
          rfl
    _ = (frozenCompatibleInputs base mask).card := by
      simpa [compatibleAcceptedInputs, compatibleRejectedInputs] using
        (Finset.filter_card_add_filter_neg_card_eq_card
          (s := frozenCompatibleInputs base mask) B.Accepts)
    _ = 2 ^ (liveSupport mask).card := frozenCompatibleInputs_card base mask

/-- Exact normalized compatible rejected-input count. -/
noncomputable def normalizedResidualRejectedInputCount {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) : Rat :=
  (B.residualRejectedInputCount base mask : Rat) /
    (2 : Rat) ^ (liveSupport mask).card

/-- The normalized rejected count is the exact numeric complement of the
normalized residual accepted-model count. -/
theorem normalizedResidualRejectedInputCount_eq_one_sub
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    B.normalizedResidualRejectedInputCount base mask =
      1 - B.normalizedResidualAcceptedModelCount base mask := by
  have hcount :=
    B.residualAcceptedModelCount_add_residualRejectedInputCount_eq_pow_live
      base mask
  have hcountRat :
      (B.residualAcceptedModelCount base mask : Rat) +
          (B.residualRejectedInputCount base mask : Rat) =
        (2 : Rat) ^ (liveSupport mask).card := by
    exact_mod_cast hcount
  unfold normalizedResidualRejectedInputCount
    normalizedResidualAcceptedModelCount
  have hdenom : (2 : Rat) ^ (liveSupport mask).card ≠ 0 := by
    positivity
  field_simp
  linarith

/-! ## Fixed-mask averaging -/

/-- Averaging over any nonempty finite base source preserves the exact
complement identity. -/
theorem finiteAverage_normalizedResidualRejectedInputCount_eq_one_sub
    {Seed : Type*} [Fintype Seed] [Nonempty Seed] {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base : Seed -> Fin n -> Bool)
    (mask : Fin n -> Bool) :
    finiteAverage (fun seed =>
        B.normalizedResidualRejectedInputCount (base seed) mask) =
      1 - finiteAverage (fun seed =>
        B.normalizedResidualAcceptedModelCount (base seed) mask) := by
  calc
    finiteAverage (fun seed =>
        B.normalizedResidualRejectedInputCount (base seed) mask) =
      finiteAverage (fun seed =>
        1 - B.normalizedResidualAcceptedModelCount (base seed) mask) := by
          apply finiteAverage_congr
          intro seed
          exact B.normalizedResidualRejectedInputCount_eq_one_sub
            (base seed) mask
    _ = finiteAverage (fun _seed : Seed => (1 : Rat)) -
        finiteAverage (fun seed =>
          B.normalizedResidualAcceptedModelCount (base seed) mask) := by
            rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]
    _ = 1 - finiteAverage (fun seed =>
        B.normalizedResidualAcceptedModelCount (base seed) mask) := by
      rw [FiniteBooleanPerVertexRestrictionBound.finiteAverage_const]

/-- Fixed-mask specialization to the structured unbiased common-seed
coordinate primitive. -/
theorem fixedMaskStructuredAverage_normalizedResidualRejectedInputCount_eq_one_sub
    (n m : Nat) (hn : 0 < n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (mask : Fin (2 ^ n) -> Bool) :
    finiteAverage (fun seed : Fin (structuredIndependence m * n) -> Bool =>
        B.normalizedResidualRejectedInputCount
          ((structuredUnbiasedPrimitive n m hn).generate seed) mask) =
      1 - finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          B.normalizedResidualAcceptedModelCount
            ((structuredUnbiasedPrimitive n m hn).generate seed) mask) := by
  exact B.finiteAverage_normalizedResidualRejectedInputCount_eq_one_sub
    (fun seed => (structuredUnbiasedPrimitive n m hn).generate seed) mask

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
