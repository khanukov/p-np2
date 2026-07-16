import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyResidualModelMass
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual accepted mass as an exact model count

The residual-mass formulation becomes useful to a last-common-prefix or
splice-counting argument only after it is connected to the literal number of
accepted completions.  This file makes that connection without a
concentration hypothesis.

For a fixed mask, `liveSupport` is the set of coordinates filled by the
uniform completion.  An accepted model contributes exactly `2^(-|live|)` if
it agrees with the base on every frozen coordinate, and contributes zero
otherwise.  Hence residual accepted mass is the number of compatible accepted
models divided by `2^|live|`.  Squaring gives the corresponding normalized
ordered-pair count.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence

namespace FiniteResidualAcceptedModelCount

local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- Coordinates which remain live under a fixed mask. -/
def liveSupport {n : Nat} (mask : Fin n -> Bool) : Finset (Fin n) :=
  Finset.univ.filter fun coordinate => mask coordinate = true

@[simp]
theorem mem_liveSupport {n : Nat} {mask : Fin n -> Bool}
    {coordinate : Fin n} :
    coordinate ∈ liveSupport mask <-> mask coordinate = true := by
  simp [liveSupport]

/-- A target input agrees with the base at every frozen coordinate. -/
def FrozenCompatible {n : Nat} (target base mask : Fin n -> Bool) : Prop :=
  forall coordinate, mask coordinate = false ->
    target coordinate = base coordinate

/-- The unique assignment to the live uniform coordinates which produces a
fixed target. -/
def livePattern {n : Nat} (target base mask : Fin n -> Bool) :
    LocalAssignment (liveSupport mask) :=
  fun coordinate => Bool.xor (base coordinate) (target coordinate)

/-- A masked completion equals a target exactly when the target is compatible
on the frozen coordinates and the uniform string has the unique live
pattern. -/
theorem maskedInput_eq_target_iff {n : Nat}
    (target base mask uniform : Fin n -> Bool) :
    maskedInput base mask uniform = target <->
      FrozenCompatible target base mask /\
        restrictAssignment (liveSupport mask) uniform =
          livePattern target base mask := by
  constructor
  · intro heq
    constructor
    · intro coordinate hmask
      have hat := congrFun heq coordinate
      simp [maskedInput, hmask] at hat
      exact hat.symm
    · funext coordinate
      have hmask : mask coordinate = true := by
        have hproperty := coordinate.property
        unfold liveSupport at hproperty
        exact (Finset.mem_filter.1 hproperty).2
      have hat := congrFun heq coordinate
      simp only [restrictAssignment, livePattern]
      cases hbase : base coordinate <;>
        cases huniform : uniform coordinate <;>
        cases htarget : target coordinate <;>
        simp_all [maskedInput]
  · rintro ⟨hcompatible, hpattern⟩
    funext coordinate
    cases hmask : mask coordinate with
    | false =>
        have hat := hcompatible coordinate hmask
        simp [maskedInput, hmask, hat]
    | true =>
        have hmem : coordinate ∈ liveSupport mask := by
          simp [hmask]
        have hat := congrFun hpattern ⟨coordinate, hmem⟩
        simp only [restrictAssignment, livePattern] at hat
        cases hbase : base coordinate <;>
          cases huniform : uniform coordinate <;>
          cases htarget : target coordinate <;>
          simp_all [maskedInput]

/-- A uniformly random Boolean string realizes every fixed local pattern with
probability exactly `2^(-|support|)`. -/
theorem finiteAverage_localPatternIndicator_uniform {n : Nat}
    (support : Finset (Fin n)) (pattern : LocalAssignment support) :
    finiteAverage (fun input : Fin n -> Bool =>
      localPatternIndicator support pattern input) =
        1 / (2 : Rat) ^ support.card := by
  classical
  let split := Equiv.piEquivPiSubtypeProd
    (fun coordinate : Fin n => coordinate ∈ support) (fun _ => Bool)
  have hrestrict
      (live : (coordinate : {x : Fin n // x ∈ support}) -> Bool)
      (frozen : (coordinate : {x : Fin n // x ∉ support}) -> Bool) :
      restrictAssignment support (split.symm (live, frozen)) = live := by
    funext coordinate
    simp [split, restrictAssignment, coordinate.property]
  unfold finiteAverage localPatternIndicator
  rw [← split.symm.sum_comp]
  have hsum :
      (∑ assignment :
          ((coordinate : {x : Fin n // x ∈ support}) -> Bool) ×
            ((coordinate : {x : Fin n // x ∉ support}) -> Bool),
        if restrictAssignment support (split.symm assignment) = pattern
        then (1 : Rat) else 0) =
      (Fintype.card
        ((coordinate : {x : Fin n // x ∉ support}) -> Bool) : Rat) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrestrict]
    simp
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]
  have hsupportCard :
      Fintype.card {x : Fin n // x ∈ support} = support.card := by
    simp
  rw [hsupportCard]
  have hcard : support.card ≤ n := by
    simpa using Finset.card_le_univ support
  have hpow :
      (2 : Rat) ^ n =
        (2 : Rat) ^ (n - support.card) * (2 : Rat) ^ support.card := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  rw [hpow]
  field_simp

/-- Exact conditional mass of one target point under a fixed affine mask. -/
theorem finiteAverage_pointIndicator_masked {n : Nat}
    (target base mask : Fin n -> Bool) :
    finiteAverage (fun uniform : Fin n -> Bool =>
      if maskedInput base mask uniform = target then (1 : Rat) else 0) =
      if FrozenCompatible target base mask then
        1 / (2 : Rat) ^ (liveSupport mask).card
      else 0 := by
  classical
  by_cases hcompatible : FrozenCompatible target base mask
  · rw [if_pos hcompatible]
    calc
      finiteAverage (fun uniform : Fin n -> Bool =>
          if maskedInput base mask uniform = target then (1 : Rat) else 0) =
        finiteAverage (fun uniform : Fin n -> Bool =>
          localPatternIndicator (liveSupport mask)
            (livePattern target base mask) uniform) := by
              apply finiteAverage_congr
              intro uniform
              simp [localPatternIndicator,
                maskedInput_eq_target_iff, hcompatible]
      _ = 1 / (2 : Rat) ^ (liveSupport mask).card :=
        finiteAverage_localPatternIndicator_uniform
          (liveSupport mask) (livePattern target base mask)
  · rw [if_neg hcompatible]
    unfold finiteAverage
    have hpoint (uniform : Fin n -> Bool) :
        maskedInput base mask uniform ≠ target := by
      intro heq
      exact hcompatible
        ((maskedInput_eq_target_iff target base mask uniform).1 heq).1
    simp [hpoint]

end FiniteResidualAcceptedModelCount

namespace FiniteUnambiguousFBDD

open FiniteResidualAcceptedModelCount

local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- Accepted inputs compatible with the base on every frozen coordinate. -/
def compatibleAcceptedModels {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : Finset B.AcceptedModel :=
  Finset.univ.filter fun accepted =>
    FrozenCompatible accepted.1 base mask

@[simp]
theorem mem_compatibleAcceptedModels {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (accepted : B.AcceptedModel) :
    accepted ∈ B.compatibleAcceptedModels base mask <->
      FrozenCompatible accepted.1 base mask := by
  simp [compatibleAcceptedModels]

/-- Literal residual accepted-model count. -/
def residualAcceptedModelCount {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : Nat :=
  (B.compatibleAcceptedModels base mask).card

/-- Ordered pairs of accepted inputs which are both compatible with the same
frozen base.  This is the literal carrier to be partitioned by a
last-common-prefix map. -/
def compatibleAcceptedModelPairs {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    Finset (B.AcceptedModel × B.AcceptedModel) :=
  (B.compatibleAcceptedModels base mask).product
    (B.compatibleAcceptedModels base mask)

/-- Literal compatible ordered-pair count. -/
def residualAcceptedModelPairCount {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) : Nat :=
  (B.compatibleAcceptedModelPairs base mask).card

/-- The ordered-pair count is the square of the residual model count. -/
theorem residualAcceptedModelPairCount_eq_count_sq {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    B.residualAcceptedModelPairCount base mask =
      (B.residualAcceptedModelCount base mask) ^ 2 := by
  simp [residualAcceptedModelPairCount, compatibleAcceptedModelPairs,
    residualAcceptedModelCount, pow_two]

/-- Exact normalized residual count. -/
noncomputable def normalizedResidualAcceptedModelCount {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) : Rat :=
  (B.residualAcceptedModelCount base mask : Rat) /
    (2 : Rat) ^ (liveSupport mask).card

/-- One accepted point has mass `2^(-|live|)` precisely when it is compatible
with the frozen base. -/
theorem acceptedPointMaskedMass_eq_if_frozenCompatible {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (base mask : Fin n -> Bool) :
    B.acceptedPointMaskedMass accepted base mask =
      if FrozenCompatible accepted.1 base mask then
        1 / (2 : Rat) ^ (liveSupport mask).card
      else 0 := by
  unfold acceptedPointMaskedMass ratAcceptedPointIndicator
  exact finiteAverage_pointIndicator_masked accepted.1 base mask

/-- Residual accepted mass is exactly the compatible model count divided by
the number of live assignments. -/
theorem residualAcceptedMass_eq_normalizedResidualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    B.residualAcceptedMass base mask =
      B.normalizedResidualAcceptedModelCount base mask := by
  classical
  unfold residualAcceptedMass normalizedResidualAcceptedModelCount
    residualAcceptedModelCount
  simp_rw [B.acceptedPointMaskedMass_eq_if_frozenCompatible]
  calc
    (∑ accepted : B.AcceptedModel,
        if FrozenCompatible accepted.1 base mask then
          1 / (2 : Rat) ^ (liveSupport mask).card else 0) =
      ∑ _accepted ∈ B.compatibleAcceptedModels base mask,
        1 / (2 : Rat) ^ (liveSupport mask).card := by
          rw [compatibleAcceptedModels, Finset.sum_filter]
    _ = ((B.compatibleAcceptedModels base mask).card : Rat) *
        (1 / (2 : Rat) ^ (liveSupport mask).card) := by simp
    _ = ((B.compatibleAcceptedModels base mask).card : Rat) /
        (2 : Rat) ^ (liveSupport mask).card := by ring

/-- Cardinal form of the residual-mass identity. -/
theorem residualAcceptedMass_eq_card_div_pow_liveSupport
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    B.residualAcceptedMass base mask =
      ((B.compatibleAcceptedModels base mask).card : Rat) /
        (2 : Rat) ^ (liveSupport mask).card := by
  exact B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount
    base mask

/-- The square of residual mass is the normalized square of the compatible
accepted-model count, i.e. the normalized ordered-pair count. -/
theorem residualAcceptedMass_sq_eq_card_sq_div_pow_two_mul_liveSupport
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    (B.residualAcceptedMass base mask) ^ 2 =
      ((B.compatibleAcceptedModels base mask).card : Rat) ^ 2 /
        (2 : Rat) ^ (2 * (liveSupport mask).card) := by
  rw [B.residualAcceptedMass_eq_card_div_pow_liveSupport]
  rw [div_pow]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- Exact normalized ordered-pair form of squared residual mass. -/
theorem residualAcceptedMass_sq_eq_pairCount_div_pow_two_mul_liveSupport
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    (B.residualAcceptedMass base mask) ^ 2 =
      (B.residualAcceptedModelPairCount base mask : Rat) /
        (2 : Rat) ^ (2 * (liveSupport mask).card) := by
  rw [B.residualAcceptedMass_sq_eq_card_sq_div_pow_two_mul_liveSupport,
    B.residualAcceptedModelPairCount_eq_count_sq]
  unfold residualAcceptedModelCount
  norm_cast

/-- Expanding a residual-count deviation exposes the normalized ordered-pair
term and the exact predictor cross term. -/
theorem normalizedResidualAcceptedModelCount_sub_sq_eq_pairCount_sub_cross
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) (predictor : Rat) :
    (B.normalizedResidualAcceptedModelCount base mask - predictor) ^ 2 =
      (B.residualAcceptedModelPairCount base mask : Rat) /
          (2 : Rat) ^ (2 * (liveSupport mask).card) -
        2 * B.normalizedResidualAcceptedModelCount base mask * predictor +
        predictor ^ 2 := by
  rw [← B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount,
    ← B.residualAcceptedMass_sq_eq_pairCount_div_pow_two_mul_liveSupport]
  ring

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
