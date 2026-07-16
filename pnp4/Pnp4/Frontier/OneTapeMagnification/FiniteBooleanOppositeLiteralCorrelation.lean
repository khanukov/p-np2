import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualFixedDifferenceReindex

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Opposite-query literal Fourier cancellation

This file isolates the exact cancellation available when two local pieces
leave one query through opposite literals.  If `a` and `b` do not depend on
`coordinate`, then

```text
  falsePart(x) = 1[x_coordinate = false] * a(x),
  truePart(x)  = 1[x_coordinate = true]  * b(x).
```

Toggling `coordinate` in a Fourier support preserves every coefficient of
`falsePart` and negates every coefficient of `truePart`.  Consequently a
simultaneously toggled fixed-dual pair cancels whenever its selection and
rank weight are unchanged.  The final lemmas retain the exact selection and
weight differences, so they do not assume the desired selector-pair bound.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge
open FiniteStructuredDualFixedDifferenceReindex
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank

namespace FiniteBooleanOppositeLiteralCorrelation

/-- Indicator of the false literal at one coordinate. -/
def falseLiteral {N : Nat} (coordinate : Fin N)
    (input : Fin N -> Bool) : Rat :=
  if input coordinate then 0 else 1

/-- Indicator of the true literal at one coordinate. -/
def trueLiteral {N : Nat} (coordinate : Fin N)
    (input : Fin N -> Bool) : Rat :=
  if input coordinate then 1 else 0

/-- A local function guarded by the false query literal. -/
def falseLiteralPart {N : Nat} (coordinate : Fin N)
    (a : (Fin N -> Bool) -> Rat) (input : Fin N -> Bool) : Rat :=
  falseLiteral coordinate input * a input

/-- A local function guarded by the true query literal. -/
def trueLiteralPart {N : Nat} (coordinate : Fin N)
    (b : (Fin N -> Bool) -> Rat) (input : Fin N -> Bool) : Rat :=
  trueLiteral coordinate input * b input

theorem falseLiteral_eq_half_one_add_character {N : Nat}
    (coordinate : Fin N) (input : Fin N -> Bool) :
    falseLiteral coordinate input =
      (1 / 2 : Rat) *
        (character (∅ : Finset (Fin N)) input +
          character {coordinate} input) := by
  cases hvalue : input coordinate <;>
    norm_num [falseLiteral, character, boolSign, hvalue]

theorem trueLiteral_eq_half_one_sub_character {N : Nat}
    (coordinate : Fin N) (input : Fin N -> Bool) :
    trueLiteral coordinate input =
      (1 / 2 : Rat) *
        (character (∅ : Finset (Fin N)) input -
          character {coordinate} input) := by
  cases hvalue : input coordinate <;>
    norm_num [trueLiteral, character, boolSign, hvalue]

private theorem finiteAverage_add_local
    {Seed : Type*} [Fintype Seed] (f g : Seed -> Rat) :
    finiteAverage (fun seed => f seed + g seed) =
      finiteAverage f + finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib]
  ring

private theorem finiteAverage_sub_local
    {Seed : Type*} [Fintype Seed] (f g : Seed -> Rat) :
    finiteAverage (fun seed => f seed - g seed) =
      finiteAverage f - finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_sub_distrib]
  ring

@[simp]
theorem coefficient_falseLiteral_empty {N : Nat}
    (coordinate : Fin N) :
    coefficient (falseLiteral coordinate) ∅ = (1 / 2 : Rat) := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin N -> Bool =>
        falseLiteral coordinate input * character ∅ input) =
      finiteAverage (fun input : Fin N -> Bool =>
        (1 / 2 : Rat) *
          (character ∅ input * character ∅ input +
            character {coordinate} input * character ∅ input)) := by
        apply finiteAverage_congr
        intro input
        rw [falseLiteral_eq_half_one_add_character]
        ring
    _ = (1 / 2 : Rat) *
        (finiteAverage (fun input : Fin N -> Bool =>
            character ∅ input * character ∅ input) +
          finiteAverage (fun input : Fin N -> Bool =>
            character {coordinate} input * character ∅ input)) := by
      rw [finiteAverage_const_mul, finiteAverage_add_local]
    _ = (1 / 2 : Rat) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
      have hne : (∅ : Finset (Fin N)) ≠ {coordinate} := by
        intro heq
        have : coordinate ∈ (∅ : Finset (Fin N)) := by rw [heq]; simp
        simp at this
      simp [Ne.symm hne]

@[simp]
theorem coefficient_falseLiteral_singleton {N : Nat}
    (coordinate : Fin N) :
    coefficient (falseLiteral coordinate) {coordinate} =
      (1 / 2 : Rat) := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin N -> Bool =>
        falseLiteral coordinate input * character {coordinate} input) =
      finiteAverage (fun input : Fin N -> Bool =>
        (1 / 2 : Rat) *
          (character ∅ input * character {coordinate} input +
            character {coordinate} input * character {coordinate} input)) := by
        apply finiteAverage_congr
        intro input
        rw [falseLiteral_eq_half_one_add_character]
        ring
    _ = (1 / 2 : Rat) *
        (finiteAverage (fun input : Fin N -> Bool =>
            character ∅ input * character {coordinate} input) +
          finiteAverage (fun input : Fin N -> Bool =>
            character {coordinate} input * character {coordinate} input)) := by
      rw [finiteAverage_const_mul, finiteAverage_add_local]
    _ = (1 / 2 : Rat) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
      have hne : (∅ : Finset (Fin N)) ≠ {coordinate} := by
        intro heq
        have : coordinate ∈ (∅ : Finset (Fin N)) := by rw [heq]; simp
        simp at this
      simp [hne]

@[simp]
theorem coefficient_trueLiteral_empty {N : Nat}
    (coordinate : Fin N) :
    coefficient (trueLiteral coordinate) ∅ = (1 / 2 : Rat) := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin N -> Bool =>
        trueLiteral coordinate input * character ∅ input) =
      finiteAverage (fun input : Fin N -> Bool =>
        (1 / 2 : Rat) *
          (character ∅ input * character ∅ input -
            character {coordinate} input * character ∅ input)) := by
        apply finiteAverage_congr
        intro input
        rw [trueLiteral_eq_half_one_sub_character]
        ring
    _ = (1 / 2 : Rat) *
        (finiteAverage (fun input : Fin N -> Bool =>
            character ∅ input * character ∅ input) -
          finiteAverage (fun input : Fin N -> Bool =>
            character {coordinate} input * character ∅ input)) := by
      rw [finiteAverage_const_mul, finiteAverage_sub_local]
    _ = (1 / 2 : Rat) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
      simp

@[simp]
theorem coefficient_trueLiteral_singleton {N : Nat}
    (coordinate : Fin N) :
    coefficient (trueLiteral coordinate) {coordinate} =
      -(1 / 2 : Rat) := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin N -> Bool =>
        trueLiteral coordinate input * character {coordinate} input) =
      finiteAverage (fun input : Fin N -> Bool =>
        (1 / 2 : Rat) *
          (character ∅ input * character {coordinate} input -
            character {coordinate} input * character {coordinate} input)) := by
        apply finiteAverage_congr
        intro input
        rw [trueLiteral_eq_half_one_sub_character]
        ring
    _ = (1 / 2 : Rat) *
        (finiteAverage (fun input : Fin N -> Bool =>
            character ∅ input * character {coordinate} input) -
          finiteAverage (fun input : Fin N -> Bool =>
            character {coordinate} input * character {coordinate} input)) := by
      rw [finiteAverage_const_mul, finiteAverage_sub_local]
    _ = -(1 / 2 : Rat) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
      have hne : (∅ : Finset (Fin N)) ≠ {coordinate} := by
        intro heq
        have : coordinate ∈ (∅ : Finset (Fin N)) := by rw [heq]; simp
        simp at this
      simp [hne]

theorem falseLiteral_dependsOnlyOn {N : Nat} (coordinate : Fin N) :
    DependsOnlyOn {coordinate} (falseLiteral coordinate) := by
  intro input input' hagree
  have hcoordinate := hagree coordinate (by simp)
  simp only [falseLiteral]
  rw [hcoordinate]

theorem trueLiteral_dependsOnlyOn {N : Nat} (coordinate : Fin N) :
    DependsOnlyOn {coordinate} (trueLiteral coordinate) := by
  intro input input' hagree
  have hcoordinate := hagree coordinate (by simp)
  simp only [trueLiteral]
  rw [hcoordinate]

private theorem singleton_disjoint_erase_univ {N : Nat}
    (coordinate : Fin N) :
    Disjoint ({coordinate} : Finset (Fin N))
      (Finset.univ.erase coordinate) := by
  rw [Finset.disjoint_left]
  intro queryIndex hsingleton herase
  have heq : queryIndex = coordinate := by simpa using hsingleton
  subst queryIndex
  simp at herase

private theorem singleton_union_erase_univ {N : Nat}
    (coordinate : Fin N) :
    ({coordinate} : Finset (Fin N)) ∪
        Finset.univ.erase coordinate = Finset.univ := by
  ext queryIndex
  by_cases heq : queryIndex = coordinate
  · subst queryIndex
    simp
  · simp [heq]

private theorem inter_singleton_eq {N : Nat}
    (coordinate : Fin N) (alpha : Finset (Fin N)) :
    alpha ∩ {coordinate} =
      if coordinate ∈ alpha then {coordinate} else ∅ := by
  ext queryIndex
  by_cases hcoordinate : coordinate ∈ alpha
  · simp [hcoordinate]
  · simp [hcoordinate]

private theorem inter_erase_univ_eq_erase {N : Nat}
    (coordinate : Fin N) (alpha : Finset (Fin N)) :
    alpha ∩ (Finset.univ.erase coordinate) = alpha.erase coordinate := by
  ext queryIndex
  simp [and_comm]

/-- Exact false-literal coefficient: toggling the queried coordinate in the
support leaves the coefficient unchanged. -/
theorem coefficient_falseLiteralPart {N : Nat}
    (coordinate : Fin N) (a : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (alpha : Finset (Fin N)) :
    coefficient (falseLiteralPart coordinate a) alpha =
      (1 / 2 : Rat) * coefficient a (alpha.erase coordinate) := by
  have hfactor := coefficient_mul_eq_mul_coefficient_of_disjoint
    (alpha := alpha)
    (falseLiteral_dependsOnlyOn coordinate) ha
    (singleton_disjoint_erase_univ coordinate)
    (by rw [singleton_union_erase_univ]; exact Finset.subset_univ alpha)
  unfold falseLiteralPart
  rw [hfactor, inter_singleton_eq, inter_erase_univ_eq_erase]
  by_cases hcoordinate : coordinate ∈ alpha
  · simp [hcoordinate]
  · simp [hcoordinate]

/-- Exact true-literal coefficient.  It has the same erased coefficient as
the false branch, with the sign determined only by membership of the queried
coordinate in the Fourier support. -/
theorem coefficient_trueLiteralPart {N : Nat}
    (coordinate : Fin N) (b : (Fin N -> Bool) -> Rat)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (alpha : Finset (Fin N)) :
    coefficient (trueLiteralPart coordinate b) alpha =
      (if coordinate ∈ alpha then -(1 / 2 : Rat) else (1 / 2 : Rat)) *
        coefficient b (alpha.erase coordinate) := by
  have hfactor := coefficient_mul_eq_mul_coefficient_of_disjoint
    (alpha := alpha)
    (trueLiteral_dependsOnlyOn coordinate) hb
    (singleton_disjoint_erase_univ coordinate)
    (by rw [singleton_union_erase_univ]; exact Finset.subset_univ alpha)
  unfold trueLiteralPart
  rw [hfactor, inter_singleton_eq, inter_erase_univ_eq_erase]
  by_cases hcoordinate : coordinate ∈ alpha
  · simp [hcoordinate]
  · simp [hcoordinate]

/-! ## Fourier-support toggle -/

/-- Toggle one coordinate in a Fourier support. -/
def toggleSupport {N : Nat} (coordinate : Fin N)
    (alpha : Finset (Fin N)) : Finset (Fin N) :=
  {coordinate} ∆ alpha

/-- Toggling a fixed support coordinate is an equivalence. -/
def toggleSupportEquiv {N : Nat} (coordinate : Fin N) :
    Finset (Fin N) ≃ Finset (Fin N) :=
  (symmDiff_right_involutive ({coordinate} : Finset (Fin N))).toPerm
    (fun alpha => {coordinate} ∆ alpha)

@[simp]
theorem toggleSupportEquiv_apply {N : Nat} (coordinate : Fin N)
    (alpha : Finset (Fin N)) :
    toggleSupportEquiv coordinate alpha = toggleSupport coordinate alpha :=
  rfl

@[simp]
theorem mem_toggleSupport_self_iff {N : Nat} (coordinate : Fin N)
    (alpha : Finset (Fin N)) :
    coordinate ∈ toggleSupport coordinate alpha ↔ coordinate ∉ alpha := by
  classical
  simp [toggleSupport, Finset.mem_symmDiff]

theorem erase_toggleSupport {N : Nat} (coordinate : Fin N)
    (alpha : Finset (Fin N)) :
    (toggleSupport coordinate alpha).erase coordinate =
      alpha.erase coordinate := by
  classical
  ext queryIndex
  by_cases heq : queryIndex = coordinate
  · subst queryIndex
    simp
  · simp [toggleSupport, Finset.mem_symmDiff, heq]

theorem toggleSupport_symmDiff {N : Nat} (coordinate : Fin N)
    (alpha W : Finset (Fin N)) :
    toggleSupport coordinate alpha ∆ W =
      toggleSupport coordinate (alpha ∆ W) := by
  classical
  ext queryIndex
  simp only [toggleSupport, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto

@[simp]
theorem toggleSupport_toggleSupport {N : Nat} (coordinate : Fin N)
    (alpha : Finset (Fin N)) :
    toggleSupport coordinate (toggleSupport coordinate alpha) = alpha := by
  exact (toggleSupportEquiv coordinate).symm_apply_apply alpha

/-- The false-literal coefficient is invariant under a Fourier-support
toggle at the queried coordinate. -/
theorem coefficient_falseLiteralPart_toggle {N : Nat}
    (coordinate : Fin N) (a : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (alpha : Finset (Fin N)) :
    coefficient (falseLiteralPart coordinate a)
        (toggleSupport coordinate alpha) =
      coefficient (falseLiteralPart coordinate a) alpha := by
  rw [coefficient_falseLiteralPart coordinate a ha,
    coefficient_falseLiteralPart coordinate a ha,
    erase_toggleSupport]

/-- The true-literal coefficient changes sign under the same toggle. -/
theorem coefficient_trueLiteralPart_toggle {N : Nat}
    (coordinate : Fin N) (b : (Fin N -> Bool) -> Rat)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (alpha : Finset (Fin N)) :
    coefficient (trueLiteralPart coordinate b)
        (toggleSupport coordinate alpha) =
      -coefficient (trueLiteralPart coordinate b) alpha := by
  rw [coefficient_trueLiteralPart coordinate b hb,
    coefficient_trueLiteralPart coordinate b hb,
    erase_toggleSupport]
  by_cases hcoordinate : coordinate ∈ alpha
  · have htoggle : coordinate ∉ toggleSupport coordinate alpha := by
      intro hmem
      exact (mem_toggleSupport_self_iff coordinate alpha).1 hmem hcoordinate
    simp [hcoordinate, htoggle]
  · have htoggle : coordinate ∈ toggleSupport coordinate alpha :=
      (mem_toggleSupport_self_iff coordinate alpha).2 hcoordinate
    simp [hcoordinate, htoggle]

/-- Simultaneously toggling both endpoints of a coefficient product negates
the product. -/
theorem oppositeLiteral_coefficientProduct_toggle {N : Nat}
    (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (left right : Finset (Fin N)) :
    coefficient (falseLiteralPart coordinate a)
          (toggleSupport coordinate left) *
        coefficient (trueLiteralPart coordinate b)
          (toggleSupport coordinate right) =
      -(coefficient (falseLiteralPart coordinate a) left *
        coefficient (trueLiteralPart coordinate b) right) := by
  rw [coefficient_falseLiteralPart_toggle coordinate a ha,
    coefficient_trueLiteralPart_toggle coordinate b hb]
  ring

/-! ## Exact fixed-dual paired form -/

/-- One selected fixed-dual summand for opposite query literals. -/
def oppositeLiteralFixedDualTerm {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N)) : Rat :=
  if highHighAlias cutoff W alpha then
    weight (alpha ∪ (alpha ∆ W)) *
      (coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W))
  else 0

/-- The full fixed-dual selected cross form for the two opposite literals. -/
def oppositeLiteralFixedDualCrossForm {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) : Rat :=
  weightedSelectedSum (highHighAlias cutoff W)
    (fun alpha => weight (alpha ∪ (alpha ∆ W)))
    (fun alpha =>
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W))

theorem oppositeLiteralFixedDualCrossForm_eq_sum_term {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) :
    oppositeLiteralFixedDualCrossForm coordinate a b cutoff W weight =
      ∑ alpha : Finset (Fin N),
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight alpha := by
  rfl

/-- Every fixed-dual sum is exactly one half of the sum of its simultaneously
toggled pairs.  This is pure finite reindexing; no cancellation estimate is
used. -/
theorem oppositeLiteralFixedDualCrossForm_eq_half_sum_togglePairs {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) :
    oppositeLiteralFixedDualCrossForm coordinate a b cutoff W weight =
      (1 / 2 : Rat) *
        ∑ alpha : Finset (Fin N),
          (oppositeLiteralFixedDualTerm
              coordinate a b cutoff W weight alpha +
            oppositeLiteralFixedDualTerm
              coordinate a b cutoff W weight
                (toggleSupport coordinate alpha)) := by
  let term := oppositeLiteralFixedDualTerm
    coordinate a b cutoff W weight
  have hpermutation :
      (∑ alpha : Finset (Fin N), term (toggleSupport coordinate alpha)) =
        ∑ alpha : Finset (Fin N), term alpha := by
    simpa only [toggleSupportEquiv_apply] using
      (toggleSupportEquiv coordinate).sum_comp term
  rw [oppositeLiteralFixedDualCrossForm_eq_sum_term]
  change (∑ alpha : Finset (Fin N), term alpha) = _
  rw [Finset.sum_add_distrib, hpermutation]
  ring

/-- Transversal version of the toggle pairing: choose exactly the Fourier
supports not containing the query coordinate.  Unlike the symmetric
half-sum, this orients every off-dual weight derivative from `union` to
`insert coordinate union`. -/
theorem oppositeLiteralFixedDualCrossForm_eq_sum_coordinateFreeTogglePairs
    {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) :
    oppositeLiteralFixedDualCrossForm coordinate a b cutoff W weight =
      ∑ alpha in (Finset.univ : Finset (Finset (Fin N))).filter
          (fun alpha => coordinate ∉ alpha),
        (oppositeLiteralFixedDualTerm
            coordinate a b cutoff W weight alpha +
          oppositeLiteralFixedDualTerm
            coordinate a b cutoff W weight
              (toggleSupport coordinate alpha)) := by
  classical
  let term := oppositeLiteralFixedDualTerm
    coordinate a b cutoff W weight
  let absent := (Finset.univ : Finset (Finset (Fin N))).filter
    (fun alpha => coordinate ∉ alpha)
  let present := (Finset.univ : Finset (Finset (Fin N))).filter
    (fun alpha => coordinate ∈ alpha)
  have hreindex :
      (∑ alpha in absent, term (toggleSupport coordinate alpha)) =
        ∑ alpha in present, term alpha := by
    apply Finset.sum_bij (fun alpha _ => toggleSupport coordinate alpha)
    · intro alpha halpha
      have habsent : coordinate ∉ alpha := by
        simpa [absent] using halpha
      simp [present, (mem_toggleSupport_self_iff coordinate alpha).2 habsent]
    · intro left hleft right hright heq
      exact (toggleSupportEquiv coordinate).injective heq
    · intro target htarget
      have hpresent : coordinate ∈ target := by
        simpa [present] using htarget
      refine ⟨toggleSupport coordinate target, ?_, ?_⟩
      · have habsent : coordinate ∉ toggleSupport coordinate target := by
          intro hmem
          exact (mem_toggleSupport_self_iff coordinate target).1 hmem hpresent
        simp [absent, habsent]
      · exact toggleSupport_toggleSupport coordinate target
    · intro alpha halpha
      rfl
  have hsplit := Finset.sum_filter_not_add_sum_filter
    (Finset.univ : Finset (Finset (Fin N)))
    (fun alpha => coordinate ∈ alpha) term
  rw [oppositeLiteralFixedDualCrossForm_eq_sum_term]
  change (∑ alpha : Finset (Fin N), term alpha) = _
  calc
    (∑ alpha : Finset (Fin N), term alpha) =
        (∑ alpha in absent, term alpha) +
          ∑ alpha in present, term alpha := by
      symm
      simpa [absent, present] using hsplit
    _ = (∑ alpha in absent, term alpha) +
          ∑ alpha in absent, term (toggleSupport coordinate alpha) := by
      rw [hreindex]
    _ = ∑ alpha in absent,
          (term alpha + term (toggleSupport coordinate alpha)) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by rfl

/-- Fixed-dual specialization of simultaneous coefficient-product
negation. -/
theorem oppositeLiteral_fixedDualCoefficientProduct_toggle {N : Nat}
    (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W alpha : Finset (Fin N)) :
    coefficient (falseLiteralPart coordinate a)
          (toggleSupport coordinate alpha) *
        coefficient (trueLiteralPart coordinate b)
          (toggleSupport coordinate alpha ∆ W) =
      -(coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)) := by
  rw [toggleSupport_symmDiff]
  exact oppositeLiteral_coefficientProduct_toggle
    coordinate a b ha hb alpha (alpha ∆ W)

/-- Exact selected/unselected decomposition of one toggled pair.  The first
branch is the bulk weight derivative; the other two nonzero branches are the
two possible cutoff boundaries. -/
theorem oppositeLiteralFixedDualTerm_add_toggle_eq_fourRegime {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N)) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    let union := alpha ∪ (alpha ∆ W)
    let toggledUnion :=
      toggleSupport coordinate alpha ∪
        (toggleSupport coordinate alpha ∆ W)
    oppositeLiteralFixedDualTerm
          coordinate a b cutoff W weight alpha +
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight
          (toggleSupport coordinate alpha) =
      if highHighAlias cutoff W alpha then
        if highHighAlias cutoff W (toggleSupport coordinate alpha) then
          product * (weight union - weight toggledUnion)
        else
          weight union * product
      else if highHighAlias cutoff W (toggleSupport coordinate alpha) then
        -(weight toggledUnion * product)
      else 0 := by
  dsimp only
  have hproduct := oppositeLiteral_fixedDualCoefficientProduct_toggle
    coordinate a b ha hb W alpha
  by_cases horiginal : highHighAlias cutoff W alpha
  · by_cases htoggled :
        highHighAlias cutoff W (toggleSupport coordinate alpha)
    · simp [oppositeLiteralFixedDualTerm, horiginal, htoggled, hproduct]
      ring
    · simp [oppositeLiteralFixedDualTerm, horiginal, htoggled]
  · by_cases htoggled :
        highHighAlias cutoff W (toggleSupport coordinate alpha)
    · simp [oppositeLiteralFixedDualTerm, horiginal, htoggled, hproduct]
    · simp [oppositeLiteralFixedDualTerm, horiginal, htoggled]

theorem toggleSupport_eq_insert_of_not_mem {N : Nat}
    (coordinate : Fin N) (alpha : Finset (Fin N))
    (hcoordinate : coordinate ∉ alpha) :
    toggleSupport coordinate alpha = insert coordinate alpha := by
  classical
  ext queryIndex
  simp only [toggleSupport, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  by_cases heq : queryIndex = coordinate
  · subst queryIndex
    simp [hcoordinate]
  · simp [heq]

/-- Away from the dual word, adding the absent query coordinate to both
endpoints preserves the high/high predicate. -/
theorem highHighAlias_toggle_of_not_mem {N : Nat}
    (coordinate : Fin N) (cutoff : Nat) (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (hhigh : highHighAlias cutoff W alpha) :
    highHighAlias cutoff W (toggleSupport coordinate alpha) := by
  have hcoordinateRight : coordinate ∉ alpha ∆ W := by
    simp only [Finset.mem_symmDiff]
    tauto
  unfold highHighAlias at hhigh ⊢
  rw [toggleSupport_symmDiff,
    toggleSupport_eq_insert_of_not_mem coordinate alpha hcoordinateAlpha,
    toggleSupport_eq_insert_of_not_mem coordinate (alpha ∆ W)
      hcoordinateRight]
  simp [hcoordinateAlpha, hcoordinateRight]
  omega

/-- With the query absent from both the representative and the fixed dual,
the toggled union is obtained by inserting exactly that coordinate. -/
theorem fixedDualUnion_toggle_eq_insert_of_not_mem {N : Nat}
    (coordinate : Fin N) (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W) :
    toggleSupport coordinate alpha ∪
          (toggleSupport coordinate alpha ∆ W) =
      insert coordinate (alpha ∪ (alpha ∆ W)) := by
  have hcoordinateRight : coordinate ∉ alpha ∆ W := by
    simp only [Finset.mem_symmDiff]
    tauto
  rw [toggleSupport_symmDiff,
    toggleSupport_eq_insert_of_not_mem coordinate alpha hcoordinateAlpha,
    toggleSupport_eq_insert_of_not_mem coordinate (alpha ∆ W)
      hcoordinateRight]
  ext queryIndex
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- **Three-regime derivative formula away from the dual word.**  Choose the
representative without the query coordinate.  Then the impossible
"original-only" regime disappears: a pair is either bulk high/high (giving
the exact weight derivative), newly admitted at the cutoff boundary, or
absent on both sides. -/
theorem oppositeLiteralFixedDualTerm_add_toggle_eq_threeRegime_of_not_mem
    {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    let union := alpha ∪ (alpha ∆ W)
    let toggledUnion :=
      toggleSupport coordinate alpha ∪
        (toggleSupport coordinate alpha ∆ W)
    oppositeLiteralFixedDualTerm
          coordinate a b cutoff W weight alpha +
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight
          (toggleSupport coordinate alpha) =
      if highHighAlias cutoff W alpha then
        product * (weight union - weight toggledUnion)
      else if highHighAlias cutoff W (toggleSupport coordinate alpha) then
        -(weight toggledUnion * product)
      else 0 := by
  rw [oppositeLiteralFixedDualTerm_add_toggle_eq_fourRegime
    coordinate a b ha hb cutoff W weight alpha]
  by_cases horiginal : highHighAlias cutoff W alpha
  · have htoggled := highHighAlias_toggle_of_not_mem
      coordinate cutoff W alpha hcoordinateAlpha hcoordinateW horiginal
    simp [horiginal, htoggled]
  · simp [horiginal]

/-- Same three-regime formula with the toggled union normalized to the
literal insertion `insert coordinate union`.  This is the form needed by a
one-coordinate mask-rank derivative estimate. -/
theorem oppositeLiteralFixedDualTerm_add_toggle_eq_insertDerivative
    {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    let union := alpha ∪ (alpha ∆ W)
    oppositeLiteralFixedDualTerm
          coordinate a b cutoff W weight alpha +
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight
          (toggleSupport coordinate alpha) =
      if highHighAlias cutoff W alpha then
        product * (weight union - weight (insert coordinate union))
      else if highHighAlias cutoff W (toggleSupport coordinate alpha) then
        -(weight (insert coordinate union) * product)
      else 0 := by
  rw [oppositeLiteralFixedDualTerm_add_toggle_eq_threeRegime_of_not_mem
    coordinate a b ha hb cutoff W weight alpha
      hcoordinateAlpha hcoordinateW]
  rw [fixedDualUnion_toggle_eq_insert_of_not_mem
    coordinate W alpha hcoordinateAlpha hcoordinateW]

/-- If the query coordinate belongs to the fixed dual word, simultaneous
toggle preserves the union support exactly. -/
theorem fixedDualUnion_toggle_eq_of_mem {N : Nat}
    (coordinate : Fin N) (W alpha : Finset (Fin N))
    (hcoordinateW : coordinate ∈ W) :
    toggleSupport coordinate alpha ∪
          (toggleSupport coordinate alpha ∆ W) =
      alpha ∪ (alpha ∆ W) := by
  classical
  ext queryIndex
  by_cases heq : queryIndex = coordinate
  · subst queryIndex
    simp [toggleSupport, Finset.mem_symmDiff, hcoordinateW]
    tauto
  · simp [toggleSupport, Finset.mem_symmDiff, heq]

/-- On a dual word containing the query, every selected-selected toggled pair
cancels exactly for every union-dependent weight. -/
theorem oppositeLiteralFixedDualTerm_add_toggle_eq_zero_of_mem_of_bothHigh
    {N : Nat}
    (coordinate : Fin N) (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N))
    (hcoordinateW : coordinate ∈ W)
    (horiginal : highHighAlias cutoff W alpha)
    (htoggled : highHighAlias cutoff W (toggleSupport coordinate alpha)) :
    oppositeLiteralFixedDualTerm
          coordinate a b cutoff W weight alpha +
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight
          (toggleSupport coordinate alpha) = 0 := by
  rw [oppositeLiteralFixedDualTerm_add_toggle_eq_fourRegime
    coordinate a b ha hb cutoff W weight alpha]
  rw [if_pos horiginal, if_pos htoggled,
    fixedDualUnion_toggle_eq_of_mem coordinate W alpha hcoordinateW]
  ring

/-! ## Actual structured rank weight at `q = 2m` -/

/-- The exact union-support mask weight used by the structured selector. -/
def structuredActualRankWeight
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) : Rat :=
  dyadicRankWeight
    (supportPrefixConstraintRank n (structuredIndependence m)
      tailBits hn htail support)

/-- The three-regime formula specialized to the actual structured mask rank,
the cutoff `q = 2m`, and independence degree `K = structuredIndependence m =
4m+1`.  In the bulk, the only surviving quantity is the one-coordinate
dyadic rank-weight derivative. -/
theorem structuredActualRankOppositeLiteralPair_eq_insertRankDerivative
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W alpha : Finset (Fin (2 ^ n)))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W) :
    let product :=
      coefficient (falseLiteralPart coordinate a) alpha *
        coefficient (trueLiteralPart coordinate b) (alpha ∆ W)
    let union := alpha ∪ (alpha ∆ W)
    oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail) alpha +
        oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail)
          (toggleSupport coordinate alpha) =
      if highHighAlias (2 * m) W alpha then
        product *
          (dyadicRankWeight
              (supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail union) -
            dyadicRankWeight
              (supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (insert coordinate union)))
      else if highHighAlias (2 * m) W (toggleSupport coordinate alpha) then
        -(dyadicRankWeight
            (supportPrefixConstraintRank n (structuredIndependence m)
              tailBits hn htail (insert coordinate union)) * product)
      else 0 := by
  simpa only [structuredActualRankWeight] using
    (oppositeLiteralFixedDualTerm_add_toggle_eq_insertDerivative
      coordinate a b ha hb (2 * m) W
        (structuredActualRankWeight n m tailBits hn htail) alpha
          hcoordinateAlpha hcoordinateW)

/-- Reexpress the complete distinct structured-dual cross form of the two
opposite literals as fixed-dual forms carrying the actual rank weight. -/
theorem structuredDualRankDistinctOppositeLiteralCrossForm_eq_fixedDual
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits (2 * m) hn htail
        (falseLiteralPart coordinate a) (trueLiteralPart coordinate b) =
      ∑ W ∈ nonemptyStructuredDualSupports n m hn,
        oppositeLiteralFixedDualCrossForm coordinate a b (2 * m) W
          (structuredActualRankWeight n m tailBits hn htail) := by
  rw [structuredDualRankDistinctCrossForm_eq_sum_fixedDualRankWeightedHighHigh]
  rfl

/-- Exact whole-form pairing.  Each nonempty structured dual word is now a
sum of simultaneous query-coordinate toggle pairs, ready for the preceding
bulk/boundary formulas. -/
theorem structuredDualRankDistinctOppositeLiteralCrossForm_eq_half_togglePairs
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits (2 * m) hn htail
        (falseLiteralPart coordinate a) (trueLiteralPart coordinate b) =
      ∑ W ∈ nonemptyStructuredDualSupports n m hn,
        (1 / 2 : Rat) *
          ∑ alpha : Finset (Fin (2 ^ n)),
            (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
                (structuredActualRankWeight n m tailBits hn htail) alpha +
              oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
                (structuredActualRankWeight n m tailBits hn htail)
                (toggleSupport coordinate alpha)) := by
  rw [structuredDualRankDistinctOppositeLiteralCrossForm_eq_fixedDual]
  apply Finset.sum_congr rfl
  intro W _hW
  rw [oppositeLiteralFixedDualCrossForm_eq_half_sum_togglePairs]

/-- Oriented whole-form version: every support is represented exactly once
by the member of its toggle orbit which omits `coordinate`.  Thus each
off-coordinate dual summand has the insert-rank derivative orientation from
`structuredActualRankOppositeLiteralPair_eq_insertRankDerivative`. -/
theorem structuredDualRankDistinctOppositeLiteralCrossForm_eq_coordinateFreePairs
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (coordinate : Fin (2 ^ n))
    (a b : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits (2 * m) hn htail
        (falseLiteralPart coordinate a) (trueLiteralPart coordinate b) =
      ∑ W ∈ nonemptyStructuredDualSupports n m hn,
        ∑ alpha in
            (Finset.univ : Finset (Finset (Fin (2 ^ n)))).filter
              (fun alpha => coordinate ∉ alpha),
          (oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
              (structuredActualRankWeight n m tailBits hn htail) alpha +
            oppositeLiteralFixedDualTerm coordinate a b (2 * m) W
              (structuredActualRankWeight n m tailBits hn htail)
              (toggleSupport coordinate alpha)) := by
  rw [structuredDualRankDistinctOppositeLiteralCrossForm_eq_fixedDual]
  apply Finset.sum_congr rfl
  intro W _hW
  rw [oppositeLiteralFixedDualCrossForm_eq_sum_coordinateFreeTogglePairs]

end FiniteBooleanOppositeLiteralCorrelation

end

end OneTapeMagnification
end Frontier
end Pnp4
