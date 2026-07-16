import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Boolean dual-alias convolution and low/high transfer

This standalone module isolates the exact algebra behind a fixed dual support
`W`.  It deliberately does not select a lower-bound route or add any source
obligation: the statements below are finite identities over `Rat`.
-/

namespace FiniteBooleanDualAliasConvolutionTransfer

open scoped BigOperators symmDiff
open FiniteBooleanFourier FiniteBooleanFourierEnergy
  FiniteBooleanRestrictionMoment

/-! ## Character multiplication -/

/-- Walsh characters multiply by symmetric difference of their supports. -/
theorem character_symmDiff {n : Nat} (alpha beta : Finset (Fin n))
    (input : Fin n → Bool) :
    character (alpha ∆ beta) input =
      character alpha input * character beta input := by
  classical
  let leftOnly := alpha \ beta
  let rightOnly := beta \ alpha
  let common := alpha ∩ beta
  have hAlpha : leftOnly ∪ common = alpha := by
    simpa [leftOnly, common] using Finset.sdiff_union_inter alpha beta
  have hBeta : rightOnly ∪ common = beta := by
    simpa [rightOnly, common, Finset.inter_comm] using
      Finset.sdiff_union_inter beta alpha
  have hSymm : alpha ∆ beta = leftOnly ∪ rightOnly := by
    ext queryIndex
    simp [leftOnly, rightOnly, Finset.mem_symmDiff]
  have hLeftRight : Disjoint leftOnly rightOnly := by
    rw [Finset.disjoint_left]
    intro queryIndex hleft hright
    simp [leftOnly, rightOnly] at hleft hright
    exact hleft.2 hright.1
  have hLeftCommon : Disjoint leftOnly common := by
    rw [Finset.disjoint_left]
    intro queryIndex hleft hcommon
    simp [leftOnly, common] at hleft hcommon
    exact hleft.2 hcommon.2
  have hRightCommon : Disjoint rightOnly common := by
    rw [Finset.disjoint_left]
    intro queryIndex hright hcommon
    simp [rightOnly, common] at hright hcommon
    exact hright.2 hcommon.1
  have hcommonSquare := character_square common input
  calc
    character (alpha ∆ beta) input =
        character (leftOnly ∪ rightOnly) input := by rw [hSymm]
    _ = character leftOnly input * character rightOnly input :=
      character_union_of_disjoint hLeftRight input
    _ =
        (character leftOnly input * character rightOnly input) *
          (character common input * character common input) := by
      rw [hcommonSquare, mul_one]
    _ =
        (character leftOnly input * character common input) *
          (character rightOnly input * character common input) := by
      ring
    _ = character alpha input * character beta input := by
      rw [← character_union_of_disjoint hLeftCommon input,
        ← character_union_of_disjoint hRightCommon input,
        hAlpha, hBeta]

/-! ## Exact coefficient convolution -/

/-- The Fourier coefficient of a pointwise product is the symmetric-difference
convolution of the two coefficient tables.  This is an exact identity over the
finite Boolean cube. -/
theorem coefficient_mul_eq_symmDiff_convolution {n : Nat}
    (f g : (Fin n → Bool) → ℚ) (W : Finset (Fin n)) :
    coefficient (fun input => f input * g input) W =
      ∑ alpha : Finset (Fin n),
        coefficient f alpha * coefficient g (alpha ∆ W) := by
  classical
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin n → Bool =>
        f input * g input * character W input) =
        finiteAverage (fun input : Fin n → Bool =>
          (∑ alpha : Finset (Fin n),
              coefficient f alpha * character alpha input) *
            g input * character W input) := by
      apply finiteAverage_congr
      intro input
      rw [fourier_inversion]
    _ = finiteAverage (fun input : Fin n → Bool =>
          ∑ alpha : Finset (Fin n),
            coefficient f alpha *
              (g input * character (alpha ∆ W) input)) := by
      apply finiteAverage_congr
      intro input
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro alpha _
      rw [character_symmDiff]
      ring
    _ = ∑ alpha : Finset (Fin n),
          finiteAverage (fun input : Fin n → Bool =>
            coefficient f alpha *
              (g input * character (alpha ∆ W) input)) := by
      simpa using
        (finiteAverage_finset_sum
          (Finset.univ : Finset (Finset (Fin n)))
          (fun alpha input =>
            coefficient f alpha *
              (g input * character (alpha ∆ W) input)))
    _ = ∑ alpha : Finset (Fin n),
          coefficient f alpha *
            finiteAverage (fun input : Fin n → Bool =>
              g input * character (alpha ∆ W) input) := by
      apply Finset.sum_congr rfl
      intro alpha _
      exact finiteAverage_const_mul _ _
    _ = ∑ alpha : Finset (Fin n),
          coefficient f alpha * coefficient g (alpha ∆ W) := by
      apply Finset.sum_congr rfl
      intro alpha _
      apply congrArg (fun value : ℚ => coefficient f alpha * value)
      exact (coefficient_eq_finiteAverage_mul g (alpha ∆ W)).symm

/-- Idempotence turns the symmetric-difference convolution back into the
original Fourier coefficient. -/
theorem idempotent_symmDiff_convolution {n : Nat}
    (f : (Fin n → Bool) → ℚ)
    (hidempotent : ∀ input, f input * f input = f input)
    (W : Finset (Fin n)) :
    (∑ alpha : Finset (Fin n),
        coefficient f alpha * coefficient f (alpha ∆ W)) =
      coefficient f W := by
  calc
    (∑ alpha : Finset (Fin n),
        coefficient f alpha * coefficient f (alpha ∆ W)) =
        coefficient (fun input => f input * f input) W :=
      (coefficient_mul_eq_symmDiff_convolution f f W).symm
    _ = coefficient f W := by
      congr 2
      funext input
      exact hidempotent input

/-- Pointwise-disjoint functions have zero cross-convolution at every dual
support.  This is the selector-pair form used for disjoint sibling cones. -/
theorem disjoint_symmDiff_convolution_eq_zero {n : Nat}
    (left right : (Fin n → Bool) → ℚ)
    (hdisjoint : ∀ input, left input * right input = 0)
    (W : Finset (Fin n)) :
    (∑ alpha : Finset (Fin n),
        coefficient left alpha * coefficient right (alpha ∆ W)) = 0 := by
  calc
    (∑ alpha : Finset (Fin n),
        coefficient left alpha * coefficient right (alpha ∆ W)) =
        coefficient (fun input => left input * right input) W :=
      (coefficient_mul_eq_symmDiff_convolution left right W).symm
    _ = coefficient (fun _ : Fin n → Bool => (0 : ℚ)) W := by
      congr 2
      funext input
      exact hdisjoint input
    _ = 0 := by
      simp [FiniteBooleanFourier.coefficient]

/-- A nonempty Walsh support has zero coefficient in the constant-one
function. -/
theorem coefficient_one_eq_zero_of_nonempty {n : Nat}
    {W : Finset (Fin n)} (hW : W.Nonempty) :
    coefficient (fun _ : Fin n → Bool => (1 : ℚ)) W = 0 := by
  rw [coefficient_eq_finiteAverage_mul]
  have horth := finiteAverage_character_mul_character
    (∅ : Finset (Fin n)) W
  rw [if_neg (Ne.symm hW.ne_empty)] at horth
  simpa using horth

/-- For a sign-valued function, the full alias convolution cancels at every
nonempty dual support.  This is the finite Boolean `g² = 1` identity. -/
theorem sign_square_symmDiff_convolution_eq_zero {n : Nat}
    (g : (Fin n → Bool) → ℚ)
    (hsquare : ∀ input, g input * g input = 1)
    {W : Finset (Fin n)} (hW : W.Nonempty) :
    (∑ alpha : Finset (Fin n),
        coefficient g alpha * coefficient g (alpha ∆ W)) = 0 := by
  calc
    (∑ alpha : Finset (Fin n),
        coefficient g alpha * coefficient g (alpha ∆ W)) =
        coefficient (fun input => g input * g input) W :=
      (coefficient_mul_eq_symmDiff_convolution g g W).symm
    _ = coefficient (fun _ : Fin n → Bool => (1 : ℚ)) W := by
      congr 2
      funext input
      exact hsquare input
    _ = 0 := coefficient_one_eq_zero_of_nonempty hW

/-- The sign encoding of any Boolean function satisfies the exact nonempty
dual-alias cancellation. -/
theorem boolean_sign_symmDiff_convolution_eq_zero {n : Nat}
    (predicate : (Fin n → Bool) → Bool)
    {W : Finset (Fin n)} (hW : W.Nonempty) :
    (∑ alpha : Finset (Fin n),
        coefficient (fun input => boolSign (predicate input)) alpha *
          coefficient (fun input => boolSign (predicate input))
            (alpha ∆ W)) = 0 := by
  apply sign_square_symmDiff_convolution_eq_zero _ (fun input => ?_) hW
  exact boolSign_square (predicate input)

/-! ## Generic selected/rejected transfer -/

/-- The unweighted contribution on the selected indices. -/
def selectedSum {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (term : Index → ℚ) : ℚ :=
  ∑ index : Index, if selected index then term index else 0

/-- The unweighted contribution on the complementary indices. -/
def rejectedSum {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (term : Index → ℚ) : ℚ :=
  ∑ index : Index, if selected index then 0 else term index

/-- A weighted sum restricted to the selected indices. -/
def weightedSelectedSum {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (weight term : Index → ℚ) : ℚ :=
  ∑ index : Index,
    if selected index then weight index * term index else 0

/-- The variation of a selected weight around a fixed base weight. -/
def selectedWeightVariation {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (weight term : Index → ℚ) (baseWeight : ℚ) : ℚ :=
  ∑ index : Index,
    if selected index then
      (weight index - baseWeight) * term index
    else 0

/-- Selected and rejected indices partition a finite sum. -/
theorem selectedSum_add_rejectedSum {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (term : Index → ℚ) :
    selectedSum selected term + rejectedSum selected term =
      ∑ index : Index, term index := by
  classical
  unfold selectedSum rejectedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hselected : selected index <;> simp [hselected]

/-- A selected weighted sum is its constant-weight part plus its weight
variation. -/
theorem weightedSelectedSum_eq_base_mul_selectedSum_add_variation
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (weight term : Index → ℚ) (baseWeight : ℚ) :
    weightedSelectedSum selected weight term =
      baseWeight * selectedSum selected term +
        selectedWeightVariation selected weight term baseWeight := by
  classical
  unfold weightedSelectedSum selectedSum selectedWeightVariation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hselected : selected index
  · simp [hselected]
    ring
  · simp [hselected]

/-- If the total unweighted sum cancels, its selected constant-weight part can
be transferred exactly to the rejected part. -/
theorem weightedSelectedSum_eq_neg_base_mul_rejectedSum_add_variation
    {Index : Type*} [Fintype Index]
    (selected : Index → Prop) [DecidablePred selected]
    (weight term : Index → ℚ) (baseWeight : ℚ)
    (htotal : (∑ index : Index, term index) = 0) :
    weightedSelectedSum selected weight term =
      -baseWeight * rejectedSum selected term +
        selectedWeightVariation selected weight term baseWeight := by
  have hpartition := selectedSum_add_rejectedSum selected term
  have hselected :
      selectedSum selected term = -rejectedSum selected term := by
    linarith
  calc
    weightedSelectedSum selected weight term =
        baseWeight * selectedSum selected term +
          selectedWeightVariation selected weight term baseWeight :=
      weightedSelectedSum_eq_base_mul_selectedSum_add_variation
        selected weight term baseWeight
    _ = -baseWeight * rejectedSum selected term +
        selectedWeightVariation selected weight term baseWeight := by
      rw [hselected]
      ring

/-! ## Fixed-dual low/high alias decomposition -/

/-- The coefficient product paired by a fixed dual support `W`. -/
def aliasProduct {n : Nat} (coefficients : Finset (Fin n) → ℚ)
    (W alpha : Finset (Fin n)) : ℚ :=
  coefficients alpha * coefficients (alpha ∆ W)

/-- Both members of the alias pair lie strictly above `cutoff`. -/
def highHighAlias {n : Nat} (cutoff : Nat) (W alpha : Finset (Fin n)) :
    Prop :=
  cutoff < alpha.card ∧ cutoff < (alpha ∆ W).card

instance highHighAlias.instDecidablePred {n : Nat} (cutoff : Nat)
    (W : Finset (Fin n)) : DecidablePred (highHighAlias cutoff W) :=
  fun alpha => by
    unfold highHighAlias
    infer_instance

/-- The unweighted high/high part of the fixed-`W` alias sum. -/
def highHighAliasSum {n : Nat} (coefficients : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n)) : ℚ :=
  selectedSum (highHighAlias cutoff W) (aliasProduct coefficients W)

/-- The complement of the high/high part.  At least one endpoint in every
summand has degree at most `cutoff`. -/
def lowAliasRemainder {n : Nat}
    (coefficients : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n)) : ℚ :=
  rejectedSum (highHighAlias cutoff W) (aliasProduct coefficients W)

/-- A weighted fixed-`W` alias sum, restricted to high/high pairs. -/
def weightedHighHighAliasSum {n : Nat}
    (coefficients weight : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n)) : ℚ :=
  weightedSelectedSum (highHighAlias cutoff W) weight
    (aliasProduct coefficients W)

/-- The high/high weight variation around `baseWeight`. -/
def weightedAliasVariation {n : Nat}
    (coefficients weight : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n)) (baseWeight : ℚ) : ℚ :=
  selectedWeightVariation (highHighAlias cutoff W) weight
    (aliasProduct coefficients W) baseWeight

/-- Exact fixed-dual transfer: full unweighted alias cancellation moves the
constant-weight high/high contribution to the low remainder. -/
theorem weightedHighHighAliasSum_eq_neg_base_mul_lowAliasRemainder_add_variation
    {n : Nat} (coefficients weight : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n)) (baseWeight : ℚ)
    (hcancel :
      (∑ alpha : Finset (Fin n), aliasProduct coefficients W alpha) = 0) :
    weightedHighHighAliasSum coefficients weight cutoff W =
      -baseWeight * lowAliasRemainder coefficients cutoff W +
        weightedAliasVariation coefficients weight cutoff W baseWeight := by
  exact weightedSelectedSum_eq_neg_base_mul_rejectedSum_add_variation
    (highHighAlias cutoff W) weight (aliasProduct coefficients W)
      baseWeight hcancel

/-- Boolean specialization of the fixed-dual transfer. -/
theorem weightedSignAlias_decomposition {n : Nat}
    (g : (Fin n → Bool) → ℚ)
    (hsquare : ∀ input, g input * g input = 1)
    (weight : Finset (Fin n) → ℚ) (cutoff : Nat)
    {W : Finset (Fin n)} (hW : W.Nonempty) (baseWeight : ℚ) :
    weightedHighHighAliasSum (coefficient g) weight cutoff W =
      -baseWeight * lowAliasRemainder (coefficient g) cutoff W +
        weightedAliasVariation (coefficient g) weight cutoff W
          baseWeight := by
  apply
    weightedHighHighAliasSum_eq_neg_base_mul_lowAliasRemainder_add_variation
  simpa [aliasProduct] using
    sign_square_symmDiff_convolution_eq_zero g hsquare hW

/-- The remaining quantitative statement needed to upper-bound a weighted
high/high alias sum.  This is only a named proposition: this module does not
assert that an arbitrary selector weight satisfies it. -/
def WeightedVariationUpperObligation {n : Nat}
    (coefficients weight : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n))
    (baseWeight budget : ℚ) : Prop :=
  weightedAliasVariation coefficients weight cutoff W baseWeight ≤
    budget + baseWeight * lowAliasRemainder coefficients cutoff W

/-- Once full cancellation and the explicitly named variation obligation are
available, the requested upper bound follows by exact algebra. -/
theorem weightedHighHighAliasSum_le_budget_of_variationUpperObligation
    {n : Nat} (coefficients weight : Finset (Fin n) → ℚ)
    (cutoff : Nat) (W : Finset (Fin n))
    (baseWeight budget : ℚ)
    (hcancel :
      (∑ alpha : Finset (Fin n), aliasProduct coefficients W alpha) = 0)
    (hvariation : WeightedVariationUpperObligation coefficients weight
      cutoff W baseWeight budget) :
    weightedHighHighAliasSum coefficients weight cutoff W ≤ budget := by
  rw [weightedHighHighAliasSum_eq_neg_base_mul_lowAliasRemainder_add_variation
    coefficients weight cutoff W baseWeight hcancel]
  unfold WeightedVariationUpperObligation at hvariation
  linarith

/-! ## Complement-fibre form of the fixed-dual convolution -/

/-- Supports contained in a fixed dual set. -/
abbrev InsideSupport {n : Nat} (W : Finset (Fin n)) :=
  ↥W.powerset

/-- Supports contained in the complement of a fixed dual set. -/
abbrev OutsideSupport {n : Nat} (W : Finset (Fin n)) :=
  ↥((Finset.univ \ W).powerset)

/-- Every Boolean Fourier support splits uniquely into its part inside `W` and
its part outside `W`. -/
def supportSplitEquiv {n : Nat} (W : Finset (Fin n)) :
    Finset (Fin n) ≃ InsideSupport W × OutsideSupport W where
  toFun alpha :=
    (⟨alpha ∩ W, Finset.mem_powerset.mpr Finset.inter_subset_right⟩,
      ⟨alpha \ W, by
        apply Finset.mem_powerset.mpr
        intro queryIndex hqueryIndex
        simp only [Finset.mem_sdiff] at hqueryIndex ⊢
        exact ⟨Finset.mem_univ queryIndex, hqueryIndex.2⟩⟩)
  invFun split := split.1.1 ∪ split.2.1
  left_inv alpha := by
    ext queryIndex
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv split := by
    rcases split with ⟨⟨B, hB⟩, ⟨C, hC⟩⟩
    have hBsubset : B ⊆ W := Finset.mem_powerset.mp hB
    have hCsubset : C ⊆ Finset.univ \ W := Finset.mem_powerset.mp hC
    have hCnotW : ∀ ⦃queryIndex⦄, queryIndex ∈ C → queryIndex ∉ W := by
      intro queryIndex hqueryIndex
      exact (Finset.mem_sdiff.mp (hCsubset hqueryIndex)).2
    apply Prod.ext
    · apply Subtype.ext
      ext queryIndex
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hqueryIndex
        rcases hqueryIndex with ⟨hBmem | hCmem, hWmem⟩
        · exact hBmem
        · exact False.elim (hCnotW hCmem hWmem)
      · intro hBmem
        exact ⟨Or.inl hBmem, hBsubset hBmem⟩
    · apply Subtype.ext
      ext queryIndex
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hqueryIndex
        rcases hqueryIndex.1 with hBmem | hCmem
        · exact False.elim (hqueryIndex.2 (hBsubset hBmem))
        · exact hCmem
      · intro hCmem
        exact ⟨Or.inr hCmem, hCnotW hCmem⟩

/-- Toggling `W` complements the inside component and leaves the outside
component fixed. -/
theorem union_symmDiff_fixed_eq_complement_union {n : Nat}
    {W : Finset (Fin n)} (B : InsideSupport W) (C : OutsideSupport W) :
    (B.1 ∪ C.1) ∆ W = (W \ B.1) ∪ C.1 := by
  ext queryIndex
  have hBtoW : queryIndex ∈ B.1 → queryIndex ∈ W :=
    fun hqueryIndex => Finset.mem_powerset.mp B.2 hqueryIndex
  have hCnotW : queryIndex ∈ C.1 → queryIndex ∉ W := by
    intro hqueryIndex
    exact (Finset.mem_sdiff.mp
      (Finset.mem_powerset.mp C.2 hqueryIndex)).2
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- The support split with the outside component first, matching an outer sum
over complement fibres. -/
def supportSplitOutsideFirstEquiv {n : Nat} (W : Finset (Fin n)) :
    Finset (Fin n) ≃ OutsideSupport W × InsideSupport W :=
  (supportSplitEquiv W).trans
    (Equiv.prodComm (InsideSupport W) (OutsideSupport W))

/-- The cross-convolution contribution of two coefficient tables in one
complement fibre. -/
def complementFiberConvolution {n : Nat}
    (left right : Finset (Fin n) → ℚ) (W : Finset (Fin n))
    (C : OutsideSupport W) : ℚ :=
  ∑ B : InsideSupport W,
    left (B.1 ∪ C.1) * right ((W \ B.1) ∪ C.1)

/-- The complement-fibre decomposition for two, possibly different,
coefficient tables. -/
theorem sum_complementFiberConvolution_eq_fullConvolution {n : Nat}
    (left right : Finset (Fin n) → ℚ) (W : Finset (Fin n)) :
    (∑ C : OutsideSupport W,
      complementFiberConvolution left right W C) =
      ∑ alpha : Finset (Fin n), left alpha * right (alpha ∆ W) := by
  classical
  symm
  calc
    (∑ alpha : Finset (Fin n), left alpha * right (alpha ∆ W)) =
        ∑ split : OutsideSupport W × InsideSupport W,
          let alpha := split.2.1 ∪ split.1.1
          left alpha * right (alpha ∆ W) := by
      apply Fintype.sum_equiv (supportSplitOutsideFirstEquiv W)
      intro alpha
      change left alpha * right (alpha ∆ W) =
        let split := (supportSplitOutsideFirstEquiv W) alpha
        let splitAlpha := split.2.1 ∪ split.1.1
        left splitAlpha * right (splitAlpha ∆ W)
      have hrecover :
          (supportSplitOutsideFirstEquiv W).symm
            ((supportSplitOutsideFirstEquiv W) alpha) = alpha :=
        Equiv.symm_apply_apply _ alpha
      change left alpha * right (alpha ∆ W) =
        left ((supportSplitOutsideFirstEquiv W).symm
          ((supportSplitOutsideFirstEquiv W) alpha)) *
        right (((supportSplitOutsideFirstEquiv W).symm
          ((supportSplitOutsideFirstEquiv W) alpha)) ∆ W)
      rw [hrecover]
    _ = ∑ split : OutsideSupport W × InsideSupport W,
          left (split.2.1 ∪ split.1.1) *
            right ((W \ split.2.1) ∪ split.1.1) := by
      apply Finset.sum_congr rfl
      intro split _
      dsimp only
      rw [union_symmDiff_fixed_eq_complement_union split.2 split.1]
    _ = ∑ C : OutsideSupport W,
          ∑ B : InsideSupport W,
            left (B.1 ∪ C.1) * right ((W \ B.1) ∪ C.1) :=
      Fintype.sum_prod_type _
    _ = ∑ C : OutsideSupport W,
          complementFiberConvolution left right W C := by
      rfl

/-- Pointwise disjointness cancels the total of all cross complement
fibres. -/
theorem sum_complementFiberConvolution_eq_zero_of_disjoint {n : Nat}
    (left right : (Fin n → Bool) → ℚ)
    (hdisjoint : ∀ input, left input * right input = 0)
    (W : Finset (Fin n)) :
    (∑ C : OutsideSupport W,
      complementFiberConvolution (coefficient left) (coefficient right) W C) =
      0 := by
  rw [sum_complementFiberConvolution_eq_fullConvolution]
  exact disjoint_symmDiff_convolution_eq_zero left right hdisjoint W

/-- The fixed-`W` convolution contribution in one complement fibre `C`. -/
def complementFiberAlias {n : Nat}
    (coefficients : Finset (Fin n) → ℚ) (W : Finset (Fin n))
    (C : OutsideSupport W) : ℚ :=
  ∑ B : InsideSupport W,
    coefficients (B.1 ∪ C.1) * coefficients ((W \ B.1) ∪ C.1)

/-- Summing all complement fibres is exactly the full symmetric-difference
alias convolution. -/
theorem sum_complementFiberAlias_eq_fullAlias {n : Nat}
    (coefficients : Finset (Fin n) → ℚ) (W : Finset (Fin n)) :
    (∑ C : OutsideSupport W, complementFiberAlias coefficients W C) =
      ∑ alpha : Finset (Fin n), aliasProduct coefficients W alpha := by
  classical
  symm
  calc
    (∑ alpha : Finset (Fin n), aliasProduct coefficients W alpha) =
        ∑ split : OutsideSupport W × InsideSupport W,
          aliasProduct coefficients W (split.2.1 ∪ split.1.1) := by
      apply Fintype.sum_equiv (supportSplitOutsideFirstEquiv W)
      intro alpha
      change aliasProduct coefficients W alpha =
        aliasProduct coefficients W
          ((supportSplitOutsideFirstEquiv W).symm
            ((supportSplitOutsideFirstEquiv W) alpha))
      rw [Equiv.symm_apply_apply]
    _ = ∑ split : OutsideSupport W × InsideSupport W,
          coefficients (split.2.1 ∪ split.1.1) *
            coefficients ((W \ split.2.1) ∪ split.1.1) := by
      apply Finset.sum_congr rfl
      intro split _
      unfold aliasProduct
      rw [union_symmDiff_fixed_eq_complement_union split.2 split.1]
    _ = ∑ C : OutsideSupport W,
          ∑ B : InsideSupport W,
            coefficients (B.1 ∪ C.1) *
              coefficients ((W \ B.1) ∪ C.1) :=
      Fintype.sum_prod_type _
    _ = ∑ C : OutsideSupport W, complementFiberAlias coefficients W C := by
      rfl

/-- Complement-fibre cancellation for a sign-valued Boolean-cube function. -/
theorem sum_complementFiberAlias_eq_zero_of_sign_square {n : Nat}
    (g : (Fin n → Bool) → ℚ)
    (hsquare : ∀ input, g input * g input = 1)
    {W : Finset (Fin n)} (hW : W.Nonempty) :
    (∑ C : OutsideSupport W,
      complementFiberAlias (coefficient g) W C) = 0 := by
  rw [sum_complementFiberAlias_eq_fullAlias]
  simpa [aliasProduct] using
    sign_square_symmDiff_convolution_eq_zero g hsquare hW

/-! ## Exact middle split in the empty outside fibre -/

/-- The empty support, regarded as an outside component. -/
def emptyOutsideSupport {n : Nat} (W : Finset (Fin n)) : OutsideSupport W :=
  ⟨∅, by simp⟩

/-- When `B ⊆ W`, toggling `W` simply replaces `B` by `W \ B`. -/
theorem inside_symmDiff_fixed_eq_complement {n : Nat}
    {W : Finset (Fin n)} (B : InsideSupport W) :
    B.1 ∆ W = W \ B.1 := by
  simpa [emptyOutsideSupport] using
    union_symmDiff_fixed_eq_complement_union B (emptyOutsideSupport W)

/-- If `|W| = 2(cutoff+1)`, the only inside supports whose two complementary
endpoints are both above `cutoff` are the exact middle splits. -/
theorem highHighAlias_inside_iff_middle_card {n cutoff : Nat}
    {W : Finset (Fin n)} (hWcard : W.card = 2 * (cutoff + 1))
    (B : InsideSupport W) :
    highHighAlias cutoff W B.1 ↔ B.1.card = cutoff + 1 := by
  have hBsubset : B.1 ⊆ W := Finset.mem_powerset.mp B.2
  have hBcard : B.1.card ≤ W.card := Finset.card_le_card hBsubset
  have hdiffCard : (W \ B.1).card = W.card - B.1.card :=
    Finset.card_sdiff hBsubset
  unfold highHighAlias
  rw [inside_symmDiff_fixed_eq_complement B, hdiffCard, hWcard]
  omega

/-- The high/high contribution carried by one outside fibre. -/
def highHighComplementFiberAlias {n : Nat}
    (coefficients : Finset (Fin n) → ℚ) (cutoff : Nat)
    (W : Finset (Fin n)) (C : OutsideSupport W) : ℚ :=
  ∑ B : InsideSupport W,
    if highHighAlias cutoff W (B.1 ∪ C.1) then
      coefficients (B.1 ∪ C.1) * coefficients ((W \ B.1) ∪ C.1)
    else 0

/-- The coefficient sum over exact middle splits of `W`. -/
def middleSplitAlias {n : Nat}
    (coefficients : Finset (Fin n) → ℚ) (cutoff : Nat)
    (W : Finset (Fin n)) : ℚ :=
  ∑ B : InsideSupport W,
    if B.1.card = cutoff + 1 then
      coefficients B.1 * coefficients (W \ B.1)
    else 0

/-- Exact `C = ∅` corollary: for balanced `W`, the high/high fibre is precisely
the middle-split sum. -/
theorem highHigh_emptyComplementFiber_eq_middleSplit {n cutoff : Nat}
    (coefficients : Finset (Fin n) → ℚ) {W : Finset (Fin n)}
    (hWcard : W.card = 2 * (cutoff + 1)) :
    highHighComplementFiberAlias coefficients cutoff W
        (emptyOutsideSupport W) =
      middleSplitAlias coefficients cutoff W := by
  classical
  unfold highHighComplementFiberAlias middleSplitAlias
  apply Finset.sum_congr rfl
  intro B _
  have hmiddle := highHighAlias_inside_iff_middle_card hWcard B
  by_cases hcard : B.1.card = cutoff + 1
  · have hhigh : highHighAlias cutoff W B.1 := hmiddle.mpr hcard
    simp [emptyOutsideSupport, hcard, hhigh]
  · have hnotHigh : ¬highHighAlias cutoff W B.1 := by
      exact fun hhigh => hcard (hmiddle.mp hhigh)
    simp [emptyOutsideSupport, hcard, hnotHigh]

end FiniteBooleanDualAliasConvolutionTransfer
end OneTapeMagnification
end Frontier
end Pnp4
