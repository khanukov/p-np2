import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDCanonicalWalkCellEnergyPacking
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralFixedWAggregation
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralCrossFormSkew

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Cardinality-free packing of canonical walk cells at one fixed dual word

For one fixed symmetric-difference support `W`, the selected high/high
Fourier form is a weighted permutation matrix: its right coefficient at
`alpha` is the coefficient at `alpha ∆ W`.  Young's inequality and the
involutivity of this permutation give a size-free operator bound.

Applying the bound to the exact partition of canonical suffix cones by
realized accepting walks controls the complete fixed-dual walk-cell pair sum
by the Fourier energies of the two cones.  Equal bare walks are included; the
off-diagonal condition here is on distinct Fourier supports.  In particular,
no degree, number-of-walks, or pair-incidence factor occurs.

This is deliberately a **fixed-`W`** theorem.  It does not sum the estimates
over different nonempty structured dual words; those weighted shifts need
not be mutually orthogonal, and controlling their combined operator remains
the next analytic obligation.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanOppositeLiteralCorrelation
open FiniteBooleanOppositeLiteralCrossFormSkew
open FiniteBooleanOppositeLiteralFixedWAggregation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualFixedDifferenceReindex
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank
open FiniteRankWeightAbelVariation

namespace FiniteCanonicalWalkCellFixedDualPacking

/-- The weighted high/high bilinear form associated with one fixed dual word.
The weight is evaluated on the union of the two toggled supports, exactly as
in the structured selector correlation. -/
def fixedDualWeightedHighHighCrossForm {N : Nat}
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (leftFunction rightFunction : (Fin N -> Bool) -> Rat) : Rat :=
  weightedSelectedSum (highHighAlias cutoff W)
    (fun alpha => weight (alpha ∪ (alpha ∆ W)))
    (fun alpha =>
      coefficient leftFunction alpha *
        coefficient rightFunction (alpha ∆ W))

private theorem abs_mul_le_half_add_sq (x y : Rat) :
    abs (x * y) <= (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (abs x - abs y), sq_abs x, sq_abs y]

/-- A fixed-dual weighted shift has the expected `l2` operator bound.  The
hypothesis is needed only on selected high/high entries. -/
theorem abs_fixedDualWeightedHighHighCrossForm_le_energy
    {N cutoff : Nat} (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (leftFunction rightFunction : (Fin N -> Bool) -> Rat)
    (scale : Rat) (hscale : 0 <= scale)
    (hweight : ∀ alpha, highHighAlias cutoff W alpha ->
      abs (weight (alpha ∪ (alpha ∆ W))) <= scale) :
    abs (fixedDualWeightedHighHighCrossForm cutoff W weight
        leftFunction rightFunction) <=
      (scale / 2) *
        ((∑ alpha : Finset (Fin N),
            (coefficient leftFunction alpha) ^ 2) +
          ∑ alpha : Finset (Fin N),
            (coefficient rightFunction alpha) ^ 2) := by
  classical
  let leftCoefficient := fun alpha : Finset (Fin N) =>
    coefficient leftFunction alpha
  let rightCoefficient := fun alpha : Finset (Fin N) =>
    coefficient rightFunction alpha
  have hreindex :
      (∑ alpha : Finset (Fin N),
          (rightCoefficient (alpha ∆ W)) ^ 2) =
        ∑ alpha : Finset (Fin N), (rightCoefficient alpha) ^ 2 := by
    simpa only [fixedDualToggleEquiv_apply] using
      (fixedDualToggleEquiv W).sum_comp
        (fun alpha => (rightCoefficient alpha) ^ 2)
  have hterm : ∀ alpha : Finset (Fin N),
      abs (if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (leftCoefficient alpha * rightCoefficient (alpha ∆ W))
        else 0) <=
      scale *
        ((leftCoefficient alpha) ^ 2 +
          (rightCoefficient (alpha ∆ W)) ^ 2) / 2 := by
    intro alpha
    by_cases hselected : highHighAlias cutoff W alpha
    · rw [if_pos hselected, abs_mul]
      calc
        abs (weight (alpha ∪ (alpha ∆ W))) *
              abs (leftCoefficient alpha *
                rightCoefficient (alpha ∆ W)) <=
            scale * abs (leftCoefficient alpha *
              rightCoefficient (alpha ∆ W)) := by
                exact mul_le_mul_of_nonneg_right
                  (hweight alpha hselected) (abs_nonneg _)
        _ <= scale *
            (((leftCoefficient alpha) ^ 2 +
              (rightCoefficient (alpha ∆ W)) ^ 2) / 2) := by
                exact mul_le_mul_of_nonneg_left
                  (abs_mul_le_half_add_sq
                    (leftCoefficient alpha)
                    (rightCoefficient (alpha ∆ W))) hscale
        _ = scale *
            ((leftCoefficient alpha) ^ 2 +
              (rightCoefficient (alpha ∆ W)) ^ 2) / 2 := by ring
    · rw [if_neg hselected, abs_zero]
      have hsquares : 0 <=
          (leftCoefficient alpha) ^ 2 +
            (rightCoefficient (alpha ∆ W)) ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      positivity
  unfold fixedDualWeightedHighHighCrossForm weightedSelectedSum
  calc
    abs (∑ alpha : Finset (Fin N),
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient leftFunction alpha *
              coefficient rightFunction (alpha ∆ W))
        else 0) <=
      ∑ alpha : Finset (Fin N),
        abs (if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient leftFunction alpha *
              coefficient rightFunction (alpha ∆ W))
        else 0) := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ alpha : Finset (Fin N),
        scale *
          ((leftCoefficient alpha) ^ 2 +
            (rightCoefficient (alpha ∆ W)) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro alpha _
      simpa [leftCoefficient, rightCoefficient] using hterm alpha
    _ = ∑ alpha : Finset (Fin N),
        ((scale / 2) * (leftCoefficient alpha) ^ 2 +
          (scale / 2) * (rightCoefficient (alpha ∆ W)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    _ = (scale / 2) *
        ((∑ alpha : Finset (Fin N), (leftCoefficient alpha) ^ 2) +
          ∑ alpha : Finset (Fin N),
            (rightCoefficient (alpha ∆ W)) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = _ := by
      rw [hreindex]

/-- Self-form specialization of the fixed-dual operator bound. -/
theorem abs_fixedDualWeightedHighHighCrossForm_self_le_energy
    {N cutoff : Nat} (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (f : (Fin N -> Bool) -> Rat)
    (scale : Rat) (hscale : 0 <= scale)
    (hweight : ∀ alpha, highHighAlias cutoff W alpha ->
      abs (weight (alpha ∪ (alpha ∆ W))) <= scale) :
    abs (fixedDualWeightedHighHighCrossForm cutoff W weight f f) <=
      scale * ∑ alpha : Finset (Fin N),
        (coefficient f alpha) ^ 2 := by
  have hbound := abs_fixedDualWeightedHighHighCrossForm_le_energy
    W weight f f scale hscale hweight
  nlinarith

/-- A nonempty structured dual word forces every union support in its fixed
shift to pay at least the saturated `(4m+1) * tailBits` rank scale. -/
theorem abs_structuredActualRankWeight_fixedDualUnion_le
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (W : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (alpha : Finset (Fin (2 ^ n))) :
    abs (structuredActualRankWeight n m tailBits hn htail
      (alpha ∪ (alpha ∆ W))) <=
        dyadicRankWeight (structuredIndependence m * tailBits) := by
  have hWdata := (mem_nonemptyStructuredDualSupports n m hn W).mp hW
  have hne : alpha ≠ alpha ∆ W := by
    intro heq
    have h := congrArg (fun support => alpha ∆ support) heq
    have hempty : (∅ : Finset (Fin (2 ^ n))) = W := by
      simpa only [symmDiff_self, symmDiff_symmDiff_cancel_left] using h
    exact hWdata.1.ne_empty hempty.symm
  have hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (alpha ∆ (alpha ∆ W)) := by
    simpa only [symmDiff_symmDiff_cancel_left] using hWdata.2
  have hbound := distinctDualAlias_invPowUnionRank_le
    n m tailBits hn htail alpha (alpha ∆ W) hne hdual
  have hnonneg : 0 <=
      structuredActualRankWeight n m tailBits hn htail
        (alpha ∪ (alpha ∆ W)) := by
    unfold structuredActualRankWeight dyadicRankWeight
    positivity
  rw [abs_of_nonneg hnonneg]
  simpa [structuredActualRankWeight, dyadicRankWeight] using hbound

/-- Structured-rank specialization: one fixed nonempty dual word has
operator scale `2^-((4m+1) * tailBits)`, without any walk or support count. -/
theorem abs_structuredFixedDualHighHighCrossForm_le_energy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (W : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    abs (fixedDualWeightedHighHighCrossForm (2 * m) W
        (structuredActualRankWeight n m tailBits hn htail)
        leftFunction rightFunction) <=
      (dyadicRankWeight (structuredIndependence m * tailBits) / 2) *
        ((∑ alpha : Finset (Fin (2 ^ n)),
            (coefficient leftFunction alpha) ^ 2) +
          ∑ alpha : Finset (Fin (2 ^ n)),
            (coefficient rightFunction alpha) ^ 2) := by
  apply abs_fixedDualWeightedHighHighCrossForm_le_energy
  · unfold dyadicRankWeight
    positivity
  · intro alpha _
    exact abs_structuredActualRankWeight_fixedDualUnion_le
      n m tailBits hn htail W hW alpha

end FiniteCanonicalWalkCellFixedDualPacking

namespace FiniteUnambiguousFBDD

open FiniteCanonicalWalkCellFixedDualPacking

private theorem coefficient_finset_sum
    {N : Nat}
    {Cell : Type*} [DecidableEq Cell]
    (cells : Finset Cell) (f : Cell -> (Fin N -> Bool) -> Rat)
    (alpha : Finset (Fin N)) :
    coefficient (fun input => ∑ cell in cells, f cell input) alpha =
      ∑ cell in cells, coefficient (f cell) alpha := by
  classical
  unfold coefficient
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem fixedDualWeightedHighHighCrossForm_finset_sum_left
    {N : Nat} {Cell : Type*} [DecidableEq Cell]
    (cells : Finset Cell) (f : Cell -> (Fin N -> Bool) -> Rat)
    (rightFunction : (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) :
    fixedDualWeightedHighHighCrossForm cutoff W weight
        (fun input => ∑ cell in cells, f cell input) rightFunction =
      ∑ cell in cells,
        fixedDualWeightedHighHighCrossForm cutoff W weight
          (f cell) rightFunction := by
  classical
  unfold fixedDualWeightedHighHighCrossForm weightedSelectedSum
  simp_rw [coefficient_finset_sum cells f]
  calc
    (∑ alpha : Finset (Fin N),
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            ((∑ cell ∈ cells, coefficient (f cell) alpha) *
              coefficient rightFunction (alpha ∆ W))
        else 0) =
      ∑ alpha : Finset (Fin N), ∑ cell ∈ cells,
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient (f cell) alpha *
              coefficient rightFunction (alpha ∆ W))
        else 0 := by
          apply Finset.sum_congr rfl
          intro alpha _
          by_cases hselected : highHighAlias cutoff W alpha
          · rw [if_pos hselected]
            simp_rw [if_pos hselected]
            rw [Finset.sum_mul, Finset.mul_sum]
          · simp [hselected]
    _ = ∑ cell ∈ cells, ∑ alpha : Finset (Fin N),
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient (f cell) alpha *
              coefficient rightFunction (alpha ∆ W))
        else 0 := by rw [Finset.sum_comm]

private theorem fixedDualWeightedHighHighCrossForm_finset_sum_right
    {N : Nat} {Cell : Type*} [DecidableEq Cell]
    (leftFunction : (Fin N -> Bool) -> Rat)
    (cells : Finset Cell) (f : Cell -> (Fin N -> Bool) -> Rat)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat) :
    fixedDualWeightedHighHighCrossForm cutoff W weight leftFunction
        (fun input => ∑ cell in cells, f cell input) =
      ∑ cell in cells,
        fixedDualWeightedHighHighCrossForm cutoff W weight
          leftFunction (f cell) := by
  classical
  unfold fixedDualWeightedHighHighCrossForm weightedSelectedSum
  simp_rw [coefficient_finset_sum cells f]
  calc
    (∑ alpha : Finset (Fin N),
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient leftFunction alpha *
              (∑ cell ∈ cells, coefficient (f cell) (alpha ∆ W)))
        else 0) =
      ∑ alpha : Finset (Fin N), ∑ cell ∈ cells,
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient leftFunction alpha *
              coefficient (f cell) (alpha ∆ W))
        else 0 := by
          apply Finset.sum_congr rfl
          intro alpha _
          by_cases hselected : highHighAlias cutoff W alpha
          · rw [if_pos hselected]
            simp_rw [if_pos hselected]
            rw [Finset.mul_sum, Finset.mul_sum]
          · simp [hselected]
    _ = ∑ cell ∈ cells, ∑ alpha : Finset (Fin N),
        if highHighAlias cutoff W alpha then
          weight (alpha ∪ (alpha ∆ W)) *
            (coefficient leftFunction alpha *
              coefficient (f cell) (alpha ∆ W))
        else 0 := by rw [Finset.sum_comm]

/-- All fixed-dual interactions between the walk cells of two (possibly
different) canonical suffix cones.  The same bare walk is deliberately
included: two different labelled sibling suffixes can cut distinct input
subcubes inside one compatible bare-walk fiber. -/
def canonicalWalkCellPairFixedDualSum
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (cutoff : Nat) (W : Finset (Fin n))
    (weight : Finset (Fin n) -> Rat) : Rat := by
  classical
  exact
    ∑ leftWalk in B.realizedCanonicalAcceptingWalks,
      ∑ rightWalk in B.realizedCanonicalAcceptingWalks,
        fixedDualWeightedHighHighCrossForm cutoff W weight
          (B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk)
          (B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk)

/-- Exact signed regrouping: the complete walk-cell rectangle expansion of
two suffix cones is their single fixed-dual bilinear form. -/
theorem fixedDualHighHighCrossForm_cones_eq_walkCellPairSum
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (cutoff : Nat) (W : Finset (Fin n))
    (weight : Finset (Fin n) -> Rat) :
    fixedDualWeightedHighHighCrossForm cutoff W weight
        (B.canonicalResidualSuffixConeIndicator leftKey)
        (B.canonicalResidualSuffixConeIndicator rightKey) =
      B.canonicalWalkCellPairFixedDualSum
        leftKey rightKey cutoff W weight := by
  classical
  have hleft : B.canonicalResidualSuffixConeIndicator leftKey =
      fun input => ∑ walk in B.realizedCanonicalAcceptingWalks,
        B.canonicalWalkSuffixConeCellIndicator leftKey walk input := by
    funext input
    exact B.canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells
      leftKey input
  have hright : B.canonicalResidualSuffixConeIndicator rightKey =
      fun input => ∑ walk in B.realizedCanonicalAcceptingWalks,
        B.canonicalWalkSuffixConeCellIndicator rightKey walk input := by
    funext input
    exact B.canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells
      rightKey input
  rw [hleft, hright]
  rw [fixedDualWeightedHighHighCrossForm_finset_sum_left]
  unfold canonicalWalkCellPairFixedDualSum
  apply Finset.sum_congr rfl
  intro leftWalk _
  rw [fixedDualWeightedHighHighCrossForm_finset_sum_right]

/-- **Two-cone fixed-dual packing.**  All walk pairs, including equal bare
walks, are controlled at once by the two unary cone energies. -/
theorem abs_canonicalWalkCellPairFixedDualSum_le_coneEnergy
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (cutoff : Nat) (W : Finset (Fin n))
    (weight : Finset (Fin n) -> Rat)
    (scale : Rat) (hscale : 0 <= scale)
    (hweight : ∀ alpha, highHighAlias cutoff W alpha ->
      abs (weight (alpha ∪ (alpha ∆ W))) <= scale) :
    abs (B.canonicalWalkCellPairFixedDualSum
        leftKey rightKey cutoff W weight) <=
      (scale / 2) *
        ((∑ alpha : Finset (Fin n),
            (coefficient
              (B.canonicalResidualSuffixConeIndicator leftKey) alpha) ^ 2) +
          ∑ alpha : Finset (Fin n),
            (coefficient
              (B.canonicalResidualSuffixConeIndicator rightKey) alpha) ^ 2) := by
  rw [← B.fixedDualHighHighCrossForm_cones_eq_walkCellPairSum]
  exact abs_fixedDualWeightedHighHighCrossForm_le_energy
    W weight
      (B.canonicalResidualSuffixConeIndicator leftKey)
      (B.canonicalResidualSuffixConeIndicator rightKey)
      scale hscale hweight

/-- Structured-rank specialization of the two-cone packing theorem. -/
theorem abs_structuredCanonicalWalkCellPairFixedDualSum_le_coneEnergy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (leftKey rightKey : List (InputLabelledFullStep B))
    (W : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn) :
    abs (B.canonicalWalkCellPairFixedDualSum leftKey rightKey (2 * m) W
      (structuredActualRankWeight n m tailBits hn htail)) <=
      (dyadicRankWeight (structuredIndependence m * tailBits) / 2) *
        ((∑ alpha : Finset (Fin (2 ^ n)),
            (coefficient
              (B.canonicalResidualSuffixConeIndicator leftKey) alpha) ^ 2) +
          ∑ alpha : Finset (Fin (2 ^ n)),
            (coefficient
              (B.canonicalResidualSuffixConeIndicator rightKey) alpha) ^ 2) := by
  apply B.abs_canonicalWalkCellPairFixedDualSum_le_coneEnergy
    leftKey rightKey (2 * m) W
      (structuredActualRankWeight n m tailBits hn htail)
      (dyadicRankWeight (structuredIndependence m * tailBits))
  · unfold dyadicRankWeight
    positivity
  · intro alpha _
    exact abs_structuredActualRankWeight_fixedDualUnion_le
      n m tailBits hn htail W hW alpha

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
