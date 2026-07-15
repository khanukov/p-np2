import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite spectral diagnostics for weighted row charge

The positive-weight row-charge premise is a diagonal-scaling condition:
after scaling a nonnegative kernel by the displayed weights, every row sum
is at most the target budget.  This file records that identity, a
coefficient-sensitive variable-budget refinement, and exact finite
diagnostics that can be checked without introducing real spectral theory.

First, every row must have small two-step return mass.  For a symmetric
kernel this is the squared `l2` mass of the row, so a high-degree star is an
obstruction even when its edges have an acyclic orientation.  Second, a
nonzero symmetric positive kernel cannot itself be strictly triangular with
respect to any rank: symmetry turns each positive edge into a two-cycle.

The variable-budget result preserves the location of Fourier energy and
does not require a common Perron bound for every active row.  The remaining
results diagnose possible selector-specific constructions.  None of them by
itself proves the selector correlation bound.
-/

noncomputable section

open scoped BigOperators

open DPTWStructuredWeightedCharge
open DPTWStructuredRankWeightedDualCorrelation
open DPTWStructuredUnbiasedDualCode
open FiniteBooleanFourier
open FiniteBooleanFourierEnergy

namespace FiniteWeightedChargeSpectral

/-- Diagonal scaling associated with a positive potential.  The row-charge
condition asks for the ordinary row sums of this kernel to be small. -/
def diagonallyScaledKernel {ι : Type*}
    (kernel : ι → ι → Rat) (weight : ι → Rat)
    (left right : ι) : Rat :=
  kernel left right * weight right / weight left

/-- The weighted row charge divided by the left potential is exactly the
row sum after diagonal scaling. -/
theorem sum_diagonallyScaledKernel_eq
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat)
    (weight : ι → Rat) (left : ι) :
    (∑ right ∈ indices,
        diagonallyScaledKernel kernel weight left right) =
      weightedRowCharge indices kernel weight left / weight left := by
  unfold diagonallyScaledKernel weightedRowCharge
  rw [Finset.sum_div]

/-- Over positive rational weights, the row-charge inequality is precisely
the corresponding diagonal-scaled row-sum inequality. -/
theorem rowCharge_le_iff_scaledRowSum_le
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat)
    (weight : ι → Rat) (budget : Rat) (left : ι)
    (hweight : 0 < weight left) :
    weightedRowCharge indices kernel weight left ≤ budget * weight left ↔
      (∑ right ∈ indices,
        diagonallyScaledKernel kernel weight left right) ≤ budget := by
  rw [sum_diagonallyScaledKernel_eq]
  exact (div_le_iff₀ hweight).symm

/-- A strict rank descent does give explicit rational potentials for a
*directed* kernel once its outgoing unweighted mass is bounded.  The base
can be chosen rational, and the potential is simply `base ^ rank`. -/
theorem strictRankDescent_rankPotential_rowCharge
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat) (rank : ι → Nat)
    (base mass budget : Rat)
    (hbase : 1 ≤ base)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hdescent : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right ≠ 0 → rank right < rank left)
    (hrowMass : ∀ left ∈ indices,
      (∑ right ∈ indices, kernel left right) ≤ mass)
    (hmass : mass ≤ budget * base) :
    ∀ left ∈ indices,
      weightedRowCharge indices kernel (fun index => base ^ rank index) left ≤
        budget * base ^ rank left := by
  have hbasePos : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  intro left hleft
  have hpower (right : ι) (hright : right ∈ indices)
      (hedge : kernel left right ≠ 0) :
      base * base ^ rank right ≤ base ^ rank left := by
    have hrank := hdescent left hleft right hright hedge
    calc
      base * base ^ rank right = base ^ (rank right + 1) := by
        rw [pow_succ]
        ring
      _ ≤ base ^ rank left :=
        pow_le_pow_right₀ hbase (Nat.succ_le_iff.mpr hrank)
  have hterm (right : ι) (hright : right ∈ indices) :
      base * (kernel left right * base ^ rank right) ≤
        kernel left right * base ^ rank left := by
    by_cases hedge : kernel left right = 0
    · simp [hedge]
    · calc
        base * (kernel left right * base ^ rank right) =
            kernel left right * (base * base ^ rank right) := by ring
        _ ≤ kernel left right * base ^ rank left :=
          mul_le_mul_of_nonneg_left (hpower right hright hedge)
            (hkernelNonnegative left hleft right hright)
  have hscaled :
      base * weightedRowCharge indices kernel
          (fun index => base ^ rank index) left ≤
        mass * base ^ rank left := by
    unfold weightedRowCharge
    calc
      base * (∑ right ∈ indices,
          kernel left right * base ^ rank right) =
        ∑ right ∈ indices,
          base * (kernel left right * base ^ rank right) := by
            simp only [Finset.mul_sum]
      _ ≤ ∑ right ∈ indices,
          kernel left right * base ^ rank left := by
            apply Finset.sum_le_sum
            intro right hright
            exact hterm right hright
      _ = (∑ right ∈ indices, kernel left right) *
          base ^ rank left := by
            simp only [Finset.sum_mul]
      _ ≤ mass * base ^ rank left :=
        mul_le_mul_of_nonneg_right (hrowMass left hleft)
          (pow_nonneg (le_of_lt hbasePos) _)
  have htarget :
      mass * base ^ rank left ≤
        base * (budget * base ^ rank left) := by
    calc
      mass * base ^ rank left ≤
          (budget * base) * base ^ rank left :=
        mul_le_mul_of_nonneg_right hmass
          (pow_nonneg (le_of_lt hbasePos) _)
      _ = base * (budget * base ^ rank left) := by ring
  exact (mul_le_mul_left hbasePos).mp (hscaled.trans htarget)

/-! ## Coefficient-sensitive variable local budgets -/

/-- Variable-budget weighted Schur criterion.  Unlike the uniform Perron
test, this conclusion preserves where the coefficient energy is located:
an expensive row is charged only in proportion to `coefficient index ^ 2`.
No pointwise common upper bound on the local budgets is required. -/
theorem signedQuadraticSum_le_variableBudgetEnergy
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient weight localBudget : ι → Rat)
    (kernel : ι → ι → Rat)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hkernelSymmetric :
      ∀ left ∈ indices, ∀ right ∈ indices,
        kernel left right = kernel right left)
    (hrow : ∀ left ∈ indices,
      weightedRowCharge indices kernel weight left ≤
        localBudget left * weight left) :
    signedQuadraticSum indices coefficient kernel ≤
      ∑ left ∈ indices, localBudget left * coefficient left ^ 2 := by
  calc
    signedQuadraticSum indices coefficient kernel ≤
        ∑ left ∈ indices,
          coefficient left ^ 2 / weight left *
            weightedRowCharge indices kernel weight left :=
      signedQuadraticSum_le_weightedRowExpression
        indices coefficient weight kernel hweight
          hkernelNonnegative hkernelSymmetric
    _ ≤ ∑ left ∈ indices,
        coefficient left ^ 2 / weight left *
          (localBudget left * weight left) := by
      apply Finset.sum_le_sum
      intro left hleft
      apply mul_le_mul_of_nonneg_left (hrow left hleft)
      exact div_nonneg (sq_nonneg _) (le_of_lt (hweight left hleft))
    _ = ∑ left ∈ indices,
        localBudget left * coefficient left ^ 2 := by
      apply Finset.sum_congr rfl
      intro left hleft
      have hweightNe : weight left ≠ 0 := ne_of_gt (hweight left hleft)
      field_simp [hweightNe]
      ring

/-- On an active coefficient set, if the kernel vanishes whenever the two
coefficients do not have positive product, the absolute-coefficient weights
make the weighted row expression exact.  Thus the variable-budget form can
match the actual positive-edge quadratic form rather than its Perron norm. -/
theorem signedQuadraticSum_eq_absWeightedRowExpression_of_nonpositive_kernel_zero
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient : ι → Rat)
    (kernel : ι → ι → Rat)
    (hactive : ∀ index ∈ indices, coefficient index ≠ 0)
    (hkernelZero : ∀ left ∈ indices, ∀ right ∈ indices,
      ¬ 0 < coefficient left * coefficient right → kernel left right = 0) :
    signedQuadraticSum indices coefficient kernel =
      ∑ left ∈ indices,
        coefficient left ^ 2 / |coefficient left| *
          weightedRowCharge indices kernel
            (fun index => |coefficient index|) left := by
  classical
  unfold signedQuadraticSum weightedRowCharge
  calc
    (∑ left ∈ indices, ∑ right ∈ indices,
        coefficient left * coefficient right * kernel left right) =
      ∑ left ∈ indices, ∑ right ∈ indices,
        coefficient left ^ 2 / |coefficient left| *
          (kernel left right * |coefficient right|) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      have hleftNe : coefficient left ≠ 0 := hactive left hleft
      have habsLeftNe : |coefficient left| ≠ 0 :=
        abs_ne_zero.mpr hleftNe
      have hquotient :
          coefficient left ^ 2 / |coefficient left| =
            |coefficient left| := by
        calc
          coefficient left ^ 2 / |coefficient left| =
              |coefficient left| ^ 2 / |coefficient left| := by
            rw [sq_abs]
          _ = |coefficient left| := by
            field_simp [habsLeftNe, pow_two]
      rw [hquotient]
      by_cases hpositive :
          0 < coefficient left * coefficient right
      · have habsProduct :
            |coefficient left| * |coefficient right| =
              coefficient left * coefficient right := by
          rw [← abs_mul, abs_of_pos hpositive]
        calc
          coefficient left * coefficient right * kernel left right =
              (|coefficient left| * |coefficient right|) *
                kernel left right := by rw [habsProduct]
          _ = |coefficient left| *
              (kernel left right * |coefficient right|) := by ring
      · simp [hkernelZero left hleft right hright hpositive]
    _ = ∑ left ∈ indices,
        coefficient left ^ 2 / |coefficient left| *
          (∑ right ∈ indices,
            kernel left right * |coefficient right|) := by
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.mul_sum]

/-- The realized local positive-edge budget obtained from absolute Fourier
weights.  It is allowed to be large on supports carrying little energy. -/
def structuredPositivePairLocalBudget
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (left : Finset (Fin (2 ^ n))) : Rat :=
  weightedRowCharge (activeHighDegreeSupports cutoff f)
      (structuredPositivePairKernel n m tailBits hn htail f)
      (fun support => |coefficient f support|) left /
    |coefficient f left|

/-- The positive-edge quadratic sum is exactly the Fourier-energy-weighted
sum of the realized local budgets.  This is the coefficient-sensitive
replacement for taking the maximum diagonal-scaled row sum. -/
theorem signedQuadraticSum_positivePair_eq_localBudgetEnergy
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) =
      ∑ support ∈ activeHighDegreeSupports cutoff f,
        structuredPositivePairLocalBudget
            n m tailBits cutoff hn htail f support *
          (coefficient f support) ^ 2 := by
  rw [signedQuadraticSum_eq_absWeightedRowExpression_of_nonpositive_kernel_zero]
  · apply Finset.sum_congr rfl
    intro support _hsupport
    unfold structuredPositivePairLocalBudget
    ring
  · intro support hsupport
    exact (mem_activeHighDegreeSupports.mp hsupport).2
  · intro left _hleft right _hright hnonpositive
    unfold structuredPositivePairKernel
    rw [if_neg hnonpositive]

/-- The exact structured rank-weighted residual is bounded by the canonical
coefficient-sensitive local-budget energy.  There are no existential row
weights and no uniform spectral premise in this statement.  Its only
relaxation is the earlier deletion of negative coefficient-product edges. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_localBudgetEnergy
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      ∑ support ∈ activeHighDegreeSupports cutoff f,
        structuredPositivePairLocalBudget
            n m tailBits cutoff hn htail f support *
          (coefficient f support) ^ 2 := by
  calc
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) :=
      structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
        n m tailBits cutoff hn htail f
    _ = ∑ support ∈ activeHighDegreeSupports cutoff f,
        structuredPositivePairLocalBudget
            n m tailBits cutoff hn htail f support *
          (coefficient f support) ^ 2 :=
      signedQuadraticSum_positivePair_eq_localBudgetEnergy
        n m tailBits cutoff hn htail f

/-- A bound on the canonical coefficient-sensitive local-budget energy
directly discharges the original structured far-correlation target. -/
theorem structuredDualFarPairCorrelation_le_of_localBudgetEnergy
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) (budget : Rat)
    (hlocal :
      (∑ support ∈ activeHighDegreeSupports cutoff f,
        structuredPositivePairLocalBudget
            n m tailBits cutoff hn htail f support *
          (coefficient f support) ^ 2) ≤ budget) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
      budget := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact
    (structuredRankWeightedDualFarPairCorrelation_le_localBudgetEnergy
      n m tailBits cutoff hn htail f).trans hlocal

/-- Selector-sensitive specialization with a separate local row budget for
each active positive-edge support.  The right side retains the actual
Fourier-energy location instead of replacing all local budgets by their
maximum.  The preceding deletion of negative coefficient-product edges is
still an upper bound and may lose useful cancellation. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_variablePositiveRowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (weight localBudget : Finset (Fin (2 ^ n)) → Rat)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ localBudget left * weight left) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      ∑ support ∈ activeHighDegreeSupports cutoff f,
        localBudget support * (coefficient f support) ^ 2 := by
  calc
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) :=
      structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
        n m tailBits cutoff hn htail f
    _ ≤ ∑ support ∈ activeHighDegreeSupports cutoff f,
        localBudget support * (coefficient f support) ^ 2 := by
      apply signedQuadraticSum_le_variableBudgetEnergy
          (weight := weight)
      · exact hweight
      · intro left _hleft right _hright
        exact structuredPositivePairKernel_nonnegative
          n m tailBits hn htail f left right
      · intro left _hleft right _hright
        exact structuredPositivePairKernel_symmetric
          n m tailBits hn htail f left right
      · exact hrow

/-- A coefficient-weighted global budget closes the original structured far
correlation without requiring every local budget to be uniformly small. -/
theorem structuredDualFarPairCorrelation_le_globalBudget_of_variablePositiveRowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (weight localBudget : Finset (Fin (2 ^ n)) → Rat)
    (globalBudget : Rat)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ localBudget left * weight left)
    (hglobal :
      (∑ support ∈ activeHighDegreeSupports cutoff f,
        localBudget support * (coefficient f support) ^ 2) ≤
          globalBudget) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
      globalBudget := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact
    (structuredRankWeightedDualFarPairCorrelation_le_variablePositiveRowCharge
      n m tailBits cutoff hn htail f weight localBudget hweight hrow).trans
        hglobal

/-- If the coefficient-weighted local budgets are at most `budget` times
the active Fourier energy, a pointwise bounded function has structured far
correlation at most `budget`.  This is the variable-budget analogue of the
uniform positive-row theorem. -/
theorem structuredDualFarPairCorrelation_le_budget_of_variablePositiveRowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1)
    (weight localBudget : Finset (Fin (2 ^ n)) → Rat)
    (budget : Rat) (hbudget : 0 ≤ budget)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ localBudget left * weight left)
    (hglobal :
      (∑ support ∈ activeHighDegreeSupports cutoff f,
        localBudget support * (coefficient f support) ^ 2) ≤
          budget *
            ∑ support ∈ activeHighDegreeSupports cutoff f,
              (coefficient f support) ^ 2) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
      budget := by
  calc
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
        ∑ support ∈ activeHighDegreeSupports cutoff f,
          localBudget support * (coefficient f support) ^ 2 := by
      rw [structuredDualFarPairCorrelation_eq_rankWeighted]
      exact
        structuredRankWeightedDualFarPairCorrelation_le_variablePositiveRowCharge
          n m tailBits cutoff hn htail f weight localBudget hweight hrow
    _ ≤ budget *
        ∑ support ∈ activeHighDegreeSupports cutoff f,
          (coefficient f support) ^ 2 := hglobal
    _ ≤ budget * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact
          (bessel f (activeHighDegreeSupports cutoff f)).trans
            (finiteAverage_sq_le_one_of_abs_le_one f hbounded)
      · exact hbudget
    _ = budget := mul_one _

/-- A positive row-charge subeigenvector forces the two-step return mass at
every active index to be at most the square of the row budget.  This is the
local closed-walk obstruction underlying the Perron lower bound. -/
theorem twoStepReturnMass_le_budget_sq
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat)
    (weight : ι → Rat) (budget : Rat)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hbudget : 0 ≤ budget)
    (hrow : ∀ left ∈ indices,
      weightedRowCharge indices kernel weight left ≤
        budget * weight left)
    (center : ι) (hcenter : center ∈ indices) :
    (∑ right ∈ indices, kernel center right * kernel right center) ≤
      budget ^ 2 := by
  classical
  have hsingle (right : ι) (hright : right ∈ indices) :
      kernel right center * weight center ≤
        weightedRowCharge indices kernel weight right := by
    unfold weightedRowCharge
    exact Finset.single_le_sum
      (fun other hother => mul_nonneg
        (hkernelNonnegative right hright other hother)
        (le_of_lt (hweight other hother))) hcenter
  have hterm (right : ι) (hright : right ∈ indices) :
      (kernel center right * kernel right center) * weight center ≤
        budget * (kernel center right * weight right) := by
    have hrightRow :
        kernel right center * weight center ≤ budget * weight right :=
      (hsingle right hright).trans (hrow right hright)
    have hnonnegative :=
      hkernelNonnegative center hcenter right hright
    have hmultiply := mul_le_mul_of_nonneg_left hrightRow hnonnegative
    calc
      (kernel center right * kernel right center) * weight center =
          kernel center right *
            (kernel right center * weight center) := by ring
      _ ≤ kernel center right * (budget * weight right) := hmultiply
      _ = budget * (kernel center right * weight right) := by ring
  have hsummed :
      (∑ right ∈ indices, kernel center right * kernel right center) *
          weight center ≤
        budget * weightedRowCharge indices kernel weight center := by
    unfold weightedRowCharge
    calc
      (∑ right ∈ indices, kernel center right * kernel right center) *
          weight center =
        ∑ right ∈ indices,
          (kernel center right * kernel right center) * weight center := by
            simp only [Finset.sum_mul]
      _ ≤ ∑ right ∈ indices,
          budget * (kernel center right * weight right) := by
            apply Finset.sum_le_sum
            intro right hright
            exact hterm right hright
      _ = budget *
          (∑ right ∈ indices, kernel center right * weight right) := by
            simp only [Finset.mul_sum]
  have hscaled :
      budget * weightedRowCharge indices kernel weight center ≤
        budget ^ 2 * weight center := by
    calc
      budget * weightedRowCharge indices kernel weight center ≤
          budget * (budget * weight center) :=
        mul_le_mul_of_nonneg_left (hrow center hcenter) hbudget
      _ = budget ^ 2 * weight center := by ring
  exact (mul_le_mul_right (hweight center hcenter)).mp
    (hsummed.trans hscaled)

/-- For a symmetric kernel, the preceding necessary condition is exactly a
bound on the sum of squared edge weights in every active row. -/
theorem symmetricRowSqMass_le_budget_sq
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat)
    (weight : ι → Rat) (budget : Rat)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hkernelSymmetric :
      ∀ left ∈ indices, ∀ right ∈ indices,
        kernel left right = kernel right left)
    (hbudget : 0 ≤ budget)
    (hrow : ∀ left ∈ indices,
      weightedRowCharge indices kernel weight left ≤
        budget * weight left)
    (center : ι) (hcenter : center ∈ indices) :
    (∑ right ∈ indices, (kernel center right) ^ 2) ≤ budget ^ 2 := by
  calc
    (∑ right ∈ indices, (kernel center right) ^ 2) =
        ∑ right ∈ indices,
          kernel center right * kernel right center := by
      apply Finset.sum_congr rfl
      intro right hright
      rw [← hkernelSymmetric center hcenter right hright]
      ring
    _ ≤ budget ^ 2 := twoStepReturnMass_le_budget_sq
      indices kernel weight budget hweight hkernelNonnegative hbudget hrow
        center hcenter

/-- A symmetric nonnegative kernel with a strict rank descent on every
positive edge vanishes on the active finite set.  Therefore merely orienting
the undirected positive-edge graph by a last-prefix order cannot turn the
kernel used by the Schur argument into a nonzero triangular/nilpotent one. -/
theorem symmetric_strictRankDescent_forces_zero
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat) (rank : ι → Nat)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hkernelSymmetric :
      ∀ left ∈ indices, ∀ right ∈ indices,
        kernel left right = kernel right left)
    (hdescent : ∀ left ∈ indices, ∀ right ∈ indices,
      0 < kernel left right → rank right < rank left) :
    ∀ left ∈ indices, ∀ right ∈ indices, kernel left right = 0 := by
  intro left hleft right hright
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositive
    have hforward := hdescent left hleft right hright hpositive
    have hreversePositive : 0 < kernel right left := by
      rw [← hkernelSymmetric left hleft right hright]
      exact hpositive
    have hreverse := hdescent right hright left hleft hreversePositive
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hforward)) hreverse
  · exact hkernelNonnegative left hleft right hright

/-! ## Structured positive-edge specialization -/

/-- Any proposed selector-dependent row weights force a coefficient-sign
graph diagnostic before Fourier magnitudes are used: at every active support,
the sum of squared dual-rank edge weights is at most `budget ^ 2`. -/
theorem structuredPositivePairKernel_rowSqMass_le_budget_sq
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hbudget : 0 ≤ budget)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ budget * weight left)
    (left : Finset (Fin (2 ^ n)))
    (hleft : left ∈ activeHighDegreeSupports cutoff f) :
    (∑ right ∈ activeHighDegreeSupports cutoff f,
        (structuredPositivePairKernel n m tailBits hn htail f
          left right) ^ 2) ≤ budget ^ 2 := by
  apply symmetricRowSqMass_le_budget_sq
      (activeHighDegreeSupports cutoff f)
      (structuredPositivePairKernel n m tailBits hn htail f)
      weight budget hweight
  · intro support _hsupport other _hother
    exact structuredPositivePairKernel_nonnegative
      n m tailBits hn htail f support other
  · intro support _hsupport other _hother
    exact structuredPositivePairKernel_symmetric
      n m tailBits hn htail f support other
  · exact hbudget
  · exact hrow
  · exact hleft

end FiniteWeightedChargeSpectral
end

end OneTapeMagnification
end Frontier
end Pnp4
