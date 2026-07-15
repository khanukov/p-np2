import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredRankWeightedDualCorrelation
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite weighted-charge criterion for the structured far correlation

The general-tail obstruction is a signed quadratic form whose kernel is
nonnegative and symmetric, but whose unweighted row sums need not be small.
This file records the exact finite Schur-type implication suggested by that
observation.  Positive weights reduce the whole signed off-diagonal form to
weighted row charges, with no factor depending on the number of supports.
For the selector-sensitive version, negative coefficient-product edges are
first discarded (they only lower the signed form), and the Schur test is
applied only to the active positive-edge graph `E_f`.  This is a valid
sufficient condition, but it is still a uniform spectral condition: a point
mass can make `E_f` itself contain an obstructing clique.  The stronger test
on the full kernel is retained for reference.

The final theorems specialize the criterion to
`structuredRankWeightedDualFarPairCorrelation`.  They do **not** construct
selector-specific weights or prove the required row-charge premise.  Thus
this is a conditional analytic reduction, not an unconditional selector
correlation bound and not progress on a mainline lower-bound source.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanFullIndependenceRestriction
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredRankWeightedDualCorrelation

namespace DPTWStructuredWeightedCharge

/-! ## Abstract finite weighted charge -/

/-- The signed quadratic sum of a coefficient vector against a finite
kernel.  The kernel may already encode an off-diagonal relation by vanishing
on the diagonal. -/
def signedQuadraticSum {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient : ι → Rat)
    (kernel : ι → ι → Rat) : Rat :=
  ∑ left ∈ indices, ∑ right ∈ indices,
    coefficient left * coefficient right * kernel left right

/-- The positive-weight charge emitted by one row of a kernel. -/
def weightedRowCharge {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (kernel : ι → ι → Rat)
    (weight : ι → Rat) (left : ι) : Rat :=
  ∑ right ∈ indices, kernel left right * weight right

/-- Indices on which the displayed coefficient vector is nonzero.  Passing
to this set is exact for a quadratic sum and lets later weights depend on the
actual selector Fourier support. -/
def activeIndices {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient : ι → Rat) : Finset ι :=
  indices.filter (fun index => coefficient index ≠ 0)

@[simp]
theorem mem_activeIndices {ι : Type*} [DecidableEq ι]
    {indices : Finset ι} {coefficient : ι → Rat} {index : ι} :
    index ∈ activeIndices indices coefficient ↔
      index ∈ indices ∧ coefficient index ≠ 0 := by
  simp [activeIndices]

/-- Deleting zero-coefficient rows and columns does not change a signed
quadratic sum. -/
theorem signedQuadraticSum_eq_activeIndices
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient : ι → Rat)
    (kernel : ι → ι → Rat) :
    signedQuadraticSum indices coefficient kernel =
      signedQuadraticSum (activeIndices indices coefficient)
        coefficient kernel := by
  classical
  unfold signedQuadraticSum activeIndices
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro left _hleft
  by_cases hleft : coefficient left = 0
  · simp [hleft]
  · rw [if_pos hleft]
    apply Finset.sum_congr rfl
    intro right _hright
    by_cases hright : coefficient right = 0 <;> simp [hright]

/-- Weighted arithmetic--geometric mean in a denominator arrangement that
matches the row-charge calculation. -/
private theorem two_mul_le_weightedSquares
    (left right leftWeight rightWeight : Rat)
    (hleftWeight : 0 < leftWeight) (hrightWeight : 0 < rightWeight) :
    2 * left * right ≤
      left ^ 2 / leftWeight * rightWeight +
        right ^ 2 / rightWeight * leftWeight := by
  have hleftNe : leftWeight ≠ 0 := ne_of_gt hleftWeight
  have hrightNe : rightWeight ≠ 0 := ne_of_gt hrightWeight
  have hproduct : 0 < leftWeight * rightWeight :=
    mul_pos hleftWeight hrightWeight
  apply (mul_le_mul_right hproduct).mp
  field_simp [hleftNe, hrightNe]
  nlinarith [sq_nonneg (left * rightWeight - right * leftWeight)]

/-- A nonnegative symmetric finite kernel is bounded above by its weighted
row-charge quadratic expression.  This is the finite signed-charge step;
there is no cardinality loss. -/
theorem signedQuadraticSum_le_weightedRowExpression
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient weight : ι → Rat)
    (kernel : ι → ι → Rat)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hkernelSymmetric :
      ∀ left ∈ indices, ∀ right ∈ indices,
        kernel left right = kernel right left) :
    signedQuadraticSum indices coefficient kernel ≤
      ∑ left ∈ indices,
        coefficient left ^ 2 / weight left *
          weightedRowCharge indices kernel weight left := by
  classical
  let rowTerm : ι → ι → Rat := fun left right =>
    coefficient left ^ 2 / weight left *
      (kernel left right * weight right)
  have hpair (left : ι) (hleft : left ∈ indices)
      (right : ι) (hright : right ∈ indices) :
      2 * (coefficient left * coefficient right * kernel left right) ≤
        rowTerm left right + rowTerm right left := by
    have hweighted := two_mul_le_weightedSquares
      (coefficient left) (coefficient right)
      (weight left) (weight right)
      (hweight left hleft) (hweight right hright)
    have hnonnegative := hkernelNonnegative left hleft right hright
    have hmultiply := mul_le_mul_of_nonneg_right hweighted hnonnegative
    dsimp only [rowTerm]
    calc
      2 * (coefficient left * coefficient right * kernel left right) =
          (2 * coefficient left * coefficient right) *
            kernel left right := by ring
      _ ≤ (coefficient left ^ 2 / weight left * weight right +
          coefficient right ^ 2 / weight right * weight left) *
            kernel left right := hmultiply
      _ = coefficient left ^ 2 / weight left *
            (kernel left right * weight right) +
          coefficient right ^ 2 / weight right *
            (kernel right left * weight left) := by
        rw [hkernelSymmetric right hright left hleft]
        ring
  have hsummed :
      2 * signedQuadraticSum indices coefficient kernel ≤
        2 * (∑ left ∈ indices, ∑ right ∈ indices,
          rowTerm left right) := by
    calc
      2 * signedQuadraticSum indices coefficient kernel =
          ∑ left ∈ indices, ∑ right ∈ indices,
            2 * (coefficient left * coefficient right *
              kernel left right) := by
            simp only [signedQuadraticSum, Finset.mul_sum]
      _ ≤ ∑ left ∈ indices, ∑ right ∈ indices,
            (rowTerm left right + rowTerm right left) := by
          apply Finset.sum_le_sum
          intro left hleft
          apply Finset.sum_le_sum
          intro right hright
          exact hpair left hleft right hright
      _ = 2 * (∑ left ∈ indices, ∑ right ∈ indices,
            rowTerm left right) := by
          have htranspose :
              (∑ left ∈ indices, ∑ right ∈ indices,
                  rowTerm right left) =
                ∑ left ∈ indices, ∑ right ∈ indices,
                  rowTerm left right := by
            rw [Finset.sum_comm]
          simp_rw [Finset.sum_add_distrib]
          rw [htranspose]
          ring
  have hbase :
      signedQuadraticSum indices coefficient kernel ≤
        ∑ left ∈ indices, ∑ right ∈ indices,
          rowTerm left right := by
    linarith
  calc
    signedQuadraticSum indices coefficient kernel ≤
        ∑ left ∈ indices, ∑ right ∈ indices,
          rowTerm left right := hbase
    _ = ∑ left ∈ indices,
          coefficient left ^ 2 / weight left *
            weightedRowCharge indices kernel weight left := by
      apply Finset.sum_congr rfl
      intro left _hleft
      simp only [rowTerm, weightedRowCharge, Finset.mul_sum]

/-- Finite weighted Schur criterion.  If every positive-weight row emits at
most `budget` times its own weight, then the signed quadratic form is at most
`budget` times the coefficient energy, independently of `indices.card`. -/
theorem signedQuadraticSum_le_budget_mul_energy
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (coefficient weight : ι → Rat)
    (kernel : ι → ι → Rat) (budget : Rat)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hkernelNonnegative :
      ∀ left ∈ indices, ∀ right ∈ indices, 0 ≤ kernel left right)
    (hkernelSymmetric :
      ∀ left ∈ indices, ∀ right ∈ indices,
        kernel left right = kernel right left)
    (hrow : ∀ left ∈ indices,
      weightedRowCharge indices kernel weight left ≤
        budget * weight left) :
    signedQuadraticSum indices coefficient kernel ≤
      budget * ∑ left ∈ indices, coefficient left ^ 2 := by
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
            (budget * weight left) := by
      apply Finset.sum_le_sum
      intro left hleft
      apply mul_le_mul_of_nonneg_left (hrow left hleft)
      exact div_nonneg (sq_nonneg _) (le_of_lt (hweight left hleft))
    _ = budget * ∑ left ∈ indices, coefficient left ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left hleft
      have hweightNe : weight left ≠ 0 := ne_of_gt (hweight left hleft)
      field_simp [hweightNe]
      ring

/-! ## Structured dual-rank kernel -/

/-- The nonnegative symmetric kernel occurring in the exact rank-weighted
structured far residual. -/
def structuredDualRankKernel
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (left right : Finset (Fin (2 ^ n))) : Rat := by
  classical
  exact
    if left ≠ right ∧
        structuredIndependence m < (left ∆ right).card ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (left ∆ right) then
      1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail (left ∪ right)
    else 0

/-- The structured dual-rank kernel is nonnegative. -/
theorem structuredDualRankKernel_nonnegative
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (left right : Finset (Fin (2 ^ n))) :
    0 ≤ structuredDualRankKernel n m tailBits hn htail left right := by
  unfold structuredDualRankKernel
  split_ifs
  · positivity
  · exact le_rfl

/-- The structured dual-rank kernel is symmetric. -/
theorem structuredDualRankKernel_symmetric
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (left right : Finset (Fin (2 ^ n))) :
    structuredDualRankKernel n m tailBits hn htail left right =
      structuredDualRankKernel n m tailBits hn htail right left := by
  classical
  unfold structuredDualRankKernel
  have hsymmDiff : right ∆ left = left ∆ right :=
    symmDiff_comm right left
  by_cases hleft : left ≠ right ∧
      structuredIndependence m < (left ∆ right).card ∧
      IsStructuredDualSupport n (structuredIndependence m) hn
        (left ∆ right)
  · have hright : right ≠ left ∧
        structuredIndependence m < (right ∆ left).card ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (right ∆ left) := by
      rw [hsymmDiff]
      exact ⟨Ne.symm hleft.1, hleft.2⟩
    rw [if_pos hleft, if_pos hright, Finset.union_comm]
  · have hright : ¬ (right ≠ left ∧
        structuredIndependence m < (right ∆ left).card ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (right ∆ left)) := by
      intro hright
      apply hleft
      rw [hsymmDiff] at hright
      exact ⟨Ne.symm hright.1, hright.2⟩
    rw [if_neg hleft, if_neg hright]

/-- The selector-dependent positive-edge kernel.  It retains a structured
dual-rank edge exactly when the two Fourier coefficients have positive
product.  Negative edges can only decrease the original signed quadratic
form, so they need not be charged in an upper bound. -/
def structuredPositivePairKernel
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (left right : Finset (Fin (2 ^ n))) : Rat :=
  if 0 < coefficient f left * coefficient f right then
    structuredDualRankKernel n m tailBits hn htail left right
  else 0

/-- The selector-dependent positive-edge kernel is nonnegative. -/
theorem structuredPositivePairKernel_nonnegative
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (left right : Finset (Fin (2 ^ n))) :
    0 ≤ structuredPositivePairKernel n m tailBits hn htail f left right := by
  unfold structuredPositivePairKernel
  split_ifs
  · exact structuredDualRankKernel_nonnegative
      n m tailBits hn htail left right
  · exact le_rfl

/-- The selector-dependent positive-edge kernel remains symmetric. -/
theorem structuredPositivePairKernel_symmetric
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (left right : Finset (Fin (2 ^ n))) :
    structuredPositivePairKernel n m tailBits hn htail f left right =
      structuredPositivePairKernel n m tailBits hn htail f right left := by
  unfold structuredPositivePairKernel
  by_cases hpositive : 0 < coefficient f left * coefficient f right
  · have hpositive' : 0 < coefficient f right * coefficient f left := by
      simpa [mul_comm] using hpositive
    rw [if_pos hpositive, if_pos hpositive',
      structuredDualRankKernel_symmetric]
  · have hpositive' : ¬ 0 < coefficient f right * coefficient f left := by
      simpa [mul_comm] using hpositive
    rw [if_neg hpositive, if_neg hpositive']

/-- The exact rank-weighted residual is the abstract signed quadratic sum
for the structured dual-rank kernel. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_signedQuadraticSum
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      signedQuadraticSum (highDegreeSupports (2 ^ n) cutoff)
        (coefficient f)
        (structuredDualRankKernel n m tailBits hn htail) := by
  classical
  unfold structuredRankWeightedDualFarPairCorrelation signedQuadraticSum
    structuredDualRankKernel
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  split_ifs <;> ring

/-- Dropping zero coefficient rows and columns gives the active high-degree
Fourier support used by the selector-dependent charge criterion. -/
def activeHighDegreeSupports
    {n : Nat} (cutoff : Nat) (f : (Fin n → Bool) → Rat) :
    Finset (Finset (Fin n)) :=
  activeIndices (highDegreeSupports n cutoff) (coefficient f)

@[simp]
theorem mem_activeHighDegreeSupports
    {n cutoff : Nat} {f : (Fin n → Bool) → Rat}
    {support : Finset (Fin n)} :
    support ∈ activeHighDegreeSupports cutoff f ↔
      support ∈ highDegreeSupports n cutoff ∧ coefficient f support ≠ 0 := by
  simp [activeHighDegreeSupports]

/-- The original signed residual is at most the quadratic sum over its
positive coefficient-product edges.  This is where usable signed
cancellation enters: negative edges are discarded before the Schur test. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_signedQuadraticSum]
  calc
    signedQuadraticSum (highDegreeSupports (2 ^ n) cutoff)
        (coefficient f)
        (structuredDualRankKernel n m tailBits hn htail) ≤
      signedQuadraticSum (highDegreeSupports (2 ^ n) cutoff)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) := by
      unfold signedQuadraticSum
      apply Finset.sum_le_sum
      intro left _hleft
      apply Finset.sum_le_sum
      intro right _hright
      unfold structuredPositivePairKernel
      by_cases hpositive : 0 < coefficient f left * coefficient f right
      · rw [if_pos hpositive]
      · rw [if_neg hpositive]
        simp only [mul_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpositive)
          (structuredDualRankKernel_nonnegative
            n m tailBits hn htail left right)
    _ = signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) := by
      exact signedQuadraticSum_eq_activeIndices
        (highDegreeSupports (2 ^ n) cutoff) (coefficient f)
          (structuredPositivePairKernel n m tailBits hn htail f)

/-- Weighted-charge reduction on the positive Fourier edge graph `E_f`.
Unlike the full-kernel criterion below, its premise charges neither zero
coefficients nor negative coefficient-product edges.  It remains stronger
than the coefficient-vector bound because every active row shares one budget. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_of_positiveRowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ budget * weight left) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      budget *
        ∑ support ∈ activeHighDegreeSupports cutoff f,
          (coefficient f support) ^ 2 := by
  calc
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      signedQuadraticSum (activeHighDegreeSupports cutoff f)
        (coefficient f)
        (structuredPositivePairKernel n m tailBits hn htail f) :=
      structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
        n m tailBits cutoff hn htail f
    _ ≤ budget *
        ∑ support ∈ activeHighDegreeSupports cutoff f,
          (coefficient f support) ^ 2 := by
      apply signedQuadraticSum_le_budget_mul_energy
          (weight := weight)
      · exact hweight
      · intro left _hleft right _hright
        exact structuredPositivePairKernel_nonnegative
          n m tailBits hn htail f left right
      · intro left _hleft right _hright
        exact structuredPositivePairKernel_symmetric
          n m tailBits hn htail f left right
      · exact hrow

/-- For a bounded selector function, a nonnegative positive-edge row budget
directly bounds the exact rank-weighted residual. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_positiveRowBudget
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hbudget : 0 ≤ budget)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ budget * weight left) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤ budget := by
  calc
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      budget *
        ∑ support ∈ activeHighDegreeSupports cutoff f,
          (coefficient f support) ^ 2 :=
      structuredRankWeightedDualFarPairCorrelation_le_of_positiveRowCharge
        n m tailBits cutoff hn htail f weight budget hweight hrow
    _ ≤ budget * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact (bessel f (activeHighDegreeSupports cutoff f)).trans
          (finiteAverage_sq_le_one_of_abs_le_one f hbounded)
      · exact hbudget
    _ = budget := mul_one _

/-- Positive-edge row charge also bounds the original structured dual far
correlation via the exact rank-weighted identity. -/
theorem structuredDualFarPairCorrelation_le_positiveRowBudget
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hbudget : 0 ≤ budget)
    (hweight : ∀ support ∈ activeHighDegreeSupports cutoff f,
      0 < weight support)
    (hrow : ∀ left ∈ activeHighDegreeSupports cutoff f,
      weightedRowCharge (activeHighDegreeSupports cutoff f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤ budget * weight left) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
      budget := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact structuredRankWeightedDualFarPairCorrelation_le_positiveRowBudget
    n m tailBits cutoff hn htail f hbounded weight budget hbudget
      hweight hrow

/-- Stronger full-kernel weighted-charge reduction.  It is mathematically
valid, but charges every dual-rank edge irrespective of coefficient sign.
Large same-kernel cliques obstruct this premise in general.  Restricting to
positive edges helps but does not eliminate every clique; the downstream
coefficient-sensitive local-budget theorem avoids the uniform spectral norm. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_of_rowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hweight : ∀ support ∈ highDegreeSupports (2 ^ n) cutoff,
      0 < weight support)
    (hrow : ∀ left ∈ highDegreeSupports (2 ^ n) cutoff,
      weightedRowCharge (highDegreeSupports (2 ^ n) cutoff)
          (structuredDualRankKernel n m tailBits hn htail) weight left ≤
        budget * weight left) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      budget *
        ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
          (coefficient f support) ^ 2 := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_signedQuadraticSum]
  apply signedQuadraticSum_le_budget_mul_energy
      (weight := weight)
  · exact hweight
  · intro left _hleft right _hright
    exact structuredDualRankKernel_nonnegative
      n m tailBits hn htail left right
  · intro left _hleft right _hright
    exact structuredDualRankKernel_symmetric
      n m tailBits hn htail left right
  · exact hrow

/-- For a pointwise bounded Boolean-cube function, the high-degree energy is
at most one.  Hence a nonnegative row budget directly bounds the structured
rank-weighted residual itself. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_budget
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hbudget : 0 ≤ budget)
    (hweight : ∀ support ∈ highDegreeSupports (2 ^ n) cutoff,
      0 < weight support)
    (hrow : ∀ left ∈ highDegreeSupports (2 ^ n) cutoff,
      weightedRowCharge (highDegreeSupports (2 ^ n) cutoff)
          (structuredDualRankKernel n m tailBits hn htail) weight left ≤
        budget * weight left) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤ budget := by
  calc
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f ≤
      budget *
        ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
          (coefficient f support) ^ 2 :=
      structuredRankWeightedDualFarPairCorrelation_le_of_rowCharge
        n m tailBits cutoff hn htail f weight budget hweight hrow
    _ ≤ budget * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact (bessel f (highDegreeSupports (2 ^ n) cutoff)).trans
          (finiteAverage_sq_le_one_of_abs_le_one f hbounded)
      · exact hbudget
    _ = budget := mul_one _

/-- The same row-charge premise controls the original structured dual far
correlation, by the exact rank-weighted identity. -/
theorem structuredDualFarPairCorrelation_le_budget_of_rowCharge
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1)
    (weight : Finset (Fin (2 ^ n)) → Rat) (budget : Rat)
    (hbudget : 0 ≤ budget)
    (hweight : ∀ support ∈ highDegreeSupports (2 ^ n) cutoff,
      0 < weight support)
    (hrow : ∀ left ∈ highDegreeSupports (2 ^ n) cutoff,
      weightedRowCharge (highDegreeSupports (2 ^ n) cutoff)
          (structuredDualRankKernel n m tailBits hn htail) weight left ≤
        budget * weight left) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f ≤
      budget := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact structuredRankWeightedDualFarPairCorrelation_le_budget
    n m tailBits cutoff hn htail f hbounded weight budget hbudget
      hweight hrow

end DPTWStructuredWeightedCharge
end

end OneTapeMagnification
end Frontier
end Pnp4
