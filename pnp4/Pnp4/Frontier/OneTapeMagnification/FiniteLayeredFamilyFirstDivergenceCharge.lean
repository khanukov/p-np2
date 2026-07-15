import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyAcceptedInputPairDecomposition
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Abstract residual-pair charge for finite correlations

`FiniteLayeredFamilyAcceptedInputPairDecomposition` rewrites the selector
high-tail second moment as an ordered double sum over accepted inputs.  This
file isolates the finite arithmetic that a future canonical-trace argument may
use after assigning every off-diagonal pair to a residual-pair group.

For every fixed left object, a `bucket` assigns each distinct right object to
a group.  A group carries an integral `residualCount` and a rational `charge`.
The sharp algebraic theorem retains the actual weighted fiber sum

`sum_left sum_group |fiber(left, group)| * residualCount(left, group) *
  charge(left, group)`.

A separate coarse corollary assumes fiber-capacity and per-left charge-budget
bounds and obtains

`varianceScale * (totalMass + totalMass^2 * chargeBudget)`.

All correlation estimates are signed upper bounds; no absolute value is
inserted.  This file does **not** construct an edge-labelled reverse trace,
identify a genuine first-divergence location, or prove a splice injection.
Those geometric and analytic obligations must be supplied separately before
the abstract charge can be instantiated as a derivation-path argument.
-/

namespace FiniteFirstDivergenceCharge

open scoped BigOperators
open FiniteBooleanRestrictionMoment
open FiniteUnambiguousFBDD

noncomputable local instance acceptedModelDecidableEq {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    DecidableEq family.AcceptedModel :=
  Classical.decEq _

/-- The right objects assigned to one residual-pair group for a fixed left
object.  The diagonal is excluded. -/
def fiber {Index Group : Type*} [Fintype Index] [DecidableEq Index]
    [DecidableEq Group]
    (bucket : Index -> Index -> Group) (left : Index) (group : Group) :
    Finset Index :=
  Finset.univ.filter fun right =>
    right ≠ left ∧ bucket left right = group

/-- Residual-pair fibers partition the off-diagonal right objects for each
fixed left object. -/
theorem sum_fiber_eq_offDiagonal
    {Index Group : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Group] [DecidableEq Group]
    (bucket : Index -> Index -> Group) (value : Index -> ℚ)
    (left : Index) :
    (∑ group : Group, ∑ right ∈ fiber bucket left group, value right) =
      ∑ right : Index, if right ≠ left then value right else 0 := by
  classical
  calc
    (∑ group : Group, ∑ right ∈ fiber bucket left group, value right) =
        ∑ group : Group, ∑ right : Index,
          if right ≠ left ∧ bucket left right = group then value right else 0 := by
            apply Finset.sum_congr rfl
            intro group _
            rw [show fiber bucket left group =
                Finset.univ.filter (fun right =>
                  right ≠ left ∧ bucket left right = group) by
              rfl]
            rw [Finset.sum_filter]
    _ = ∑ right : Index, ∑ group : Group,
          if right ≠ left ∧ bucket left right = group then value right else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ right : Index, if right ≠ left then value right else 0 := by
      apply Finset.sum_congr rfl
      intro right _
      by_cases hne : right ≠ left
      · simp [hne]
      · simp [hne]

/-- A finite double sum is its diagonal plus its residual-pair fiber sums. -/
theorem sum_pair_eq_sum_diagonal_add_sum_fibers
    {Index Group : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Group] [DecidableEq Group]
    (bucket : Index -> Index -> Group) (correlation : Index -> Index -> ℚ) :
    (∑ left : Index, ∑ right : Index, correlation left right) =
      (∑ left : Index, correlation left left) +
        ∑ left : Index, ∑ group : Group,
          ∑ right ∈ fiber bucket left group, correlation left right := by
  classical
  calc
    (∑ left : Index, ∑ right : Index, correlation left right) =
        ∑ left : Index,
          (correlation left left +
            ∑ right : Index,
              if right ≠ left then correlation left right else 0) := by
            apply Finset.sum_congr rfl
            intro left _
            calc
              (∑ right : Index, correlation left right) =
                  ∑ right : Index,
                    ((if right = left then correlation left right else 0) +
                      if right ≠ left then correlation left right else 0) := by
                        apply Finset.sum_congr rfl
                        intro right _
                        by_cases heq : right = left
                        · simp [heq]
                        · simp [heq]
              _ = (∑ right : Index,
                    if right = left then correlation left right else 0) +
                    ∑ right : Index,
                      if right ≠ left then correlation left right else 0 := by
                        rw [Finset.sum_add_distrib]
              _ = correlation left left +
                    ∑ right : Index,
                      if right ≠ left then correlation left right else 0 := by
                        simp
    _ = (∑ left : Index, correlation left left) +
        ∑ left : Index, ∑ right : Index,
          if right ≠ left then correlation left right else 0 := by
            rw [Finset.sum_add_distrib]
    _ = (∑ left : Index, correlation left left) +
        ∑ left : Index, ∑ group : Group,
          ∑ right ∈ fiber bucket left group, correlation left right := by
            congr 1
            apply Finset.sum_congr rfl
            intro left _
            symm
            exact sum_fiber_eq_offDiagonal bucket
              (fun right => correlation left right) left

/-- The strongest purely algebraic residual-pair estimate retained by this
module.  It uses an aggregate diagonal budget and keeps the actual weighted
fiber-cardinality sum.  No sign assumptions on the scale or charges are needed:
the signed pointwise off-diagonal upper bounds already imply the result. -/
theorem sum_pair_le_diagonalBudget_add_weightedFiberCharge
    {Index Group : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Group] [DecidableEq Group]
    (bucket : Index -> Index -> Group)
    (residualCount : Index -> Group -> ℕ)
    (charge : Index -> Group -> ℚ)
    (correlation : Index -> Index -> ℚ)
    (varianceScale diagonalBudget : ℚ)
    (hDiagonalBudget :
      (∑ index : Index, correlation index index) ≤ diagonalBudget)
    (hOffDiagonal : ∀ left right, left ≠ right ->
      correlation left right ≤
        varianceScale * (residualCount left (bucket left right) : ℚ) *
          charge left (bucket left right)) :
    (∑ left : Index, ∑ right : Index, correlation left right) ≤
      diagonalBudget + varianceScale *
        (∑ left : Index, ∑ group : Group,
          ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) * charge left group) := by
  classical
  rw [sum_pair_eq_sum_diagonal_add_sum_fibers bucket correlation]
  apply add_le_add hDiagonalBudget
  calc
    (∑ left : Index, ∑ group : Group,
        ∑ right ∈ fiber bucket left group, correlation left right) ≤
        ∑ left : Index, ∑ group : Group,
          ∑ _right ∈ fiber bucket left group,
            varianceScale * (residualCount left group : ℚ) *
              charge left group := by
                apply Finset.sum_le_sum
                intro left _
                apply Finset.sum_le_sum
                intro group _
                apply Finset.sum_le_sum
                intro right hright
                have hmem := Finset.mem_filter.1 hright
                simpa [hmem.2.2] using
                  hOffDiagonal left right (Ne.symm hmem.2.1)
    _ = ∑ left : Index, ∑ group : Group,
          varianceScale *
            (((fiber bucket left group).card : ℚ) *
              (residualCount left group : ℚ) * charge left group) := by
            apply Finset.sum_congr rfl
            intro left _
            apply Finset.sum_congr rfl
            intro group _
            simp
            ring
    _ = varianceScale *
        (∑ left : Index, ∑ group : Group,
          ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) * charge left group) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.mul_sum]

/-- Coarse residual-pair charge inequality.

The fiber-capacity and charge-budget premises are abstract inputs.  A future
trace/splicing development may prove such inputs, but this theorem itself
contains no canonical-path geometry.  Its only analytic premise is the signed
pointwise estimate `hOffDiagonal`. -/
theorem sum_pair_le_of_firstDivergenceCharge
    {Index Group : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Group] [DecidableEq Group]
    (bucket : Index -> Index -> Group)
    (residualCount : Index -> Group -> ℕ)
    (charge : Index -> Group -> ℚ)
    (correlation : Index -> Index -> ℚ)
    (totalMass : ℕ) (varianceScale chargeBudget : ℚ)
    (hScale : 0 ≤ varianceScale)
    (hBudget : 0 ≤ chargeBudget)
    (hCharge : ∀ left group, 0 ≤ charge left group)
    (hIndexCard : Fintype.card Index ≤ totalMass)
    (hFiberCapacity : ∀ left group,
      (fiber bucket left group).card * residualCount left group ≤ totalMass)
    (hChargeBudget : ∀ left,
      (∑ group : Group, charge left group) ≤ chargeBudget)
    (hDiagonal : ∀ index,
      correlation index index ≤ varianceScale)
    (hOffDiagonal : ∀ left right, left ≠ right ->
      correlation left right ≤
        varianceScale * (residualCount left (bucket left right) : ℚ) *
          charge left (bucket left right)) :
    (∑ left : Index, ∑ right : Index, correlation left right) ≤
      varianceScale *
        ((totalMass : ℚ) + (totalMass : ℚ) ^ 2 * chargeBudget) := by
  classical
  have hDiagonalSum :
      (∑ left : Index, correlation left left) ≤
        varianceScale * (totalMass : ℚ) := by
    calc
      (∑ left : Index, correlation left left) ≤
          ∑ _left : Index, varianceScale := by
            apply Finset.sum_le_sum
            intro left _
            exact hDiagonal left
      _ = (Fintype.card Index : ℚ) * varianceScale := by simp
      _ ≤ (totalMass : ℚ) * varianceScale := by
        apply mul_le_mul_of_nonneg_right _ hScale
        exact_mod_cast hIndexCard
      _ = varianceScale * (totalMass : ℚ) := by ring
  have hWeightedFiber (left : Index) (group : Group) :
      ((fiber bucket left group).card : ℚ) *
          (residualCount left group : ℚ) * charge left group ≤
        (totalMass : ℚ) * charge left group := by
    have hCapacityQ :
        ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) ≤ (totalMass : ℚ) := by
      exact_mod_cast hFiberCapacity left group
    exact mul_le_mul_of_nonneg_right hCapacityQ (hCharge left group)
  have hWeightedPerLeft (left : Index) :
      (∑ group : Group,
        ((fiber bucket left group).card : ℚ) *
          (residualCount left group : ℚ) * charge left group) ≤
        (totalMass : ℚ) * chargeBudget := by
    calc
      (∑ group : Group,
          ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) * charge left group) ≤
          ∑ group : Group, (totalMass : ℚ) * charge left group := by
            apply Finset.sum_le_sum
            intro group _
            exact hWeightedFiber left group
      _ = (totalMass : ℚ) * ∑ group : Group, charge left group := by
            rw [Finset.mul_sum]
      _ ≤ (totalMass : ℚ) * chargeBudget := by
        apply mul_le_mul_of_nonneg_left (hChargeBudget left)
        positivity
  have hWeightedTotal :
      (∑ left : Index, ∑ group : Group,
        ((fiber bucket left group).card : ℚ) *
          (residualCount left group : ℚ) * charge left group) ≤
        (totalMass : ℚ) ^ 2 * chargeBudget := by
    calc
      (∑ left : Index, ∑ group : Group,
          ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) * charge left group) ≤
          ∑ _left : Index, (totalMass : ℚ) * chargeBudget := by
            apply Finset.sum_le_sum
            intro left _
            exact hWeightedPerLeft left
      _ = (Fintype.card Index : ℚ) *
            ((totalMass : ℚ) * chargeBudget) := by simp
      _ ≤ (totalMass : ℚ) * ((totalMass : ℚ) * chargeBudget) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hIndexCard
        · exact mul_nonneg (by positivity) hBudget
      _ = (totalMass : ℚ) ^ 2 * chargeBudget := by ring
  calc
    (∑ left : Index, ∑ right : Index, correlation left right) ≤
        varianceScale * (totalMass : ℚ) + varianceScale *
          (∑ left : Index, ∑ group : Group,
            ((fiber bucket left group).card : ℚ) *
              (residualCount left group : ℚ) * charge left group) :=
      sum_pair_le_diagonalBudget_add_weightedFiberCharge
        bucket residualCount charge correlation varianceScale
          (varianceScale * (totalMass : ℚ)) hDiagonalSum hOffDiagonal
    _ ≤ varianceScale * (totalMass : ℚ) +
          varianceScale * ((totalMass : ℚ) ^ 2 * chargeBudget) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hWeightedTotal hScale) _
    _ = varianceScale *
        ((totalMass : ℚ) + (totalMass : ℚ) ^ 2 * chargeBudget) := by ring

/-! ## Accepted-input specialization -/

/-- Rewrite the selector second moment to accepted-input pairs and apply the
sharp abstract residual-pair charge.  The hypotheses remain explicit: in
particular, this theorem does not manufacture a trace bucket or a splice
bound. -/
theorem selector_highTailAverage_secondMoment_le_of_residualPairCharge
    {n k : Nat} {DSeed TSeed Group : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    [Fintype Group] [DecidableEq Group]
    (family : FiniteLayeredQueryProgramFamily n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (bucket : family.AcceptedModel -> family.AcceptedModel -> Group)
    (residualCount : family.AcceptedModel -> Group -> ℕ)
    (charge : family.AcceptedModel -> Group -> ℚ)
    (varianceScale diagonalBudget : ℚ)
    (hDiagonalBudget :
      (∑ accepted : family.AcceptedModel,
        finiteAverage (fun seed : DSeed × TSeed =>
          family.acceptedPointHighTailAverage accepted k
              (D seed.1) (T seed.2) *
            family.acceptedPointHighTailAverage accepted k
              (D seed.1) (T seed.2))) ≤ diagonalBudget)
    (hOffDiagonal : ∀ left right, left ≠ right ->
      finiteAverage (fun seed : DSeed × TSeed =>
        family.acceptedPointHighTailAverage left k
            (D seed.1) (T seed.2) *
          family.acceptedPointHighTailAverage right k
            (D seed.1) (T seed.2)) ≤
        varianceScale * (residualCount left (bucket left right) : ℚ) *
          charge left (bucket left right)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n -> Bool =>
        ratHighDegreeFourierTail
          family.selectorFBDD.ratAcceptanceIndicator k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      diagonalBudget + varianceScale *
        (∑ left : family.AcceptedModel, ∑ group : Group,
          ((fiber bucket left group).card : ℚ) *
            (residualCount left group : ℚ) * charge left group) := by
  classical
  rw [family.selector_highTailAverage_secondMoment_eq_sum_acceptedPointPairs D T]
  exact sum_pair_le_diagonalBudget_add_weightedFiberCharge
    bucket residualCount charge
      (fun left right => finiteAverage (fun seed : DSeed × TSeed =>
        family.acceptedPointHighTailAverage left k
            (D seed.1) (T seed.2) *
          family.acceptedPointHighTailAverage right k
            (D seed.1) (T seed.2)))
      varianceScale diagonalBudget hDiagonalBudget hOffDiagonal

end FiniteFirstDivergenceCharge

end OneTapeMagnification
end Frontier
end Pnp4
