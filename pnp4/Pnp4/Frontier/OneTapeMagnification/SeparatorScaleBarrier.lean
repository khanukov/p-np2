import Mathlib.Data.Nat.Basic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Single-scale separator accounting

The block/transcript simulation behind the published one-tape argument has two
opposing costs.  At a chosen scale, one cost grows with the amount of local
work retained inside a block, while the other grows with the number of block
interfaces crossed by the computation.  Before those costs are connected to
an actual machine simulation, their common numerical core is the product
coverage inequality

`time ≤ blockCost * transcriptCost`.

This file isolates exactly what that inequality implies.  If one common
budget is required to dominate both costs, its square must dominate `time`.
Equivalently, any budget whose square is smaller than `time` must fail on at
least one side.  This is the precise single-scale square-root tradeoff.

The hypotheses below do **not** assert that every one-tape simulation, PRG, or
HSG must obey this accounting.  In particular, a collective construction that
uses coherence among canonical path transcripts could avoid paying for the
two sides independently.  Establishing such a construction is the open step.
-/

/-- The larger of the local-block and path-transcript costs at one scale. -/
def singleScaleSeparatorCost (blockCost transcriptCost : Nat) : Nat :=
  max blockCost transcriptCost

/-- Product coverage forces the square of the larger single-scale cost to
cover the simulated running time. -/
theorem singleScale_time_le_max_cost_squared
    {time blockCost transcriptCost : Nat}
    (hcover : time ≤ blockCost * transcriptCost) :
    time ≤ (singleScaleSeparatorCost blockCost transcriptCost) ^ 2 := by
  calc
    time ≤ blockCost * transcriptCost := hcover
    _ ≤ (max blockCost transcriptCost) * (max blockCost transcriptCost) :=
      Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    _ = (singleScaleSeparatorCost blockCost transcriptCost) ^ 2 := by
      simp [singleScaleSeparatorCost, Nat.pow_succ]

/-- If both sides fit under one budget, product coverage makes the running
time fit under the square of that budget. -/
theorem singleScale_time_le_budget_squared
    {time blockCost transcriptCost budget : Nat}
    (hcover : time ≤ blockCost * transcriptCost)
    (hBlock : blockCost ≤ budget)
    (hTranscript : transcriptCost ≤ budget) :
    time ≤ budget ^ 2 := by
  calc
    time ≤ blockCost * transcriptCost := hcover
    _ ≤ budget * budget := Nat.mul_le_mul hBlock hTranscript
    _ = budget ^ 2 := by simp [Nat.pow_succ]

/-- Contrapositive form of the tradeoff: below square-root capacity, at least
one of the two independently charged costs exceeds the common budget. -/
theorem singleScale_budget_exceeded_on_one_side
    {time blockCost transcriptCost budget : Nat}
    (hcover : time ≤ blockCost * transcriptCost)
    (hTooSmall : budget ^ 2 < time) :
    budget < blockCost ∨ budget < transcriptCost := by
  by_contra hFits
  have hNotFits := not_or.mp hFits
  have hBlock : blockCost ≤ budget := Nat.le_of_not_gt hNotFits.1
  have hTranscript : transcriptCost ≤ budget := Nat.le_of_not_gt hNotFits.2
  have hTime : time ≤ budget ^ 2 :=
    singleScale_time_le_budget_squared hcover hBlock hTranscript
  exact (Nat.not_lt_of_ge hTime) hTooSmall

end OneTapeMagnification
end Frontier
end Pnp4
