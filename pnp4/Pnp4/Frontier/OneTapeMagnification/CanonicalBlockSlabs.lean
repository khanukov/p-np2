import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalWorkBlocks
import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical work blocks as explicit tape slabs

`CanonicalWorkBlocks` labels the represented work cells `0, ..., T` by the
number of selected cuts strictly to their left.  This file gives every label
an explicit half-open slab.  Block zero starts at cell zero, a nonzero block
starts immediately to the right of the preceding cut, a nonfinal block ends
immediately to the right of its next cut, and the final block ends at `T + 1`.

The resulting slab is nonempty and has width at most `2 * b`, including the
degenerate case `T / b = 0`.  Membership agrees exactly with `workBlockAt` on
represented cells.  The final theorem specializes this fact to an actual
blank-start work-head trajectory, supplying precisely the `WorkCellInSlab`
hypothesis consumed by `runFrom_sameOnWorkSlab`.

No replay schedule, branching-program construction, width bound for such a
program, or input-independent canonical transcript is asserted here.
-/

/-- Inclusive lower endpoint of a canonical block. -/
noncomputable def canonicalBlockLower {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) : Nat :=
  if hzero : block.val = 0 then 0
  else
    (canonicalBoundary hb crossings
      ⟨block.val - 1, by omega⟩).val + 1

/-- Exclusive upper endpoint of a canonical block. -/
noncomputable def canonicalBlockUpperExclusive {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) : Nat :=
  if hnext : block.val < T / b then
    (canonicalBoundary hb crossings ⟨block.val, hnext⟩).val + 1
  else T + 1

/-- Width of the half-open slab assigned to a canonical block. -/
noncomputable def canonicalBlockWidth {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) : Nat :=
  canonicalBlockUpperExclusive hb crossings block -
    canonicalBlockLower hb crossings block

@[simp]
theorem canonicalBlockLower_of_val_eq_zero {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1))
    (hzero : block.val = 0) :
    canonicalBlockLower hb crossings block = 0 := by
  simp [canonicalBlockLower, hzero]

theorem canonicalBlockLower_of_val_pos {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1))
    (hpos : 0 < block.val) :
    canonicalBlockLower hb crossings block =
      (canonicalBoundary hb crossings
        ⟨block.val - 1, by omega⟩).val + 1 := by
  simp [canonicalBlockLower, Nat.ne_of_gt hpos]

theorem canonicalBlockUpperExclusive_of_val_lt {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1))
    (hnext : block.val < T / b) :
    canonicalBlockUpperExclusive hb crossings block =
      (canonicalBoundary hb crossings ⟨block.val, hnext⟩).val + 1 := by
  simp [canonicalBlockUpperExclusive, hnext]

@[simp]
theorem canonicalBlockUpperExclusive_of_not_val_lt {T b : Nat}
    (hb : 0 < b) (crossings : Fin T → Nat)
    (block : Fin (T / b + 1)) (hnext : ¬ block.val < T / b) :
    canonicalBlockUpperExclusive hb crossings block = T + 1 := by
  simp [canonicalBlockUpperExclusive, hnext]

/-- A represented cell carrying `block`'s label lies between the explicit
endpoints of that block. -/
theorem canonicalBlock_bounds_of_workBlockAt_eq {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1))
    (hblock : workBlockAt hb crossings cell.val = block) :
    canonicalBlockLower hb crossings block ≤ cell.val ∧
      cell.val < canonicalBlockUpperExclusive hb crossings block := by
  have hval := congrArg Fin.val hblock
  constructor
  · by_cases hzero : block.val = 0
    · rw [canonicalBlockLower_of_val_eq_zero hb crossings block hzero]
      exact Nat.zero_le _
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      let previous : Fin (T / b) :=
        ⟨block.val - 1, by omega⟩
      have hindex : previous.val <
          (workBlockAt hb crossings cell.val).val := by
        dsimp only [previous]
        omega
      have hcut :
          (canonicalBoundary hb crossings previous).val < cell.val :=
        (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
          hb crossings previous cell.val).mpr hindex
      rw [canonicalBlockLower_of_val_pos hb crossings block hpos]
      change (canonicalBoundary hb crossings previous).val + 1 ≤ cell.val
      omega
  · by_cases hnext : block.val < T / b
    · let next : Fin (T / b) := ⟨block.val, hnext⟩
      have hnotCut : ¬
          ((canonicalBoundary hb crossings next).val < cell.val) := by
        intro hcut
        have hindex :=
          (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
            hb crossings next cell.val).mp hcut
        dsimp only [next] at hindex
        omega
      have hcellLe : cell.val ≤
          (canonicalBoundary hb crossings next).val :=
        Nat.le_of_not_gt hnotCut
      rw [canonicalBlockUpperExclusive_of_val_lt
        hb crossings block hnext]
      change cell.val < (canonicalBoundary hb crossings next).val + 1
      omega
    · rw [canonicalBlockUpperExclusive_of_not_val_lt
        hb crossings block hnext]
      exact cell.isLt

/-- Conversely, endpoint membership determines the canonical block label. -/
theorem workBlockAt_eq_of_canonicalBlock_bounds {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1))
    (hbounds : canonicalBlockLower hb crossings block ≤ cell.val ∧
      cell.val < canonicalBlockUpperExclusive hb crossings block) :
    workBlockAt hb crossings cell.val = block := by
  have hBlockLeLabel : block.val ≤
      (workBlockAt hb crossings cell.val).val := by
    by_cases hzero : block.val = 0
    · omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      let previous : Fin (T / b) :=
        ⟨block.val - 1, by omega⟩
      have hlower := hbounds.1
      rw [canonicalBlockLower_of_val_pos hb crossings block hpos] at hlower
      have hcut :
          (canonicalBoundary hb crossings previous).val < cell.val := by
        change (canonicalBoundary hb crossings previous).val + 1 ≤
          cell.val at hlower
        omega
      have hindex :=
        (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
          hb crossings previous cell.val).mp hcut
      dsimp only [previous] at hindex
      omega
  have hLabelLeBlock : (workBlockAt hb crossings cell.val).val ≤
      block.val := by
    by_cases hnext : block.val < T / b
    · let next : Fin (T / b) := ⟨block.val, hnext⟩
      have hupper := hbounds.2
      rw [canonicalBlockUpperExclusive_of_val_lt
        hb crossings block hnext] at hupper
      have hnotCut : ¬
          ((canonicalBoundary hb crossings next).val < cell.val) := by
        change cell.val < (canonicalBoundary hb crossings next).val + 1
          at hupper
        omega
      have hnotIndex : ¬ next.val <
          (workBlockAt hb crossings cell.val).val := by
        intro hindex
        exact hnotCut
          ((canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
            hb crossings next cell.val).mpr hindex)
      dsimp only [next] at hnotIndex
      omega
    · have hlabel := (workBlockAt hb crossings cell.val).isLt
      omega
  apply Fin.ext
  exact Nat.le_antisymm hLabelLeBlock hBlockLeLabel

/-- Exact agreement between the rank classifier and the explicit half-open
slab on represented work cells. -/
theorem workBlockAt_eq_iff_canonicalBlock_bounds {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1)) :
    workBlockAt hb crossings cell.val = block ↔
      canonicalBlockLower hb crossings block ≤ cell.val ∧
        cell.val < canonicalBlockUpperExclusive hb crossings block := by
  constructor
  · exact canonicalBlock_bounds_of_workBlockAt_eq hb crossings cell block
  · exact workBlockAt_eq_of_canonicalBlock_bounds hb crossings cell block

/-- Every canonical slab has a strictly smaller lower endpoint than upper
endpoint, including when there are no selected cuts. -/
theorem canonicalBlockLower_lt_upperExclusive {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) :
    canonicalBlockLower hb crossings block <
      canonicalBlockUpperExclusive hb crossings block := by
  by_cases hNoBlocks : T / b = 0
  · have hzero : block.val = 0 := by omega
    rw [canonicalBlockLower_of_val_eq_zero hb crossings block hzero,
      canonicalBlockUpperExclusive_of_not_val_lt hb crossings block]
    · omega
    · omega
  · have hBlocks : 0 < T / b := Nat.pos_of_ne_zero hNoBlocks
    by_cases hzero : block.val = 0
    · have hnext : block.val < T / b := by omega
      rw [canonicalBlockLower_of_val_eq_zero hb crossings block hzero,
        canonicalBlockUpperExclusive_of_val_lt
          hb crossings block hnext]
      omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      by_cases hlast : block.val = T / b
      · have hnotNext : ¬ block.val < T / b := by omega
        rw [canonicalBlockLower_of_val_pos hb crossings block hpos,
          canonicalBlockUpperExclusive_of_not_val_lt
            hb crossings block hnotNext]
        have hcutLt :=
          (canonicalBoundary hb crossings
            ⟨block.val - 1, by omega⟩).isLt
        omega
      · have hnext : block.val < T / b := by
          have hle : block.val ≤ T / b := Nat.le_of_lt_succ block.isLt
          omega
        let previous : Fin (T / b) :=
          ⟨block.val - 1, by omega⟩
        let next : Fin (T / b) := ⟨block.val, hnext⟩
        have hindex : previous < next := by
          change block.val - 1 < block.val
          omega
        have hcuts :=
          canonicalBoundary_lt_of_index_lt hb crossings hindex
        rw [canonicalBlockLower_of_val_pos hb crossings block hpos,
          canonicalBlockUpperExclusive_of_val_lt
            hb crossings block hnext]
        change (canonicalBoundary hb crossings previous).val + 1 <
          (canonicalBoundary hb crossings next).val + 1
        omega

/-- Every canonical slab contains at least one work cell. -/
theorem canonicalBlockWidth_pos {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) :
    0 < canonicalBlockWidth hb crossings block := by
  exact Nat.sub_pos_of_lt
    (canonicalBlockLower_lt_upperExclusive hb crossings block)

/-- The stored width recovers the exclusive endpoint without truncated-
subtraction loss. -/
theorem canonicalBlockLower_add_width_eq_upperExclusive {T b : Nat}
    (hb : 0 < b) (crossings : Fin T → Nat)
    (block : Fin (T / b + 1)) :
    canonicalBlockLower hb crossings block +
        canonicalBlockWidth hb crossings block =
      canonicalBlockUpperExclusive hb crossings block := by
  have horder :=
    canonicalBlockLower_lt_upperExclusive hb crossings block
  unfold canonicalBlockWidth
  omega

/-- Every canonical slab has width at most `2 * b`.  The proof treats the
no-cut, first, middle, and final slabs according to their exact endpoint
conventions. -/
theorem canonicalBlockWidth_le_two_mul {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (block : Fin (T / b + 1)) :
    canonicalBlockWidth hb crossings block ≤ 2 * b := by
  by_cases hNoBlocks : T / b = 0
  · have hzero : block.val = 0 := by omega
    have hTlt : T < b := Nat.lt_of_div_eq_zero hb hNoBlocks
    rw [canonicalBlockWidth,
      canonicalBlockLower_of_val_eq_zero hb crossings block hzero,
      canonicalBlockUpperExclusive_of_not_val_lt hb crossings block]
    · omega
    · omega
  · have hBlocks : 0 < T / b := Nat.pos_of_ne_zero hNoBlocks
    by_cases hzero : block.val = 0
    · have hnext : block.val < T / b := by omega
      have hfirst :
          (⟨block.val, hnext⟩ : Fin (T / b)) =
            firstFullBucketIndex hBlocks := by
        apply Fin.ext
        simp [hzero, firstFullBucketIndex]
      have hgap :=
        firstCanonicalBoundary_lt_blockSize hb hBlocks crossings
      rw [canonicalBlockWidth,
        canonicalBlockLower_of_val_eq_zero hb crossings block hzero,
        canonicalBlockUpperExclusive_of_val_lt
          hb crossings block hnext, hfirst]
      omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      by_cases hlast : block.val = T / b
      · have hnotNext : ¬ block.val < T / b := by omega
        have hlastIndex :
            (⟨block.val - 1, by omega⟩ : Fin (T / b)) =
              lastFullBucketIndex hBlocks := by
          apply Fin.ext
          change block.val - 1 = T / b - 1
          rw [hlast]
        have hgap :=
          total_lt_lastCanonicalBoundary_add_two_mul
            hb hBlocks crossings
        rw [canonicalBlockWidth,
          canonicalBlockLower_of_val_pos hb crossings block hpos,
          canonicalBlockUpperExclusive_of_not_val_lt
            hb crossings block hnotNext, hlastIndex]
        omega
      · have hnext : block.val < T / b := by
          have hle : block.val ≤ T / b := Nat.le_of_lt_succ block.isLt
          omega
        let previous : Fin (T / b) :=
          ⟨block.val - 1, by omega⟩
        let next : Fin (T / b) := ⟨block.val, hnext⟩
        have hAdjacent : next.val = previous.val + 1 := by
          simp only [previous, next]
          omega
        have hgap :=
          (canonicalBoundary_adjacent_gap_lt_two_mul
            hb crossings previous next hAdjacent).2
        rw [canonicalBlockWidth,
          canonicalBlockLower_of_val_pos hb crossings block hpos,
          canonicalBlockUpperExclusive_of_val_lt
            hb crossings block hnext]
        change
          (canonicalBoundary hb crossings next).val + 1 -
              ((canonicalBoundary hb crossings previous).val + 1) ≤
            2 * b
        omega

/-- A represented cell with a given canonical label belongs to the finite
slab used by `LocalBlockReplay`. -/
theorem workCellInSlab_of_workBlockAt_eq {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1))
    (hblock : workBlockAt hb crossings cell.val = block) :
    WorkCellInSlab
      (canonicalBlockLower hb crossings block)
      (canonicalBlockWidth hb crossings block)
      cell.val := by
  have hbounds :=
    canonicalBlock_bounds_of_workBlockAt_eq
      hb crossings cell block hblock
  have horder :=
    canonicalBlockLower_lt_upperExclusive hb crossings block
  unfold WorkCellInSlab canonicalBlockWidth
  constructor
  · exact hbounds.1
  · omega

/-- Direct bridge from canonical labels to the exact slab-membership predicate
used by local replay. -/
theorem workBlockAt_eq_iff_workCellInCanonicalSlab {T b : Nat}
    (hb : 0 < b) (crossings : Fin T → Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1)) :
    workBlockAt hb crossings cell.val = block ↔
      WorkCellInSlab
        (canonicalBlockLower hb crossings block)
        (canonicalBlockWidth hb crossings block)
        cell.val := by
  constructor
  · exact workCellInSlab_of_workBlockAt_eq hb crossings cell block
  · intro hslab
    apply workBlockAt_eq_of_canonicalBlock_bounds hb crossings cell block
    unfold WorkCellInSlab at hslab
    have hendpoint :=
      canonicalBlockLower_add_width_eq_upperExclusive
        hb crossings block
    constructor
    · exact hslab.1
    · omega

/-- Exact local-replay premise for a represented trajectory time starting
from an arbitrary configuration. -/
theorem workHeadTrajectoryFrom_in_canonicalBlockSlab
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat)
    (hrepresented : workHeadTrajectoryFrom machine input config time ≤ T)
    (block : Fin (T / b + 1))
    (hblock : workBlockAt hb crossings
      (workHeadTrajectoryFrom machine input config time) = block) :
    WorkCellInSlab
      (canonicalBlockLower hb crossings block)
      (canonicalBlockWidth hb crossings block)
      (runFrom machine input config time).workHead := by
  let cell : Fin (T + 1) :=
    ⟨workHeadTrajectoryFrom machine input config time, by omega⟩
  have hcell :=
    workCellInSlab_of_workBlockAt_eq hb crossings cell block (by
      simpa only [cell] using hblock)
  simpa only [cell, workHeadTrajectoryFrom] using hcell

/-- Exact local-replay premise for any represented time of a blank-start
trajectory carrying the advertised canonical block label. -/
theorem workHeadTrajectory_in_canonicalBlockSlab
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (machine : DeterministicMachine) (input : List Bool)
    (time : Nat) (htime : time ≤ T) (block : Fin (T / b + 1))
    (hblock : canonicalWorkBlockAtTime hb crossings machine input time =
      block) :
    WorkCellInSlab
      (canonicalBlockLower hb crossings block)
      (canonicalBlockWidth hb crossings block)
      (workHeadTrajectory machine input time) := by
  have hhead := workHeadTrajectory_le_time machine input time
  have hrepresented :
      workHeadTrajectoryFrom machine input (initialConfiguration machine)
          time ≤ T := by
    have hfromLe :
        workHeadTrajectoryFrom machine input (initialConfiguration machine)
            time ≤ time := by
      simpa only [workHeadTrajectory] using hhead
    exact hfromLe.trans htime
  have hfrom :=
    workHeadTrajectoryFrom_in_canonicalBlockSlab
      hb crossings machine input (initialConfiguration machine) time
      hrepresented block
      (by simpa only [canonicalWorkBlockAtTime, workHeadTrajectory] using
        hblock)
  simpa only [workHeadTrajectory, workHeadTrajectoryFrom] using hfrom

end OneTapeMagnification
end Frontier
end Pnp4
