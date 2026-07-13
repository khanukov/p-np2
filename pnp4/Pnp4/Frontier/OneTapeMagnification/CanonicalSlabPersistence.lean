import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualSegmentSlabReplay
import Pnp4.Frontier.OneTapeMagnification.WorkSlabPersistence

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Persistence of unvisited canonical slabs

Canonical block slabs are half-open subintervals of the represented work
cells `0, ..., T`.  Distinct block labels therefore give disjoint slabs.  The
proof below uses the already established exact equivalence between slab
membership and `workBlockAt`, rather than duplicating endpoint arithmetic.

The final theorem specializes `WorkSlabPersistence` to one actual maximal
group.  Replaying inside its visited canonical slab preserves an already equal
restriction of any other canonical slab, including across the final step,
which may leave the visited slab.  This is a two-slab persistence statement,
not a global cross-visit invariant or a fixed-alpha validator.
-/

/-- Every canonical exclusive upper endpoint is within the represented
endpoint `T + 1`. -/
theorem canonicalBlockUpperExclusive_le_total_add_one
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (block : Fin (T / b + 1)) :
    canonicalBlockUpperExclusive hb crossings block ≤ T + 1 := by
  unfold canonicalBlockUpperExclusive
  split
  · have hcut :=
      (canonicalBoundary hb crossings
        ⟨block.val, by assumption⟩).isLt
    omega
  · exact Nat.le_refl _

/-- Distinct canonical block labels have disjoint explicit slabs.  This also
covers `T = 0`; when there is only one block, the distinct-label premise is
simply impossible. -/
theorem canonicalBlockSlabsDisjoint_of_ne
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (first second : Fin (T / b + 1)) (hne : first ≠ second) :
    WorkSlabsDisjoint
      (canonicalBlockLower hb crossings first)
      (canonicalBlockWidth hb crossings first)
      (canonicalBlockLower hb crossings second)
      (canonicalBlockWidth hb crossings second) := by
  intro cell hfirst hsecond
  have hupper := canonicalBlockUpperExclusive_le_total_add_one
    hb crossings first
  have hendpoint := canonicalBlockLower_add_width_eq_upperExclusive
    hb crossings first
  have hcellLt : cell < T + 1 := by
    unfold WorkCellInSlab at hfirst
    omega
  let representedCell : Fin (T + 1) := ⟨cell, hcellLt⟩
  have hfirstLabel :
      workBlockAt hb crossings representedCell.val = first :=
    (workBlockAt_eq_iff_workCellInCanonicalSlab
      hb crossings representedCell first).mpr (by
        simpa only [representedCell] using hfirst)
  have hsecondLabel :
      workBlockAt hb crossings representedCell.val = second :=
    (workBlockAt_eq_iff_workCellInCanonicalSlab
      hb crossings representedCell second).mpr (by
        simpa only [representedCell] using hsecond)
  exact hne (hfirstLabel.symm.trans hsecondLabel)

/-- In the no-full-bucket case there is exactly one canonical block and its
slab is the complete represented interval `[0, T + 1)`.  This includes
`T = 0`. -/
theorem canonicalBlockSlab_eq_full_of_div_eq_zero
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (hzero : T / b = 0) (block : Fin (T / b + 1)) :
    canonicalBlockLower hb crossings block = 0 ∧
      canonicalBlockUpperExclusive hb crossings block = T + 1 ∧
      canonicalBlockWidth hb crossings block = T + 1 := by
  have hblockZero : block.val = 0 := by omega
  have hnotNext : ¬ block.val < T / b := by omega
  constructor
  · exact canonicalBlockLower_of_val_eq_zero
      hb crossings block hblockZero
  constructor
  · exact canonicalBlockUpperExclusive_of_not_val_lt
      hb crossings block hnotNext
  · rw [canonicalBlockWidth,
      canonicalBlockLower_of_val_eq_zero hb crossings block hblockZero,
      canonicalBlockUpperExclusive_of_not_val_lt
        hb crossings block hnotNext]
    omega

/-- Explicit zero-time instance: the unique canonical slab is the singleton
represented cell interval `[0, 1)`. -/
theorem canonicalBlockSlab_zero_time
    {b : Nat} (hb : 0 < b) (crossings : Fin 0 → Nat)
    (block : Fin (0 / b + 1)) :
    canonicalBlockLower hb crossings block = 0 ∧
      canonicalBlockUpperExclusive hb crossings block = 1 ∧
      canonicalBlockWidth hb crossings block = 1 := by
  simpa using canonicalBlockSlab_eq_full_of_div_eq_zero
    hb crossings (by simp) block

/-- Replaying one actual maximal group inside its canonical slab preserves an
already equal restriction of every other canonical slab.  The alternative
configuration may differ outside the two named slabs.  The conclusion is at
the segment exit, so the last transition is allowed to enter the protected
slab or leave the visited slab. -/
theorem restrictOtherCanonicalBlock_runFrom_eq_of_sameOn_actualGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (alternativeEntry : Configuration machine.State)
    (otherBlock : Fin (T / b + 1))
    (hother :
      actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before) ≠ otherBlock)
    (hvisitedEntry : SameOnWorkSlab
      (canonicalBlockLower hb
        (actualWorkBoundaryCounts machine input T)
        (actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before)))
      (canonicalBlockWidth hb
        (actualWorkBoundaryCounts machine input T)
        (actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before)))
      (run machine input (timeGroupsLength before)) alternativeEntry)
    (hotherEntry :
      restrictWorkSlab
          (canonicalBlockLower hb
            (actualWorkBoundaryCounts machine input T) otherBlock)
          (canonicalBlockWidth hb
            (actualWorkBoundaryCounts machine input T) otherBlock)
          (run machine input (timeGroupsLength before)).workTape =
        restrictWorkSlab
          (canonicalBlockLower hb
            (actualWorkBoundaryCounts machine input T) otherBlock)
          (canonicalBlockWidth hb
            (actualWorkBoundaryCounts machine input T) otherBlock)
          alternativeEntry.workTape) :
    restrictWorkSlab
        (canonicalBlockLower hb
          (actualWorkBoundaryCounts machine input T) otherBlock)
        (canonicalBlockWidth hb
          (actualWorkBoundaryCounts machine input T) otherBlock)
        (run machine input
          (timeGroupsLength before + group.length)).workTape =
      restrictWorkSlab
        (canonicalBlockLower hb
          (actualWorkBoundaryCounts machine input T) otherBlock)
        (canonicalBlockWidth hb
          (actualWorkBoundaryCounts machine input T) otherBlock)
        (runFrom machine input alternativeEntry group.length).workTape := by
  let visitedBlock := actualCanonicalWorkBlockAtTime machine input T b hb
    (timeGroupsLength before)
  let crossings := actualWorkBoundaryCounts machine input T
  let visitedBase := canonicalBlockLower hb crossings visitedBlock
  let visitedWidth := canonicalBlockWidth hb crossings visitedBlock
  let protectedBase := canonicalBlockLower hb crossings otherBlock
  let protectedWidth := canonicalBlockWidth hb crossings otherBlock
  have hdisjoint : WorkSlabsDisjoint
      visitedBase visitedWidth protectedBase protectedWidth := by
    exact canonicalBlockSlabsDisjoint_of_ne
      hb crossings visitedBlock otherBlock hother
  have hinside : ∀ time, time < group.length →
      WorkCellInSlab visitedBase visitedWidth
        (runFrom machine input
          (run machine input (timeGroupsLength before)) time).workHead := by
    intro time htime
    have hglobal := actualCanonicalWorkBlockGroup_workHead_in_slab
      machine input T b hb before after group hsplit time htime
    have hrun := runFrom_add_eq_runFrom_runFrom machine input
      (initialConfiguration machine) (timeGroupsLength before) time
    change WorkCellInSlab visitedBase visitedWidth
      (runFrom machine input
        (run machine input (timeGroupsLength before)) time).workHead
    simpa [visitedBase, visitedWidth, visitedBlock, crossings, run] using
      congrArg Configuration.workHead hrun ▸ hglobal
  have hpersistence :=
    restrictWorkSlab_runFrom_eq_of_sameOn_disjoint_visitedSlab
      machine input
      (visitedBase := visitedBase) (visitedWidth := visitedWidth)
      (protectedBase := protectedBase) (protectedWidth := protectedWidth)
      (steps := group.length) hvisitedEntry hotherEntry hdisjoint hinside
  change restrictWorkSlab protectedBase protectedWidth
      (run machine input
        (timeGroupsLength before + group.length)).workTape =
    restrictWorkSlab protectedBase protectedWidth
      (runFrom machine input alternativeEntry group.length).workTape
  rw [run, runFrom_add_eq_runFrom_runFrom]
  exact hpersistence

end OneTapeMagnification
end Frontier
end Pnp4
