import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Persistence of a slab while the work head is elsewhere

Local replay explains what happens inside the slab currently being visited.
The complementary fact needed for block-by-block gluing is that a different
slab is unchanged while every pre-transition work head stays outside it.  The
last transition may enter the protected slab: the write is performed at the
old head, so its contents are still preserved.

These statements are exact tape-locality lemmas.  They do not construct the
cross-visit invariant needed by a fixed-alpha validator, nor a branching
program or width bound.
-/

/-- Two slabs are disjoint when no absolute work cell belongs to both. -/
def WorkSlabsDisjoint
    (firstBase firstWidth secondBase secondWidth : Nat) : Prop :=
  ∀ cell, WorkCellInSlab firstBase firstWidth cell →
    ¬ WorkCellInSlab secondBase secondWidth cell

/-- Ordered nonoverlapping half-open intervals define disjoint slabs. -/
theorem workSlabsDisjoint_of_first_end_le_second_base
    {firstBase firstWidth secondBase secondWidth : Nat}
    (hordered : firstBase + firstWidth ≤ secondBase) :
    WorkSlabsDisjoint firstBase firstWidth secondBase secondWidth := by
  intro cell hfirst hsecond
  unfold WorkCellInSlab at hfirst hsecond
  omega

/-- Disjointness of slabs is symmetric. -/
theorem WorkSlabsDisjoint.symm
    {firstBase firstWidth secondBase secondWidth : Nat}
    (hdisjoint : WorkSlabsDisjoint
      firstBase firstWidth secondBase secondWidth) :
    WorkSlabsDisjoint secondBase secondWidth firstBase firstWidth := by
  intro cell hsecond hfirst
  exact hdisjoint cell hfirst hsecond

/-- Applying one instruction cannot change a slab which does not contain the
old work-head cell.  The new work head may enter that slab. -/
theorem restrictWorkSlab_applyInstruction_of_not_mem
    {State : Type} (config : Configuration State)
    (instruction : Instruction State) (base width : Nat)
    (houtside : ¬ WorkCellInSlab base width config.workHead) :
    restrictWorkSlab base width
        (applyInstruction config instruction).workTape =
      restrictWorkSlab base width config.workTape := by
  exact restrictWorkSlab_workTape_write_of_not_mem
    config.workTape instruction.write houtside

/-- One machine step preserves every slab outside the old work head.  Halted
stuttering is included. -/
theorem restrictWorkSlab_step_of_not_mem
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (base width : Nat)
    (houtside : ¬ WorkCellInSlab base width config.workHead) :
    restrictWorkSlab base width (step machine input config).workTape =
      restrictWorkSlab base width config.workTape := by
  unfold step
  split
  · rfl
  · exact restrictWorkSlab_applyInstruction_of_not_mem
      config _ base width houtside

/-- A finite run preserves a slab when every pre-transition head is outside
it.  No condition is imposed on the head after the final transition. -/
theorem restrictWorkSlab_runFrom_eq_of_avoids
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (base width steps : Nat)
    (havoids : ∀ time, time < steps →
      ¬ WorkCellInSlab base width
        (runFrom machine input config time).workHead) :
    restrictWorkSlab base width
        (runFrom machine input config steps).workTape =
      restrictWorkSlab base width config.workTape := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [runFrom_succ_eq_step_runFrom]
      calc
        restrictWorkSlab base width
            (step machine input
              (runFrom machine input config steps)).workTape =
            restrictWorkSlab base width
              (runFrom machine input config steps).workTape :=
          restrictWorkSlab_step_of_not_mem machine input _ base width
            (havoids steps (by omega))
        _ = restrictWorkSlab base width config.workTape :=
          ih (fun time htime => havoids time (by omega))

/-- Equal protected-slab contents remain equal across two runs which both
avoid that slab.  This is the explicit midpoint-tape premise consumed by a
later two-slab composition. -/
theorem restrictWorkSlab_runFrom_eq_of_eq_and_both_avoid
    (machine : DeterministicMachine) (input : List Bool)
    (left right : Configuration machine.State) (base width steps : Nat)
    (hentry : restrictWorkSlab base width left.workTape =
      restrictWorkSlab base width right.workTape)
    (hleft : ∀ time, time < steps →
      ¬ WorkCellInSlab base width
        (runFrom machine input left time).workHead)
    (hright : ∀ time, time < steps →
      ¬ WorkCellInSlab base width
        (runFrom machine input right time).workHead) :
    restrictWorkSlab base width
        (runFrom machine input left steps).workTape =
      restrictWorkSlab base width
        (runFrom machine input right steps).workTape := by
  rw [restrictWorkSlab_runFrom_eq_of_avoids
      machine input left base width steps hleft,
    restrictWorkSlab_runFrom_eq_of_avoids
      machine input right base width steps hright]
  exact hentry

/-- Replaying inside one slab preserves an already equal, disjoint protected
slab on both runs.  Equality of the work heads along the alternative run is
derived from local replay; it is not an extra premise.

This theorem supplies the explicit protected-slab equality required at the
midpoint of a two-slab composition, provided that equality was already true
at entry.  Establishing that entry equality across all later revisits remains
the separate block-grouped invariant. -/
theorem restrictWorkSlab_runFrom_eq_of_sameOn_disjoint_visitedSlab
    (machine : DeterministicMachine) (input : List Bool)
    {left right : Configuration machine.State}
    {visitedBase visitedWidth protectedBase protectedWidth steps : Nat}
    (hvisitedEntry : SameOnWorkSlab
      visitedBase visitedWidth left right)
    (hprotectedEntry :
      restrictWorkSlab protectedBase protectedWidth left.workTape =
        restrictWorkSlab protectedBase protectedWidth right.workTape)
    (hdisjoint : WorkSlabsDisjoint
      visitedBase visitedWidth protectedBase protectedWidth)
    (hinside : ∀ time, time < steps →
      WorkCellInSlab visitedBase visitedWidth
        (runFrom machine input left time).workHead) :
    restrictWorkSlab protectedBase protectedWidth
        (runFrom machine input left steps).workTape =
      restrictWorkSlab protectedBase protectedWidth
        (runFrom machine input right steps).workTape := by
  have hleftAvoids : ∀ time, time < steps →
      ¬ WorkCellInSlab protectedBase protectedWidth
        (runFrom machine input left time).workHead := by
    intro time htime
    exact hdisjoint _ (hinside time htime)
  have hrightAvoids : ∀ time, time < steps →
      ¬ WorkCellInSlab protectedBase protectedWidth
        (runFrom machine input right time).workHead := by
    intro time htime
    have hsameAt := runFrom_sameOnWorkSlab_same_input (steps := time)
      machine input
      hvisitedEntry (fun earlier hearlier =>
        hinside earlier (by omega : earlier < steps))
    have hnot := hdisjoint _ (hinside time htime)
    intro hrightProtected
    apply hnot
    rw [hsameAt.2.2.1]
    exact hrightProtected
  exact restrictWorkSlab_runFrom_eq_of_eq_and_both_avoid
    machine input left right protectedBase protectedWidth steps
    hprotectedEntry hleftAvoids hrightAvoids

end OneTapeMagnification
end Frontier
end Pnp4
