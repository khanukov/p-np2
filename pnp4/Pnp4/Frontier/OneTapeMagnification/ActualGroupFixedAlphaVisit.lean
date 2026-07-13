import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualSegmentSlabReplay
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaBlockVisitReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One actual maximal group as a fixed-alpha block visit

`FixedAlphaBlockVisitReplay` deliberately accepts an abstract advertised visit
list.  This file supplies a one-group completeness bridge.  A named maximal
group of the actual canonical work-block decomposition determines a strict
bounded visit whose endpoints are sampled from the actual run.  Its block
geometry is then read from the offsets of the actual timed alpha.

Starting with the actual entry slab restriction, the fixed-alpha validator
accepts this visit.  Its unique output slab is exactly the actual slab
restriction at group exit.  The proof uses the advertised/actual geometry
bridge and the generic converse replay theorem; no new contract, source,
provider, or lower-bound assumption is introduced.

This is intentionally a single-group completeness theorem.  It neither
constructs the advertised visit list from an arbitrary timed word nor proves
that a guessed alpha is sound.  Blank initialization of the first visit and
threading the carried slab through all revisits remain separate composition
steps.
-/

/-- Bounded endpoint metadata sampled from an actual blank-start run at any
represented time `time ≤ T`. -/
def fixedAlphaVisitEndpointAtRunTime
    (machine : DeterministicMachine) (input : List Bool)
    (T time : Nat) (htime : time ≤ T) :
    FixedAlphaVisitEndpoint machine.State T :=
  { state := (run machine input time).state
    inputHead :=
      ⟨(run machine input time).inputHead, by
        exact Nat.lt_succ_of_le
          ((inputHead_run_le_time_for_crossingRecord
            machine input time).trans htime)⟩
    workHead :=
      ⟨(run machine input time).workHead, by
        exact Nat.lt_succ_of_le (by
          have hhead : (run machine input time).workHead ≤ time := by
            simpa [workHeadTrajectory, workHeadTrajectoryFrom, run] using
              (workHeadTrajectory_le_time machine input time)
          exact hhead.trans htime)⟩ }

@[simp]
theorem fixedAlphaVisitEndpointAtRunTime_state
    (machine : DeterministicMachine) (input : List Bool)
    (T time : Nat) (htime : time ≤ T) :
    (fixedAlphaVisitEndpointAtRunTime machine input T time htime).state =
      (run machine input time).state :=
  rfl

@[simp]
theorem fixedAlphaVisitEndpointAtRunTime_inputHead_val
    (machine : DeterministicMachine) (input : List Bool)
    (T time : Nat) (htime : time ≤ T) :
    (fixedAlphaVisitEndpointAtRunTime
      machine input T time htime).inputHead.val =
      (run machine input time).inputHead :=
  rfl

@[simp]
theorem fixedAlphaVisitEndpointAtRunTime_workHead_val
    (machine : DeterministicMachine) (input : List Bool)
    (T time : Nat) (htime : time ≤ T) :
    (fixedAlphaVisitEndpointAtRunTime
      machine input T time htime).workHead.val =
      (run machine input time).workHead :=
  rfl

/-- The actual canonical block label of the group following `before`. -/
noncomputable def actualCanonicalWorkBlockGroupLabel
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) : Fin (T / b + 1) :=
  actualCanonicalWorkBlockAtTime machine input T b hb
    (timeGroupsLength before)

/-- A named nonempty maximal group determines a strict advertised visit with
the exact cumulative entry and exit times and actual endpoint metadata. -/
noncomputable def actualCanonicalWorkBlockGroupVisit
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    FixedAlphaBlockVisit machine.State T := by
  have hend : timeGroupsLength before + group.length ≤ T :=
    actualCanonicalWorkBlockGroup_end_le_steps
      machine input T b hb before after group hsplit
  have hnonempty : group ≠ [] :=
    actualCanonicalWorkBlockGroup_nonempty
      machine input T b hb before after group hsplit
  have hlength : 0 < group.length := List.length_pos_iff.mpr hnonempty
  exact
    { entryTime := ⟨timeGroupsLength before, by omega⟩
      exitTime := ⟨timeGroupsLength before + group.length, by omega⟩
      entryTime_lt_exitTime := by
        change timeGroupsLength before <
          timeGroupsLength before + group.length
        omega
      entry := fixedAlphaVisitEndpointAtRunTime machine input T
        (timeGroupsLength before) (by omega)
      exit := fixedAlphaVisitEndpointAtRunTime machine input T
        (timeGroupsLength before + group.length) hend }

@[simp]
theorem actualCanonicalWorkBlockGroupVisit_entryTime_val
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    (actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit).entryTime.val =
      timeGroupsLength before := by
  rfl

@[simp]
theorem actualCanonicalWorkBlockGroupVisit_exitTime_val
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    (actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit).exitTime.val =
      timeGroupsLength before + group.length := by
  rfl

@[simp]
theorem actualCanonicalWorkBlockGroupVisit_steps
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    (actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit).steps =
      group.length := by
  unfold FixedAlphaBlockVisit.steps
  rw [actualCanonicalWorkBlockGroupVisit_entryTime_val,
    actualCanonicalWorkBlockGroupVisit_exitTime_val]
  omega

/-- Actual work-tape restriction for any named block and represented time,
expressed in the geometry advertised by the actual timed alpha. -/
noncomputable def actualFixedAlphaBlockSlabAtTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (block : Fin (T / b + 1)) (time : Nat) :
    WorkSlab
      (advertisedBlockWidth
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        block) :=
  restrictWorkSlab
    (advertisedBlockLower
      (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
      block)
    (advertisedBlockWidth
      (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
      block)
    (run machine input time).workTape

/-- Every advertised block restriction is literally blank at actual time
zero. -/
@[simp]
theorem actualFixedAlphaBlockSlabAtTime_zero
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (block : Fin (T / b + 1)) :
    actualFixedAlphaBlockSlabAtTime machine input T b hb block 0 =
      blankWorkSlab
        (advertisedBlockWidth
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          block) := by
  rw [actualFixedAlphaBlockSlabAtTime]
  change restrictWorkSlab _ _ WorkTape.blank = blankWorkSlab _
  exact restrictWorkSlab_blank _ _

/-- The carried slab at this actual group's entry, expressed entirely in the
geometry advertised by the actual timed alpha. -/
noncomputable def actualCanonicalWorkBlockGroupEntrySlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) :
    WorkSlab
      (advertisedBlockWidth
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        (actualCanonicalWorkBlockGroupLabel
          machine input T b hb before)) :=
  actualFixedAlphaBlockSlabAtTime machine input T b hb
    (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
    (timeGroupsLength before)

/-- The chronological first group's actual entry restriction is the single
blank slab expected by the fixed-alpha validator. -/
@[simp]
theorem actualCanonicalWorkBlockGroupEntrySlab_nil
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualCanonicalWorkBlockGroupEntrySlab
        machine input T b hb [] =
      blankWorkSlab
        (advertisedBlockWidth
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          (actualCanonicalWorkBlockGroupLabel machine input T b hb [])) := by
  rw [actualCanonicalWorkBlockGroupEntrySlab]
  change restrictWorkSlab _ _ WorkTape.blank = blankWorkSlab _
  exact restrictWorkSlab_blank _ _

/-- The materialized validator entry and the actual group entry expose the
same state, both heads, and actual-alpha slab restriction. -/
theorem actualCanonicalWorkBlockGroupVisit_entry_sameOnWorkSlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    SameOnWorkSlab
      (advertisedBlockLower
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
      (advertisedBlockWidth
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
      (fixedAlphaBlockVisitEntryConfiguration
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before after group hsplit)
        (actualCanonicalWorkBlockGroupEntrySlab
          machine input T b hb before))
      (run machine input (timeGroupsLength before)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp [fixedAlphaBlockVisitEntryConfiguration,
      actualCanonicalWorkBlockGroupEntrySlab,
      actualFixedAlphaBlockSlabAtTime]

/-- Every concrete pre-transition head of the actual group lies in the slab
advertised by the actual timed alpha. -/
theorem actualCanonicalWorkBlockGroupVisit_workHead_in_advertisedSlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (time : Nat)
    (htime : time <
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb before after group hsplit).steps) :
    WorkCellInSlab
      (advertisedBlockLower
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
      (advertisedBlockWidth
        (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
      (runFrom machine input
        (run machine input (timeGroupsLength before)) time).workHead := by
  have htimeGroup : time < group.length := by
    simpa using htime
  have hglobal := actualCanonicalWorkBlockGroup_workHead_in_slab
    machine input T b hb before after group hsplit time htimeGroup
  have hrun :
      run machine input (timeGroupsLength before + time) =
        runFrom machine input
          (run machine input (timeGroupsLength before)) time := by
    simpa [run] using
      (runFrom_add_eq_runFrom_runFrom machine input
        (initialConfiguration machine) (timeGroupsLength before) time)
  have hlocal := congrArg Configuration.workHead hrun ▸ hglobal
  simpa [chronologicalTimedCanonicalAlpha,
    actualCanonicalWorkBlockGroupLabel, actualWorkBoundaryCounts] using hlocal

/-- The actual group exit realizes the visit's advertised exit endpoint. -/
theorem actualCanonicalWorkBlockGroupVisit_exit_matches
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    ConfigurationMatchesFixedAlphaEndpoint
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb before after group hsplit).exit
      (runFrom machine input
        (run machine input (timeGroupsLength before))
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before after group hsplit).steps) := by
  have hrun :
      runFrom machine input
          (run machine input (timeGroupsLength before)) group.length =
        run machine input (timeGroupsLength before + group.length) := by
    symm
    simpa [run] using
      (runFrom_add_eq_runFrom_runFrom machine input
        (initialConfiguration machine) (timeGroupsLength before) group.length)
  rw [actualCanonicalWorkBlockGroupVisit_steps, hrun]
  exact ⟨rfl, rfl, rfl⟩

/-- One actual maximal group is accepted by the fixed-alpha local validator
when the single carried state is initialized to its actual entry restriction. -/
theorem actualCanonicalWorkBlockGroupVisit_valid
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    FixedAlphaBlockVisitValid machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb before after group hsplit)
      (actualCanonicalWorkBlockGroupEntrySlab
        machine input T b hb before) := by
  apply fixedAlphaBlockVisitValid_of_matching_concrete_replay
    machine input
    (chronologicalTimedCanonicalAlpha machine input T b hb)
    (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
    (actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit)
    (actualCanonicalWorkBlockGroupEntrySlab machine input T b hb before)
    (run machine input (timeGroupsLength before))
  · exact actualCanonicalWorkBlockGroupVisit_entry_sameOnWorkSlab
      machine input T b hb before after group hsplit
  · exact actualCanonicalWorkBlockGroupVisit_workHead_in_advertisedSlab
      machine input T b hb before after group hsplit
  · exact actualCanonicalWorkBlockGroupVisit_exit_matches
      machine input T b hb before after group hsplit

/-- In particular, the chronological first actual group is accepted from the
validator's literal blank carried state. -/
theorem actualCanonicalFirstWorkBlockGroupVisit_valid_from_blank
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      group :: after) :
    FixedAlphaBlockVisitValid machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      (actualCanonicalWorkBlockGroupLabel machine input T b hb [])
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb [] after group (by simpa using hsplit))
      (blankWorkSlab
        (advertisedBlockWidth
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          (actualCanonicalWorkBlockGroupLabel
            machine input T b hb []))) := by
  simpa using
    (actualCanonicalWorkBlockGroupVisit_valid
      machine input T b hb [] after group (by simpa using hsplit))

/-- The validator's unique output state is exactly the actual group-exit slab
restriction, still expressed in actual-alpha advertised geometry. -/
theorem actualCanonicalWorkBlockGroupVisit_outputSlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    fixedAlphaBlockVisitOutputSlab machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before after group hsplit)
        (actualCanonicalWorkBlockGroupEntrySlab
          machine input T b hb before) =
      restrictWorkSlab
        (advertisedBlockLower
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
        (advertisedBlockWidth
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          (actualCanonicalWorkBlockGroupLabel machine input T b hb before))
        (run machine input
          (timeGroupsLength before + group.length)).workTape := by
  have hvalid := actualCanonicalWorkBlockGroupVisit_valid
    machine input T b hb before after group hsplit
  have hentry :=
    actualCanonicalWorkBlockGroupVisit_entry_sameOnWorkSlab
      machine input T b hb before after group hsplit
  have hinterface := fixedAlphaBlockVisitValid_concrete_exit_interface
    machine input
    (chronologicalTimedCanonicalAlpha machine input T b hb)
    (actualCanonicalWorkBlockGroupLabel machine input T b hb before)
    (actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit)
    (actualCanonicalWorkBlockGroupEntrySlab machine input T b hb before)
    hvalid (run machine input (timeGroupsLength before)) hentry
  have hrun :
      runFrom machine input
          (run machine input (timeGroupsLength before)) group.length =
        run machine input (timeGroupsLength before + group.length) := by
    symm
    simpa [run] using
      (runFrom_add_eq_runFrom_runFrom machine input
        (initialConfiguration machine) (timeGroupsLength before) group.length)
  rw [actualCanonicalWorkBlockGroupVisit_steps, hrun] at hinterface
  exact hinterface.2.symm

/-- Target-typed form of one-group validity.  An explicit equality identifying
the group's actual label with `target` transports the dependent carried slab
without any choice or tape reset. -/
theorem actualCanonicalWorkBlockGroupVisit_valid_for_target
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (htarget : actualCanonicalWorkBlockGroupLabel
      machine input T b hb before = target) :
    FixedAlphaBlockVisitValid machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb) target
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb before after group hsplit)
      (actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before)) := by
  subst target
  simpa [actualCanonicalWorkBlockGroupEntrySlab,
    actualFixedAlphaBlockSlabAtTime] using
      (actualCanonicalWorkBlockGroupVisit_valid
        machine input T b hb before after group hsplit)

/-- Target-typed output theorem corresponding to the preceding validity
bridge. -/
theorem actualCanonicalWorkBlockGroupVisit_outputSlab_for_target
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (htarget : actualCanonicalWorkBlockGroupLabel
      machine input T b hb before = target) :
    fixedAlphaBlockVisitOutputSlab machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) target
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before after group hsplit)
        (actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before)) =
      actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before + group.length) := by
  subst target
  simpa [actualCanonicalWorkBlockGroupEntrySlab,
    actualFixedAlphaBlockSlabAtTime] using
      (actualCanonicalWorkBlockGroupVisit_outputSlab
        machine input T b hb before after group hsplit)

end OneTapeMagnification
end Frontier
end Pnp4
