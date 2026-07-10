import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.InputCacheNormalization
import Pnp4.Frontier.OneTapeMagnification.LowRunInputOrder
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Input orders extracted from actual one-tape runs

`LowRunInputOrder` proves the combinatorics of a generic chronological event
list.  This file supplies that list from the concrete deterministic semantics:
there is one event for each transition time `0, ..., steps - 1`, its input
position is the pre-transition input-head position, and `advances` is true
exactly when the next position is its successor.  Work-block membership is a
supplied finite classifier; no separator construction or branching-program
simulation is hidden in that argument.

The one-way machine semantics makes all raw positions nondecreasing.  After
stay events are omitted, the pre-transition positions of advancing moves are
strictly increasing.  Thus stable work-block grouping has at most
`blockCount` increasing runs, and in particular at most `K + 1` runs for
`K + 1` blocks.

For `cachedInputMachine`, omitting a stay from the external query list is
semantically justified by `cachedInputTransition_stay_independent_general`:
the local instruction uses the cached logical symbol and is independent of
the next unread physical symbol.  The exact trajectory theorem at the end
records this fact.  Nothing here proves input-independent block membership,
bounded branching-program width, or an oblivious ROBP simulation.
-/

/-- Whether the transition at `time` advances the one-way input head. -/
def inputHeadAdvancesAt (machine : DeterministicMachine) (input : List Bool)
    (time : Nat) : Bool :=
  (run machine input (time + 1)).inputHead ==
    (run machine input time).inputHead + 1

/-- The concrete input-read event at one transition time. -/
def actualRunInputEvent {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool)
    (workBlockAt : Nat → Fin blockCount) (time : Nat) :
    InputReadEvent blockCount where
  chronologicalPosition := time
  workBlock := workBlockAt time
  inputPosition := (run machine input time).inputHead
  advances := inputHeadAdvancesAt machine input time

/-- Chronological events for precisely the transitions `0, ..., steps - 1`. -/
def actualRunInputEvents {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat)
    (workBlockAt : Nat → Fin blockCount) : List (InputReadEvent blockCount) :=
  List.ofFn fun time : Fin steps =>
    actualRunInputEvent machine input workBlockAt time.val

@[simp]
theorem actualRunInputEvents_length {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat)
    (workBlockAt : Nat → Fin blockCount) :
    (actualRunInputEvents machine input steps workBlockAt).length = steps := by
  simp [actualRunInputEvents]

/-- Iteration splits at an arbitrary intermediate time. -/
theorem runFrom_add_eq_runFrom_runFrom
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (first later : Nat) :
    runFrom machine input config (first + later) =
      runFrom machine input (runFrom machine input config first) later := by
  induction first generalizing config with
  | zero => simp only [Nat.zero_add, runFrom_zero]
  | succ first ih =>
      simpa only [Nat.succ_add, Nat.succ_eq_add_one, runFrom_succ] using
        (ih (config := step machine input config))

/-- Input-head position is monotone as a function of blank-start run time. -/
theorem inputHead_run_mono
    (machine : DeterministicMachine) (input : List Bool)
    {earlier later : Nat} (hTime : earlier ≤ later) :
    (run machine input earlier).inputHead ≤
      (run machine input later).inputHead := by
  obtain ⟨delta, rfl⟩ := Nat.exists_eq_add_of_le hTime
  rw [run, run, runFrom_add_eq_runFrom_runFrom]
  exact inputHead_le_runFrom machine input
    (runFrom machine input (initialConfiguration machine) earlier) delta

/-- The extracted chronological labels are strictly ordered. -/
theorem actualRunInputEvents_chronological_pairwise
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    ((actualRunInputEvents machine input steps workBlockAt).map
      InputReadEvent.chronologicalPosition).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa [actualRunInputEvents, actualRunInputEvent] using hij

/-- Raw positions extracted from the run are nondecreasing. -/
theorem actualRunInputEvents_raw_positions_pairwise_le
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    (rawInputPositions
      (actualRunInputEvents machine input steps workBlockAt)).Pairwise
        (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [rawInputPositions, List.length_map,
    actualRunInputEvents_length] at hi hj
  simp [rawInputPositions, actualRunInputEvents, actualRunInputEvent]
  exact inputHead_run_mono machine input (Nat.le_of_lt hij)

/-- The event flag is true exactly for a successor move. -/
theorem actualRunInputEvent_advances_iff {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool)
    (workBlockAt : Nat → Fin blockCount) (time : Nat) :
    (actualRunInputEvent machine input workBlockAt time).advances = true ↔
      (run machine input (time + 1)).inputHead =
        (run machine input time).inputHead + 1 := by
  simp [actualRunInputEvent, inputHeadAdvancesAt]

/-- A false event flag is exactly a stay, using the concrete machine's
exhaustive stay/right step dichotomy. -/
theorem actualRunInputEvent_not_advances_iff_stays {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool)
    (workBlockAt : Nat → Fin blockCount) (time : Nat) :
    (actualRunInputEvent machine input workBlockAt time).advances = false ↔
      (run machine input (time + 1)).inputHead =
        (run machine input time).inputHead := by
  rw [actualRunInputEvent, inputHeadAdvancesAt]
  simp only [run, runFrom_succ_eq_step_runFrom]
  have hCases := inputHead_step_cases machine input
    (run machine input time)
  simp only [run] at hCases
  rcases hCases with hStay | hRight
  · simp [hStay]
  · simp [hRight]

/-- Omitting nonadvancing events is exactly omitting input-head stays. -/
theorem actualRunInputEvent_no_fresh_query_iff_stays {blockCount : Nat}
    (machine : DeterministicMachine) (input : List Bool)
    (workBlockAt : Nat → Fin blockCount) (time : Nat) :
    freshInputQuery?
        (actualRunInputEvent machine input workBlockAt time) = none ↔
      (run machine input (time + 1)).inputHead =
        (run machine input time).inputHead := by
  rw [← actualRunInputEvent_not_advances_iff_stays
    machine input workBlockAt time]
  cases hAdvance :
      (actualRunInputEvent machine input workBlockAt time).advances <;>
    simp [freshInputQuery?, hAdvance]

/-- The advancing pre-transition positions in an actual one-way run are
strictly increasing. -/
theorem actualRunInputEvents_fresh_positions_pairwise_lt
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    (freshInputPositions
      (actualRunInputEvents machine input steps workBlockAt)).Pairwise
        (· < ·) := by
  rw [freshInputPositions_eq_filterMap, List.pairwise_filterMap]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij positionI hI positionJ hJ
  simp only [actualRunInputEvents_length] at hi hj
  have hI' :
      inputHeadAdvancesAt machine input i = true ∧
        (run machine input i).inputHead = positionI := by
    simpa [freshInputQuery?, actualRunInputEvents, actualRunInputEvent]
      using hI
  have hJ' :
      inputHeadAdvancesAt machine input j = true ∧
        (run machine input j).inputHead = positionJ := by
    simpa [freshInputQuery?, actualRunInputEvents, actualRunInputEvent]
      using hJ
  rcases hI' with ⟨hAdvanceI, hPositionI⟩
  rcases hJ' with ⟨-, hPositionJ⟩
  have hAdvanceI' :
      (run machine input (i + 1)).inputHead =
        (run machine input i).inputHead + 1 := by
    simpa [inputHeadAdvancesAt] using hAdvanceI
  rw [← hPositionI, ← hPositionJ]
  calc
    (run machine input i).inputHead <
        (run machine input (i + 1)).inputHead := by omega
    _ ≤ (run machine input j).inputHead :=
      inputHead_run_mono machine input (Nat.succ_le_of_lt hij)

/-- Stable grouping of an actual run has at most `blockCount` nondecreasing
raw-position runs. -/
theorem actualRun_stableGroupedRaw_has_at_most_blockCount_runs
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    HasAtMostInputRuns (· ≤ ·) blockCount
      (stableGroupedRawInputPositions
        (actualRunInputEvents machine input steps workBlockAt)) :=
  stableGroupedRawInputPositions_has_at_most_blockCount_runs _
    (actualRunInputEvents_raw_positions_pairwise_le
      machine input steps workBlockAt)

/-- Stable grouping of actual fresh queries has at most `blockCount` strict
increasing runs. -/
theorem actualRun_stableGroupedFresh_has_at_most_blockCount_strict_runs
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    HasAtMostInputRuns (· < ·) blockCount
      (stableGroupedFreshInputPositions
        (actualRunInputEvents machine input steps workBlockAt)) :=
  stableGroupedFreshInputPositions_has_at_most_blockCount_strict_runs _
    (actualRunInputEvents_fresh_positions_pairwise_lt
      machine input steps workBlockAt)

/-- The separator notation: `K` separators give `K + 1` possible blocks and
therefore at most `K + 1` increasing fresh-query runs. -/
theorem actualRun_stableGroupedFresh_has_at_most_K_add_one_strict_runs
    {K : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin (K + 1)) :
    HasAtMostInputRuns (· < ·) (K + 1)
      (stableGroupedFreshInputPositions
        (actualRunInputEvents machine input steps workBlockAt)) :=
  stableGroupedFreshInputPositions_has_at_most_K_add_one_strict_runs _
    (actualRunInputEvents_fresh_positions_pairwise_lt
      machine input steps workBlockAt)

/-- Exact cached-input semantics for a simulated nonhalting stay: the local
normalized instruction is independent of the next unread physical symbol.
This is the semantic reason such an event contributes no fresh external query.
The work symbol is the one present in the actual original run at `time`. -/
theorem cachedRun_stay_instruction_independent_of_unread
    (machine : DeterministicMachine) (input : List Bool) (time : Nat)
    (hRunning : machine.halt (run machine input time).state = none)
    (hStay : (run machine input (time + 1)).inputHead =
      (run machine input time).inputHead)
    (unread₁ unread₂ : ReadOnlySymbol) :
    cachedInputTransition machine
        (some ((run machine input time).state,
          readOnlySymbol input (run machine input time).inputHead)) unread₁
        (WorkTape.read (run machine input time).workTape
          (run machine input time).workHead) =
      cachedInputTransition machine
        (some ((run machine input time).state,
          readOnlySymbol input (run machine input time).inputHead)) unread₂
        (WorkTape.read (run machine input time).workTape
          (run machine input time).workHead) := by
  let config := run machine input time
  have hStep : (step machine input config).inputHead = config.inputHead := by
    simpa only [config, run, runFrom_succ_eq_step_runFrom] using hStay
  have hRunning' : machine.halt config.state = none := by
    simpa [config] using hRunning
  have hMove :
      (machine.transition config.state
        (readOnlySymbol input config.inputHead)
        (WorkTape.read config.workTape config.workHead)).inputMove = .stay := by
    let instruction := machine.transition config.state
      (readOnlySymbol input config.inputHead)
      (WorkTape.read config.workTape config.workHead)
    cases hInputMove : instruction.inputMove
    · rfl
    · have hRight :
          (step machine input config).inputHead = config.inputHead + 1 := by
        simp [step, hRunning', instruction, applyInstruction,
          moveInputHead, hInputMove]
      omega
  exact cachedInputTransition_stay_independent_general machine
    config.state (readOnlySymbol input config.inputHead)
    (WorkTape.read config.workTape config.workHead) unread₁ unread₂ hMove

/-- Event-level cached-input consequence: whenever the extracted event says
that the simulated head did not advance, the normalized local instruction is
independent of the unread physical symbol.  Hence the event can be represented
by `none` in the fresh external-query order without assuming away a read. -/
theorem cachedRun_nonadvancing_event_instruction_independent_of_unread
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (workBlockAt : Nat → Fin blockCount) (time : Nat)
    (hRunning : machine.halt (run machine input time).state = none)
    (hNoAdvance :
      (actualRunInputEvent machine input workBlockAt time).advances = false)
    (unread₁ unread₂ : ReadOnlySymbol) :
    cachedInputTransition machine
        (some ((run machine input time).state,
          readOnlySymbol input (run machine input time).inputHead)) unread₁
        (WorkTape.read (run machine input time).workTape
          (run machine input time).workHead) =
      cachedInputTransition machine
        (some ((run machine input time).state,
          readOnlySymbol input (run machine input time).inputHead)) unread₂
        (WorkTape.read (run machine input time).workTape
          (run machine input time).workHead) :=
  cachedRun_stay_instruction_independent_of_unread machine input time hRunning
    ((actualRunInputEvent_not_advances_iff_stays
      machine input workBlockAt time).mp hNoAdvance) unread₁ unread₂

end OneTapeMagnification
end Frontier
end Pnp4
