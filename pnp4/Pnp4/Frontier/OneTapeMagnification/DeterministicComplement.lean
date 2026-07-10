import Pnp4.Frontier.OneTapeMagnification.OneTapeMachine

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Complementing a deterministic one-tape machine

The deterministic lower-bound endpoint is naturally phrased for coMCSP,
whose hard truth tables form a dense accepting set.  This file closes the
usually implicit complement-closure step in the concrete machine model.

Swapping the two halting outcomes leaves every configuration and transition
unchanged.  Runs are therefore definitionally simulated with the same time,
input-head, work-head, and work-tape behavior.  Acceptance of the complemented
machine is exactly rejection of the original machine, and conversely.
-/

/-- Swap deterministic terminal outcomes. -/
def flipHaltOutcome : HaltOutcome → HaltOutcome
  | .accept => .reject
  | .reject => .accept

@[simp]
theorem flipHaltOutcome_involutive (outcome : HaltOutcome) :
    flipHaltOutcome (flipHaltOutcome outcome) = outcome := by
  cases outcome <;> rfl

/-- Complement a deterministic machine without changing its transition
function or state space. -/
def complementMachine (machine : DeterministicMachine) :
    DeterministicMachine where
  State := machine.State
  stateFintype := machine.stateFintype
  startState := machine.startState
  halt state := (machine.halt state).map flipHaltOutcome
  transition := machine.transition

/-- Complementation changes no small step. -/
theorem complementMachine_step
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    step (complementMachine machine) input config =
      step machine input config := by
  cases hHalt : machine.halt config.state <;>
    simp [step, complementMachine, hHalt]

/-- Complementation changes no finite run from an arbitrary configuration. -/
theorem complementMachine_runFrom
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    runFrom (complementMachine machine) input config steps =
      runFrom machine input config steps := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      rw [runFrom_succ, complementMachine_step, runFrom_succ]
      exact ih (config := step machine input config)

/-- Complementation changes no run from the blank initial configuration. -/
theorem complementMachine_run
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    run (complementMachine machine) input steps =
      run machine input steps := by
  exact complementMachine_runFrom machine input
    (initialConfiguration machine) steps

/-- Acceptance after complementing is exactly original rejection. -/
theorem complementMachine_isAccepting_iff_isRejecting
    (machine : DeterministicMachine)
    (config : Configuration machine.State) :
    IsAccepting (complementMachine machine) config ↔
      IsRejecting machine config := by
  cases hHalt : machine.halt config.state with
  | none => simp [IsAccepting, IsRejecting, outcome, complementMachine, hHalt]
  | some haltOutcome =>
      cases haltOutcome <;>
        simp [IsAccepting, IsRejecting, outcome, complementMachine,
          flipHaltOutcome, hHalt]

/-- Rejection after complementing is exactly original acceptance. -/
theorem complementMachine_isRejecting_iff_isAccepting
    (machine : DeterministicMachine)
    (config : Configuration machine.State) :
    IsRejecting (complementMachine machine) config ↔
      IsAccepting machine config := by
  cases hHalt : machine.halt config.state with
  | none => simp [IsAccepting, IsRejecting, outcome, complementMachine, hHalt]
  | some haltOutcome =>
      cases haltOutcome <;>
        simp [IsAccepting, IsRejecting, outcome, complementMachine,
          flipHaltOutcome, hHalt]

/-- Bounded-time acceptance of the complement is bounded-time rejection of
the original machine. -/
theorem complementMachine_acceptsWithin_iff_rejectsWithin
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    AcceptsWithin (complementMachine machine) input steps ↔
      RejectsWithin machine input steps := by
  constructor
  · rintro ⟨first, hFirst, hAccepts⟩
    refine ⟨first, hFirst, ?_⟩
    rw [complementMachine_run] at hAccepts
    exact (complementMachine_isAccepting_iff_isRejecting
      machine (run machine input first)).mp hAccepts
  · rintro ⟨first, hFirst, hRejects⟩
    refine ⟨first, hFirst, ?_⟩
    rw [complementMachine_run]
    exact (complementMachine_isAccepting_iff_isRejecting
      machine (run machine input first)).2 hRejects

/-- Bounded-time rejection of the complement is bounded-time acceptance of
the original machine. -/
theorem complementMachine_rejectsWithin_iff_acceptsWithin
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    RejectsWithin (complementMachine machine) input steps ↔
      AcceptsWithin machine input steps := by
  constructor
  · rintro ⟨first, hFirst, hRejects⟩
    refine ⟨first, hFirst, ?_⟩
    rw [complementMachine_run] at hRejects
    exact (complementMachine_isRejecting_iff_isAccepting
      machine (run machine input first)).mp hRejects
  · rintro ⟨first, hFirst, hAccepts⟩
    refine ⟨first, hFirst, ?_⟩
    rw [complementMachine_run]
    exact (complementMachine_isRejecting_iff_isAccepting
      machine (run machine input first)).2 hAccepts

end OneTapeMagnification
end Frontier
end Pnp4
