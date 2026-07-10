import Pnp4.Frontier.OneTapeMagnification.OneTapeMachine
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-way input cache normalization

Canonical path/transcript decompositions are easiest to state when an input
symbol is used only at the moment it is first encountered.  The concrete
machine model also allows the input head to stay, apparently exposing the same
symbol on many consecutive transitions.  This module removes that technical
issue without assuming it away.

The normalized machine has one initialization state and then stores the
current logical input symbol in finite control.  Its physical input head is
one cell ahead of the simulated head.  While the simulated head stays, the
transition is independent of the unread physical symbol.  When the simulated
head moves right, that unread symbol is cached and the physical head advances.

After the one-step initialization, every normalized run is proved exactly
equal to the cached image of the original run.  The construction preserves
the work tape and work-head evolution step for step and adds only a constant
factor to the finite control.  This is a model-normalization lemma, not the
Viola branching-program simulation or the missing collective HSG.
-/

/-- One initialization state (`none`), followed by the original control state
paired with the cached logical input symbol. -/
abbrev CachedInputState (machine : DeterministicMachine) :=
  Option (machine.State × ReadOnlySymbol)

/-- Local transition of the cached-input simulation. -/
def cachedInputTransition (machine : DeterministicMachine)
    (state : CachedInputState machine)
    (unread : ReadOnlySymbol) (work : Bool) :
    Instruction (CachedInputState machine) :=
  match state with
  | none =>
      { nextState := some (machine.startState, unread)
        write := work
        inputMove := .right
        workMove := .stay }
  | some (originalState, cached) =>
      let instruction := machine.transition originalState cached work
      match instruction.inputMove with
      | .stay =>
          { nextState := some (instruction.nextState, cached)
            write := instruction.write
            inputMove := .stay
            workMove := instruction.workMove }
      | .right =>
          { nextState := some (instruction.nextState, unread)
            write := instruction.write
            inputMove := .right
            workMove := instruction.workMove }

/-- Deterministic machine implementing the one-cell-ahead input cache. -/
def cachedInputMachine (machine : DeterministicMachine) :
    DeterministicMachine where
  State := CachedInputState machine
  stateFintype := by
    letI : Fintype machine.State := machine.stateFintype
    exact inferInstanceAs (Fintype (Option (machine.State × ReadOnlySymbol)))
  startState := none
  halt
    | none => none
    | some (state, _) => machine.halt state
  transition := cachedInputTransition machine

/-- The normalization adds one initialization state and three cached-symbol
copies of every original control state. -/
theorem cachedInputMachine_state_card (machine : DeterministicMachine) :
    @Fintype.card (cachedInputMachine machine).State
        (cachedInputMachine machine).stateFintype =
      1 + 3 * @Fintype.card machine.State machine.stateFintype := by
  have hSymbols : Fintype.card ReadOnlySymbol = 3 := by decide
  simp [cachedInputMachine, CachedInputState, hSymbols,
    Nat.mul_comm, Nat.add_comm]

/-- Canonical cached configuration corresponding to one original
configuration.  The physical input head points to the next unread symbol. -/
def cachedConfiguration (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    Configuration (CachedInputState machine) where
  state := some (config.state, readOnlySymbol input config.inputHead)
  inputHead := config.inputHead + 1
  workHead := config.workHead
  workTape := config.workTape

/-- During a simulated stay move, the local transition is independent of the
next unread physical input symbol. -/
theorem cachedInputTransition_stay_independent
    (machine : DeterministicMachine)
    (state : machine.State) (cached work : Bool)
    (unread₁ unread₂ : ReadOnlySymbol)
    (hStay :
      (machine.transition state (.bit cached) work).inputMove = .stay) :
    cachedInputTransition machine (some (state, .bit cached)) unread₁ work =
      cachedInputTransition machine (some (state, .bit cached)) unread₂ work := by
  simp [cachedInputTransition, hStay]

/-- General form of unread-symbol independence, including the right-end
marker as a cached symbol. -/
theorem cachedInputTransition_stay_independent_general
    (machine : DeterministicMachine)
    (state : machine.State) (cached : ReadOnlySymbol) (work : Bool)
    (unread₁ unread₂ : ReadOnlySymbol)
    (hStay : (machine.transition state cached work).inputMove = .stay) :
    cachedInputTransition machine (some (state, cached)) unread₁ work =
      cachedInputTransition machine (some (state, cached)) unread₂ work := by
  simp [cachedInputTransition, hStay]

/-- One normalized simulation step is exactly the cached image of one
original step. -/
theorem cachedInputMachine_step_cachedConfiguration
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    step (cachedInputMachine machine) input
        (cachedConfiguration machine input config) =
      cachedConfiguration machine input (step machine input config) := by
  cases hHalt : machine.halt config.state with
  | some outcome =>
      simp [step, cachedInputMachine, cachedConfiguration, hHalt]
  | none =>
      generalize hInstruction :
        machine.transition config.state
          (readOnlySymbol input config.inputHead)
          (WorkTape.read config.workTape config.workHead) = instruction
      cases hMove : instruction.inputMove <;>
        simp [step, cachedInputMachine, cachedInputTransition,
          cachedConfiguration, hHalt, hInstruction, hMove,
          applyInstruction, moveInputHead]

/-- Exact simulation from any already-cached configuration for any number of
steps. -/
theorem cachedInputMachine_runFrom_cachedConfiguration
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    runFrom (cachedInputMachine machine) input
        (cachedConfiguration machine input config) steps =
      cachedConfiguration machine input
        (runFrom machine input config steps) := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      rw [runFrom_succ,
        cachedInputMachine_step_cachedConfiguration,
        runFrom_succ]
      exact ih (config := step machine input config)

/-- The initialization transition caches input cell zero, advances the
physical head once, and otherwise preserves the blank initial configuration. -/
theorem cachedInputMachine_step_initial
    (machine : DeterministicMachine) (input : List Bool) :
    step (cachedInputMachine machine) input
        (initialConfiguration (cachedInputMachine machine)) =
      cachedConfiguration machine input (initialConfiguration machine) := by
  have hBlankWrite :
      WorkTape.write WorkTape.blank 0 false = WorkTape.blank := by
    funext position
    simp [WorkTape.write, WorkTape.blank]
  simp [step, cachedInputMachine, cachedInputTransition,
    cachedConfiguration, initialConfiguration, applyInstruction,
    moveInputHead, moveWorkHead, hBlankWrite]

/-- Full run correspondence: the cached machine uses one initialization step,
then simulates exactly `steps` original transitions. -/
theorem cachedInputMachine_run_succ
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    run (cachedInputMachine machine) input (steps + 1) =
      cachedConfiguration machine input (run machine input steps) := by
  unfold run
  rw [runFrom_succ, cachedInputMachine_step_initial,
    cachedInputMachine_runFrom_cachedConfiguration]

/-- Cached configurations have exactly the original terminal outcome. -/
theorem cachedInputMachine_outcome_cachedConfiguration
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    outcome (cachedInputMachine machine)
        (cachedConfiguration machine input config) =
      outcome machine config := by
  rfl

/-- In particular, acceptance at the end of `steps` original transitions is
equivalent to acceptance after the normalized initialization plus those
`steps` transitions. -/
theorem cachedInputMachine_accepting_run_succ_iff
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input (steps + 1)) ↔
      IsAccepting machine (run machine input steps) := by
  rw [cachedInputMachine_run_succ]
  rfl

/-- Bounded-time language equivalence with the exact one-step overhead.  This
also covers a machine whose start state is already halting. -/
theorem cachedInputMachine_acceptsWithin_succ_iff
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    AcceptsWithin (cachedInputMachine machine) input (steps + 1) ↔
      AcceptsWithin machine input steps := by
  constructor
  · rintro ⟨first, hFirst, hAccepts⟩
    cases first with
    | zero =>
        simp [run_zero, IsAccepting, outcome, cachedInputMachine,
          initialConfiguration] at hAccepts
    | succ first =>
        have hBound : first ≤ steps := Nat.le_of_succ_le_succ hFirst
        refine ⟨first, hBound, ?_⟩
        have hAccepts' :
            IsAccepting (cachedInputMachine machine)
              (run (cachedInputMachine machine) input (first + 1)) := by
          simpa [Nat.succ_eq_add_one] using hAccepts
        exact (cachedInputMachine_accepting_run_succ_iff
          machine input first).mp hAccepts'
  · rintro ⟨first, hFirst, hAccepts⟩
    refine ⟨first + 1, Nat.add_le_add_right hFirst 1, ?_⟩
    exact (cachedInputMachine_accepting_run_succ_iff
      machine input first).2 hAccepts

end OneTapeMagnification
end Frontier
end Pnp4
