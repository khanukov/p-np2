import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A concrete deterministic one-tape convention

Cheraghchi--Hirahara--Myrisiotis--Yoshida use a one-way read-only input tape and one
read/write work tape, but do not fix low-level choices such as endmarkers,
stay moves, or the left boundary convention.  This file therefore chooses the
following explicit operational convention:

* input and work symbols are Boolean;
* reading at or to the right of the end of the finite input returns one
  distinguished right-end symbol;
* the input head starts at zero and may only stay or move right;
* the work tape is indexed by `Nat`, is initially all blank (`false`), and its
  head may move left, stay, or move right; a left move at zero stays at zero;
* a transition into a halting state consumes one step, and a halted
  configuration subsequently stutters.

These choices make the measured step count unambiguous.  They are a local
formalization convention, not a claim that the paper specifies endmarkers in
this way.  In particular, this is neither the MMW random-access streaming RAM
nor the repository's loaded-input single-tape machine: the input below is a
separate immutable tape and a transition can inspect only its current symbol.
-/

/-- The finite alphabet seen by the head of a read-only finite tape. -/
inductive ReadOnlySymbol where
  | bit (value : Bool)
  | rightEnd
deriving DecidableEq, Fintype, Repr

/-- A one-way read-only head can stay put or advance by one cell. -/
inductive InputMove where
  | stay
  | right
deriving DecidableEq, Fintype, Repr

/-- The work head can move in either direction, or stay put. -/
inductive WorkMove where
  | left
  | stay
  | right
deriving DecidableEq, Fintype, Repr

/-- The two possible terminal outcomes of a machine. -/
inductive HaltOutcome where
  | accept
  | reject
deriving DecidableEq, Fintype, Repr

/-- Read a finite read-only Boolean tape using the chosen right-end symbol. -/
def readOnlySymbol (tape : List Bool) (head : Nat) : ReadOnlySymbol :=
  match tape[head]? with
  | some value => .bit value
  | none => .rightEnd

/-- Apply one legal move of the one-way input head. -/
def moveInputHead (head : Nat) : InputMove → Nat
  | .stay => head
  | .right => head + 1

/--
Apply one work-head move.  The `Nat`-indexed work tape has a reflecting left
boundary, so moving left from cell zero leaves the head at zero.
-/
def moveWorkHead (head : Nat) : WorkMove → Nat
  | .left => head - 1
  | .stay => head
  | .right => head + 1

/-- A Boolean, `Nat`-indexed read/write work tape. -/
abbrev WorkTape := Nat → Bool

namespace WorkTape

/-- The initially blank work tape. -/
def blank : WorkTape := fun _ => false

/-- Read one work-tape cell. -/
def read (tape : WorkTape) (head : Nat) : Bool := tape head

/-- Write one work-tape cell, leaving every other cell unchanged. -/
def write (tape : WorkTape) (head : Nat) (value : Bool) : WorkTape :=
  fun i => if i = head then value else tape i

@[simp]
theorem read_blank (head : Nat) : read blank head = false := rfl

@[simp]
theorem read_write_same (tape : WorkTape) (head : Nat) (value : Bool) :
    read (write tape head value) head = value := by
  simp [read, write]

theorem read_write_of_ne
    (tape : WorkTape) (head other : Nat) (value : Bool)
    (h : other ≠ head) :
    read (write tape head value) other = read tape other := by
  simp [read, write, h]

end WorkTape

/-- One local deterministic transition instruction. -/
structure Instruction (State : Type) where
  nextState : State
  write : Bool
  inputMove : InputMove
  workMove : WorkMove

/-!
`stateFintype` is data, rather than an ambient assumption: every machine
explicitly carries a finite enumeration of its control states.  Since all
three symbol/move types are finite, `transition` is a finite local program.
It has no argument containing the whole input tape.
-/

/-- A deterministic CHMY-style one-tape machine under the convention above. -/
structure DeterministicMachine where
  State : Type
  stateFintype : Fintype State
  startState : State
  halt : State → Option HaltOutcome
  transition : State → ReadOnlySymbol → Bool → Instruction State

/-- A short name for the deterministic model in this file. -/
abbrev OneTapeMachine := DeterministicMachine

/-- A small-step configuration; the immutable input tape is intentionally absent. -/
structure Configuration (State : Type) where
  state : State
  inputHead : Nat
  workHead : Nat
  workTape : WorkTape

/-- The blank initial configuration of a deterministic machine. -/
def initialConfiguration (machine : DeterministicMachine) :
    Configuration machine.State where
  state := machine.startState
  inputHead := 0
  workHead := 0
  workTape := WorkTape.blank

/-- Apply a local instruction to a configuration. -/
def applyInstruction {State : Type}
    (config : Configuration State) (instruction : Instruction State) :
    Configuration State where
  state := instruction.nextState
  inputHead := moveInputHead config.inputHead instruction.inputMove
  workHead := moveWorkHead config.workHead instruction.workMove
  workTape := WorkTape.write config.workTape config.workHead instruction.write

/--
One deterministic small step.  Halting configurations stutter; otherwise the
machine reads exactly the current input and work symbols and applies one local
instruction.
-/
def step (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) : Configuration machine.State :=
  match machine.halt config.state with
  | some _ => config
  | none =>
      applyInstruction config
        (machine.transition config.state
          (readOnlySymbol input config.inputHead)
          (WorkTape.read config.workTape config.workHead))

/-- Run exactly `steps` small steps from an arbitrary configuration. -/
def runFrom (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) : Nat → Configuration machine.State
  | 0 => config
  | steps + 1 => runFrom machine input (step machine input config) steps

/-- Run exactly `steps` small steps from the blank initial configuration. -/
def run (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    Configuration machine.State :=
  runFrom machine input (initialConfiguration machine) steps

@[simp]
theorem runFrom_zero (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    runFrom machine input config 0 = config := rfl

@[simp]
theorem runFrom_succ (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    runFrom machine input config (steps + 1) =
      runFrom machine input (step machine input config) steps := rfl

@[simp]
theorem run_zero (machine : DeterministicMachine) (input : List Bool) :
    run machine input 0 = initialConfiguration machine := rfl

@[simp]
theorem step_of_halted
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (outcome : HaltOutcome)
    (h : machine.halt config.state = some outcome) :
    step machine input config = config := by
  simp [step, h]

/-- A one-way input step either preserves the head or increments it once. -/
theorem inputHead_step_cases
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).inputHead = config.inputHead ∨
      (step machine input config).inputHead = config.inputHead + 1 := by
  unfold step
  split
  · exact Or.inl rfl
  · dsimp only [applyInstruction]
    cases (machine.transition config.state
      (readOnlySymbol input config.inputHead)
      (WorkTape.read config.workTape config.workHead)).inputMove <;>
      simp [moveInputHead]

/-- In particular, a small step can never move the input head left. -/
theorem inputHead_le_step
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    config.inputHead ≤ (step machine input config).inputHead := by
  rcases inputHead_step_cases machine input config with h | h
  · simp [h]
  · simp [h]

/-- The input head is monotone throughout any exact finite run. -/
theorem inputHead_le_runFrom
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    config.inputHead ≤ (runFrom machine input config steps).inputHead := by
  induction steps generalizing config with
  | zero => simp
  | succ steps ih =>
      exact le_trans (inputHead_le_step machine input config)
        (ih (config := step machine input config))

/-- The terminal outcome, if any, of a configuration. -/
def outcome (machine : DeterministicMachine)
    (config : Configuration machine.State) : Option HaltOutcome :=
  machine.halt config.state

/-- A configuration is in either terminal state. -/
def IsHalted (machine : DeterministicMachine)
    (config : Configuration machine.State) : Prop :=
  (outcome machine config).isSome

/-- A configuration is accepting. -/
def IsAccepting (machine : DeterministicMachine)
    (config : Configuration machine.State) : Prop :=
  outcome machine config = some .accept

/-- A configuration is rejecting. -/
def IsRejecting (machine : DeterministicMachine)
    (config : Configuration machine.State) : Prop :=
  outcome machine config = some .reject

/-- The run has reached some halting configuration no later than `steps`. -/
def HaltsWithin (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) : Prop :=
  ∃ first : Nat, first ≤ steps ∧ IsHalted machine (run machine input first)

/-- The run has reached an accepting configuration no later than `steps`. -/
def AcceptsWithin (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) : Prop :=
  ∃ first : Nat, first ≤ steps ∧ IsAccepting machine (run machine input first)

/-- `steps` is the first step at which the run is halted. -/
def HaltsExactlyAt (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) : Prop :=
  IsHalted machine (run machine input steps) ∧
    ∀ earlier : Nat, earlier < steps →
      ¬ IsHalted machine (run machine input earlier)

/-- `steps` is the first halting step, and its outcome is acceptance. -/
def AcceptsExactlyAt (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) : Prop :=
  IsAccepting machine (run machine input steps) ∧
    ∀ earlier : Nat, earlier < steps →
      ¬ IsHalted machine (run machine input earlier)

/-- `steps` is the first halting step, and its outcome is rejection. -/
def RejectsExactlyAt (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) : Prop :=
  IsRejecting machine (run machine input steps) ∧
    ∀ earlier : Nat, earlier < steps →
      ¬ IsHalted machine (run machine input earlier)

end OneTapeMagnification
end Frontier
end Pnp4
