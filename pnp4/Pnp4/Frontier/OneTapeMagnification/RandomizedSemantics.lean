import Pnp4.Frontier.OneTapeMagnification.OneTapeMachine
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A separate finite random tape

This file extends the deterministic convention in `OneTapeMachine` with an
independent, one-way, read-only random tape.  A randomized transition remains
local: it sees one input symbol, one random symbol, and one work symbol.  It
does not receive either complete tape as an argument.

The random tape contains exactly `randomBits` Boolean cells.  Its head starts
at zero, may stay or move right, and reads `ReadOnlySymbol.rightEnd` after the
last cell.  Acceptance probability is the exact rational uniform average over
all `2 ^ randomBits` finite tapes; no external probability primitive is used.
-/

/-- A finite Boolean tape of the indicated length. -/
abbrev FiniteBitTape (length : Nat) := Fin length → Bool

/-- Read a finite random tape using the same explicit right-end convention. -/
def readFiniteBitTape {length : Nat}
    (tape : FiniteBitTape length) (head : Nat) : ReadOnlySymbol :=
  if h : head < length then .bit (tape ⟨head, h⟩) else .rightEnd

/-- One local transition instruction for the randomized machine. -/
structure RandomInstruction (State : Type) where
  nextState : State
  write : Bool
  inputMove : InputMove
  randomMove : InputMove
  workMove : WorkMove

/--
A randomized CHMY-style one-tape machine.  Its finite control enumeration is
explicit data, and its transition table has only finite local arguments.
-/
structure RandomizedMachine where
  State : Type
  stateFintype : Fintype State
  startState : State
  halt : State → Option HaltOutcome
  transition :
    State → ReadOnlySymbol → ReadOnlySymbol → Bool → RandomInstruction State

/-- A configuration with separate input, random, and work heads. -/
structure RandomConfiguration (State : Type) where
  state : State
  inputHead : Nat
  randomHead : Nat
  workHead : Nat
  workTape : WorkTape

/-- The blank initial configuration of a randomized machine. -/
def initialRandomConfiguration (machine : RandomizedMachine) :
    RandomConfiguration machine.State where
  state := machine.startState
  inputHead := 0
  randomHead := 0
  workHead := 0
  workTape := WorkTape.blank

/-- Apply one randomized local instruction. -/
def applyRandomInstruction {State : Type}
    (config : RandomConfiguration State)
    (instruction : RandomInstruction State) : RandomConfiguration State where
  state := instruction.nextState
  inputHead := moveInputHead config.inputHead instruction.inputMove
  randomHead := moveInputHead config.randomHead instruction.randomMove
  workHead := moveWorkHead config.workHead instruction.workMove
  workTape := WorkTape.write config.workTape config.workHead instruction.write

/-- One randomized small step with both read-only tapes supplied separately. -/
def randomizedStep (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    RandomConfiguration machine.State :=
  match machine.halt config.state with
  | some _ => config
  | none =>
      applyRandomInstruction config
        (machine.transition config.state
          (readOnlySymbol input config.inputHead)
          (readFiniteBitTape randomTape config.randomHead)
          (WorkTape.read config.workTape config.workHead))

/-- Run exactly `steps` randomized small steps from an arbitrary configuration. -/
def randomizedRunFrom (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    Nat → RandomConfiguration machine.State
  | 0 => config
  | steps + 1 =>
      randomizedRunFrom machine input randomTape
        (randomizedStep machine input randomTape config) steps

/-- Run exactly `steps` randomized small steps from the blank configuration. -/
def randomizedRun (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits) (steps : Nat) :
    RandomConfiguration machine.State :=
  randomizedRunFrom machine input randomTape
    (initialRandomConfiguration machine) steps

@[simp]
theorem randomizedRunFrom_zero
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    randomizedRunFrom machine input randomTape config 0 = config := rfl

@[simp]
theorem randomizedRunFrom_succ
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) (steps : Nat) :
    randomizedRunFrom machine input randomTape config (steps + 1) =
      randomizedRunFrom machine input randomTape
        (randomizedStep machine input randomTape config) steps := rfl

@[simp]
theorem randomizedStep_of_halted
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) (result : HaltOutcome)
    (h : machine.halt config.state = some result) :
    randomizedStep machine input randomTape config = config := by
  simp [randomizedStep, h]

/-- A randomized input step preserves or increments the input head. -/
theorem randomizedInputHead_step_cases
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    (randomizedStep machine input randomTape config).inputHead = config.inputHead ∨
      (randomizedStep machine input randomTape config).inputHead =
        config.inputHead + 1 := by
  unfold randomizedStep
  split
  · exact Or.inl rfl
  · dsimp only [applyRandomInstruction]
    cases (machine.transition config.state
      (readOnlySymbol input config.inputHead)
      (readFiniteBitTape randomTape config.randomHead)
      (WorkTape.read config.workTape config.workHead)).inputMove <;>
      simp [moveInputHead]

/-- A randomized input step cannot move the input head left. -/
theorem randomizedInputHead_le_step
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    config.inputHead ≤
      (randomizedStep machine input randomTape config).inputHead := by
  rcases randomizedInputHead_step_cases machine input randomTape config with h | h
  · simp [h]
  · simp [h]

/-- A randomized random-tape step preserves or increments the random head. -/
theorem randomHead_step_cases
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    (randomizedStep machine input randomTape config).randomHead = config.randomHead ∨
      (randomizedStep machine input randomTape config).randomHead =
        config.randomHead + 1 := by
  unfold randomizedStep
  split
  · exact Or.inl rfl
  · dsimp only [applyRandomInstruction]
    cases (machine.transition config.state
      (readOnlySymbol input config.inputHead)
      (readFiniteBitTape randomTape config.randomHead)
      (WorkTape.read config.workTape config.workHead)).randomMove <;>
      simp [moveInputHead]

/-- A randomized small step cannot move the random-tape head left. -/
theorem randomHead_le_step
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) :
    config.randomHead ≤
      (randomizedStep machine input randomTape config).randomHead := by
  rcases randomHead_step_cases machine input randomTape config with h | h
  · simp [h]
  · simp [h]

/-- Both read-only heads remain monotone during an exact finite run. -/
theorem readOnlyHeads_le_randomizedRunFrom
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (config : RandomConfiguration machine.State) (steps : Nat) :
    config.inputHead ≤
        (randomizedRunFrom machine input randomTape config steps).inputHead ∧
      config.randomHead ≤
        (randomizedRunFrom machine input randomTape config steps).randomHead := by
  induction steps generalizing config with
  | zero => simp
  | succ steps ih =>
      constructor
      · exact le_trans
          (randomizedInputHead_le_step machine input randomTape config)
          (ih (config := randomizedStep machine input randomTape config)).1
      · exact le_trans
          (randomHead_le_step machine input randomTape config)
          (ih (config := randomizedStep machine input randomTape config)).2

/-- The terminal result after exactly the requested number of small steps. -/
def randomizedOutcomeAfter (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits) (steps : Nat) :
    Option HaltOutcome :=
  machine.halt (randomizedRun machine input randomTape steps).state

/-- Executable acceptance after exactly `steps`; earlier halts stutter. -/
def randomizedAcceptsAfter (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (steps : Nat) : Bool :=
  match randomizedOutcomeAfter machine input randomTape steps with
  | some .accept => true
  | _ => false

/-- The run on this finite random tape halts for the first time at `steps`. -/
def RandomizedHaltsExactlyAt
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (steps : Nat) : Prop :=
  (randomizedOutcomeAfter machine input randomTape steps).isSome ∧
    ∀ earlier : Nat, earlier < steps →
      ¬ (randomizedOutcomeAfter machine input randomTape earlier).isSome

/-- The first halt on this finite random tape is acceptance at `steps`. -/
def RandomizedAcceptsExactlyAt
    (machine : RandomizedMachine) (input : List Bool)
    {randomBits : Nat} (randomTape : FiniteBitTape randomBits)
    (steps : Nat) : Prop :=
  randomizedOutcomeAfter machine input randomTape steps = some .accept ∧
    ∀ earlier : Nat, earlier < steps →
      ¬ (randomizedOutcomeAfter machine input randomTape earlier).isSome

/-- The finite set of random tapes accepted after the given number of steps. -/
def acceptingRandomTapes
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) : Finset (FiniteBitTape randomBits) :=
  Finset.univ.filter fun randomTape =>
    randomizedAcceptsAfter machine input randomTape steps = true

/-- The exact number of uniformly sampled finite random tapes that accept. -/
def acceptingRandomTapeCount
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) : Nat :=
  (acceptingRandomTapes machine input randomBits steps).card

/-- There are exactly `2 ^ length` Boolean tapes of length `length`. -/
theorem finiteBitTape_card (length : Nat) :
    Fintype.card (FiniteBitTape length) = 2 ^ length := by
  simp [FiniteBitTape]

/-- The accepting count cannot exceed the total number of random tapes. -/
theorem acceptingRandomTapeCount_le
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) :
    acceptingRandomTapeCount machine input randomBits steps ≤ 2 ^ randomBits := by
  calc
    acceptingRandomTapeCount machine input randomBits steps =
        (acceptingRandomTapes machine input randomBits steps).card := rfl
    _ ≤ (Finset.univ : Finset (FiniteBitTape randomBits)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (FiniteBitTape randomBits) := by simp
    _ = 2 ^ randomBits := finiteBitTape_card randomBits

/--
Exact uniform acceptance probability over the separate finite random tape.
The numerator and denominator are finite natural numbers embedded in `Rat`.
-/
def acceptanceProbability
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) : Rat :=
  (acceptingRandomTapeCount machine input randomBits steps : Rat) /
    (2 ^ randomBits : Rat)

/-- A descriptive alias used when several probability models are in scope. -/
abbrev randomizedAcceptanceProbability := acceptanceProbability

theorem acceptanceProbability_nonneg
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) :
    0 ≤ acceptanceProbability machine input randomBits steps := by
  unfold acceptanceProbability
  positivity

theorem acceptanceProbability_le_one
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) :
    acceptanceProbability machine input randomBits steps ≤ 1 := by
  have hCount :
      (acceptingRandomTapeCount machine input randomBits steps : Rat) ≤
        (2 ^ randomBits : Rat) := by
    exact_mod_cast acceptingRandomTapeCount_le machine input randomBits steps
  have hPositive : (0 : Rat) < 2 ^ randomBits := by positivity
  unfold acceptanceProbability
  apply (div_le_iff₀ hPositive).2
  simpa using hCount

/-- The exact finite acceptance probability lies in the rational unit interval. -/
theorem acceptanceProbability_mem_unitInterval
    (machine : RandomizedMachine) (input : List Bool)
    (randomBits steps : Nat) :
    0 ≤ acceptanceProbability machine input randomBits steps ∧
      acceptanceProbability machine input randomBits steps ≤ 1 :=
  ⟨acceptanceProbability_nonneg machine input randomBits steps,
    acceptanceProbability_le_one machine input randomBits steps⟩

end OneTapeMagnification
end Frontier
end Pnp4
