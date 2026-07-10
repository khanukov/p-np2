import Complexity.Interfaces

/-!
# A polynomial-clock operational complexity track

The repository `TM` stores an unrestricted function `runTime : Nat -> Nat`.
`RuntimeAdviceBarrier` shows that merely bounding this field does not prevent
it from carrying one arbitrary advice bit per input length.

This module adds a separate uniform track.  An `OperationalTM` contains one
finite transition table, one natural exponent, and a Boolean output map on its
finite state set.  Its execution TM is built with clock
`n ^ exponent + exponent` by definition.  There is no length-indexed field in
the program, while the output map makes deterministic complement literal and
executable.

The resulting `UniformP` and `UniformNP` are additive infrastructure.  A
separate canonical, explicitly numbered presentation embeds both into the old
repository classes and into the repaired classes.  No converse normalization
theorem, bridge from the old unrestricted-runtime classes, streaming upper
bound, or `P != NP` theorem is claimed here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalUniformity

open Pnp3.ComplexityInterfaces

abbrev RepoTM := Pnp3.Internal.PsubsetPpoly.TM.{0}

/-! ## Clock-normalized machine with an explicit Boolean output -/

/--
One finite transition system, a natural polynomial-clock exponent, and a
total Boolean observation of the final state.  The execution carrier below
constructs `runTime n = n ^ exponent + exponent` definitionally; the program
itself has no length-indexed field.
-/
structure OperationalTM where
  state : Type
  [stateFintype : Fintype state]
  [stateDecEq : DecidableEq state]
  start : state
  step : state -> Bool ->
    state × Bool × Pnp3.Internal.PsubsetPpoly.Move
  exponent : Nat
  output : state -> Bool

attribute [instance] OperationalTM.stateFintype
attribute [instance] OperationalTM.stateDecEq

namespace OperationalTM

/--
Reuse the finite control of an existing repository machine while deliberately
discarding its old runtime field.  Correctness at the new canonical clock is
not automatic and must be proved by the caller.
-/
def ofRepoCore (machine : RepoTM) (exponent : Nat)
    (output : machine.state -> Bool) : OperationalTM where
  state := machine.state
  stateFintype := machine.stateFintype
  stateDecEq := machine.stateDecEq
  start := machine.start
  step := machine.step
  exponent := exponent
  output := output

/-- Repository execution carrier with a definitional canonical clock.
Its `accept` field is irrelevant because `OperationalTM.accepts` observes the
explicit Boolean output map instead. -/
def executionTM (program : OperationalTM) : RepoTM where
  state := program.state
  stateFintype := program.stateFintype
  stateDecEq := program.stateDecEq
  start := program.start
  accept := program.start
  step := program.step
  runTime := fun inputLength =>
    inputLength ^ program.exponent + program.exponent

@[simp] theorem executionTM_runTime (program : OperationalTM)
    (inputLength : Nat) :
    program.executionTM.runTime inputLength =
      inputLength ^ program.exponent + program.exponent :=
  rfl

/-- Run the fixed transition system at its canonical clock and observe it. -/
def accepts (program : OperationalTM) (inputLength : Nat)
    (input : Bitstring inputLength) : Bool :=
  program.output
    ((program.executionTM.run (n := inputLength) input).state)

/-- Boolean complement changes no transition, tape cell, or clock value. -/
def complement (program : OperationalTM) : OperationalTM where
  state := program.state
  stateFintype := program.stateFintype
  stateDecEq := program.stateDecEq
  start := program.start
  step := program.step
  exponent := program.exponent
  output := fun state => !(program.output state)

@[simp] theorem complement_accepts (program : OperationalTM)
    (inputLength : Nat) (input : Bitstring inputLength) :
    program.complement.accepts inputLength input =
      !(program.accepts inputLength input) :=
  rfl

end OperationalTM

/-! ## Repaired deterministic and nondeterministic classes -/

/-- One operational program decides every input length. -/
def UniformP (language : Language) : Prop :=
  exists program : OperationalTM,
    forall inputLength (input : Bitstring inputLength),
      program.accepts inputLength input = language inputLength input

/-- A clock-normalized verifier with a finite-data polynomial witness bound. -/
def UniformNP (language : Language) : Prop :=
  exists verifier : OperationalTM,
  exists witnessExponent : Nat,
    forall inputLength (input : Bitstring inputLength),
      language inputLength input = true <->
        exists witness : Bitstring
            (Pnp3.ComplexityInterfaces.certificateLength
              inputLength witnessExponent),
          verifier.accepts
              (inputLength +
                Pnp3.ComplexityInterfaces.certificateLength
                  inputLength witnessExponent)
              (Pnp3.ComplexityInterfaces.concatBitstring input witness) = true

/-- Predicate inequality for the repaired classes.  This module proves neither
`UniformP <= UniformNP` nor equivalence with a conventional halting model, so
this definition is not itself an unconditional `P != NP` result. -/
def UniformP_ne_UniformNP : Prop :=
  Not (UniformP = UniformNP)

/-- Pointwise Boolean complement of a language. -/
def complementLanguage (language : Language) : Language :=
  fun inputLength input => !(language inputLength input)

/-- Deterministic operational polynomial time is closed under complement. -/
theorem uniformP_complement {language : Language}
    (hlanguage : UniformP language) :
    UniformP (complementLanguage language) := by
  rcases hlanguage with ⟨program, hcorrect⟩
  refine ⟨program.complement, ?_⟩
  intro inputLength input
  simp [hcorrect, complementLanguage]

/-! ## Explicit repo-compatible finite syntax -/

/--
An explicitly numbered finite transition table with a definitional polynomial
clock.  Unlike the old repository `TM`, it has no `Nat -> Nat` data field.
-/
structure CanonicalClockTM where
  stateCount : Nat
  stateCount_pos : 0 < stateCount
  start : Fin stateCount
  accept : Fin stateCount
  step : Fin stateCount -> Bool ->
    Fin stateCount × Bool × Pnp3.Internal.PsubsetPpoly.Move
  exponent : Nat

namespace CanonicalClockTM

def clock (machine : CanonicalClockTM) (inputLength : Nat) : Nat :=
  inputLength ^ machine.exponent + machine.exponent

def toRepoTM (machine : CanonicalClockTM) : RepoTM where
  state := Fin machine.stateCount
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := machine.start
  accept := machine.accept
  step := machine.step
  runTime := machine.clock

/--
The same canonical transition table as a repaired operational program.
Acceptance is observed after the run instead of being stored in the execution
carrier's otherwise irrelevant `accept` field.
-/
def toOperationalTM (machine : CanonicalClockTM) : OperationalTM where
  state := Fin machine.stateCount
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := machine.start
  step := machine.step
  exponent := machine.exponent
  output := fun state => decide (state = machine.accept)

/-- A copy of a canonical machine with only the observational accept state
changed.  Execution does not inspect this field. -/
private def withAccept (machine : CanonicalClockTM)
    (accept : Fin machine.stateCount) : RepoTM where
  state := Fin machine.stateCount
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := machine.start
  accept := accept
  step := machine.step
  runTime := machine.clock

/-- Pointwise agreement between configurations of machines that differ only
in their observational accept state. -/
private def ConfigAgree (machine : CanonicalClockTM)
    (left right : Fin machine.stateCount) {inputLength : Nat}
    (leftConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine left) inputLength)
    (rightConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine right) inputLength) : Prop :=
  leftConfig.state = rightConfig.state ∧
    leftConfig.head = rightConfig.head ∧
      leftConfig.tape = rightConfig.tape

private theorem initialAgree (machine : CanonicalClockTM)
    (left right : Fin machine.stateCount) {inputLength : Nat}
    (input : Bitstring inputLength) :
    ConfigAgree machine left right
      ((withAccept machine left).initialConfig input)
      ((withAccept machine right).initialConfig input) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem stepAgree (machine : CanonicalClockTM)
    (left right : Fin machine.stateCount) {inputLength : Nat}
    {leftConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine left) inputLength}
    {rightConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine right) inputLength}
    (hagrees : ConfigAgree machine left right leftConfig rightConfig) :
    ConfigAgree machine left right
      ((withAccept machine left).stepConfig leftConfig)
      ((withAccept machine right).stepConfig rightConfig) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  unfold ConfigAgree
  unfold Pnp3.Internal.PsubsetPpoly.TM.stepConfig
  simp only [withAccept]
  rw [hstate, hhead, htape]
  refine ⟨rfl, ?_, ?_⟩
  · unfold Pnp3.Internal.PsubsetPpoly.TM.Configuration.moveHead
    simp only [Pnp3.Internal.PsubsetPpoly.TM.tapeLength, withAccept]
    split <;> simp_all
  · unfold Pnp3.Internal.PsubsetPpoly.TM.Configuration.write
    funext index
    split <;> simp_all

private theorem runConfigAgree (machine : CanonicalClockTM)
    (left right : Fin machine.stateCount) {inputLength : Nat}
    {leftConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine left) inputLength}
    {rightConfig : Pnp3.Internal.PsubsetPpoly.TM.Configuration
      (M := withAccept machine right) inputLength}
    (hagrees : ConfigAgree machine left right leftConfig rightConfig)
    (steps : Nat) :
    ConfigAgree machine left right
      ((withAccept machine left).runConfig leftConfig steps)
      ((withAccept machine right).runConfig rightConfig steps) := by
  induction steps with
  | zero => exact hagrees
  | succ steps ih =>
      rw [Pnp3.Internal.PsubsetPpoly.TM.runConfig]
      rw [Function.iterate_succ_apply']
      rw [Pnp3.Internal.PsubsetPpoly.TM.runConfig]
      rw [Function.iterate_succ_apply']
      exact stepAgree machine left right ih

private theorem runState_withAccept
    (machine : CanonicalClockTM)
    (left right : Fin machine.stateCount)
    (inputLength : Nat) (input : Bitstring inputLength) :
    ((withAccept machine left).run input).state =
      ((withAccept machine right).run input).state := by
  unfold Pnp3.Internal.PsubsetPpoly.TM.run
  exact (runConfigAgree machine left right
    (initialAgree machine left right input)
    (machine.clock inputLength)).1

@[simp] theorem toRepoTM_runTime
    (machine : CanonicalClockTM) (inputLength : Nat) :
    machine.toRepoTM.runTime inputLength =
      inputLength ^ machine.exponent + machine.exponent :=
  rfl

/-- The operational and repository observations of a canonical machine agree
exactly.  Both executions use the same start state, transition table, and
definitional clock; the repository `accept` field is only inspected here. -/
@[simp] theorem toOperationalTM_accepts
    (machine : CanonicalClockTM) (inputLength : Nat)
    (input : Bitstring inputLength) :
    machine.toOperationalTM.accepts inputLength input =
      Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := machine.toRepoTM) (n := inputLength) input :=
  by
    unfold OperationalTM.accepts
      Pnp3.Internal.PsubsetPpoly.TM.accepts
    simp only [toOperationalTM]
    congr 2
    change ((withAccept machine machine.start).run input).state =
      ((withAccept machine machine.accept).run input).state
    exact runState_withAccept machine machine.start machine.accept
      inputLength input

end CanonicalClockTM

/-- The explicitly numbered, repository-compatible deterministic variant. -/
def CanonicalUniformP (language : Language) : Prop :=
  exists machine : CanonicalClockTM,
    forall inputLength (input : Bitstring inputLength),
      Pnp3.Internal.PsubsetPpoly.TM.accepts
          (M := machine.toRepoTM) (n := inputLength) input =
        language inputLength input

/-- The analogous explicitly numbered verifier variant. -/
def CanonicalUniformNP (language : Language) : Prop :=
  exists machine : CanonicalClockTM,
  exists witnessExponent : Nat,
    forall inputLength (input : Bitstring inputLength),
      language inputLength input = true <->
        exists witness : Bitstring
            (Pnp3.ComplexityInterfaces.certificateLength
              inputLength witnessExponent),
          Pnp3.Internal.PsubsetPpoly.TM.accepts
              (M := machine.toRepoTM)
              (n := inputLength +
                Pnp3.ComplexityInterfaces.certificateLength
                  inputLength witnessExponent)
              (Pnp3.ComplexityInterfaces.concatBitstring input witness) = true

theorem canonicalUniformP_subset_repoP {language : Language} :
    CanonicalUniformP language -> P language := by
  rintro ⟨machine, hcorrect⟩
  refine ⟨machine.toRepoTM, machine.exponent, ?_, hcorrect⟩
  intro inputLength
  simp

/-- Every explicitly canonical deterministic machine is already a repaired
operational machine; no runtime normalization hypothesis is needed. -/
theorem canonicalUniformP_subset_uniformP {language : Language} :
    CanonicalUniformP language -> UniformP language := by
  rintro ⟨machine, hcorrect⟩
  refine ⟨machine.toOperationalTM, ?_⟩
  intro inputLength input
  simpa using hcorrect inputLength input

theorem canonicalUniformNP_subset_repoNP {language : Language} :
    CanonicalUniformNP language -> NP language := by
  rintro ⟨machine, witnessExponent, hcorrect⟩
  refine ⟨machine.toRepoTM, machine.exponent, witnessExponent, ?_, hcorrect⟩
  intro inputLength
  simp

/-- The same exact compilation transports canonical verifiers and their
unchanged polynomial witness lengths into the repaired nondeterministic class.
-/
theorem canonicalUniformNP_subset_uniformNP {language : Language} :
    CanonicalUniformNP language -> UniformNP language := by
  rintro ⟨machine, witnessExponent, hcorrect⟩
  refine ⟨machine.toOperationalTM, witnessExponent, ?_⟩
  intro inputLength input
  simpa using hcorrect inputLength input

/-! ## Executable sanity witnesses -/

def boolState : Bool -> Fin 2
  | false => ⟨0, by decide⟩
  | true => ⟨1, by decide⟩

def constantMachine (answer : Bool) : CanonicalClockTM where
  stateCount := 2
  stateCount_pos := by decide
  start := boolState answer
  accept := boolState true
  step := fun state symbol =>
    (state, symbol, Pnp3.Internal.PsubsetPpoly.Move.stay)
  exponent := 0

def constantLanguage (answer : Bool) : Language :=
  fun _inputLength _input => answer

@[simp] theorem constantMachine_accepts
    (answer : Bool) (inputLength : Nat) (input : Bitstring inputLength) :
    Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := (constantMachine answer).toRepoTM)
        (n := inputLength) input = answer := by
  cases answer <;> rfl

/-- Direct closure-friendly operational program for a constant answer. -/
def constantProgram (answer : Bool) : OperationalTM where
  state := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := answer
  step := fun state symbol =>
    (state, symbol, Pnp3.Internal.PsubsetPpoly.Move.stay)
  exponent := 0
  output := fun state => state

@[simp] theorem constantProgram_accepts
    (answer : Bool) (inputLength : Nat) (input : Bitstring inputLength) :
    (constantProgram answer).accepts inputLength input = answer := by
  cases answer <;> rfl

theorem constantLanguage_in_canonicalUniformP (answer : Bool) :
    CanonicalUniformP (constantLanguage answer) := by
  refine ⟨constantMachine answer, ?_⟩
  intro inputLength input
  simpa only [constantLanguage] using
    constantMachine_accepts answer inputLength input

theorem constantLanguage_in_uniformP (answer : Bool) :
    UniformP (constantLanguage answer) := by
  refine ⟨constantProgram answer, ?_⟩
  intro inputLength input
  simpa only [constantLanguage] using
    constantProgram_accepts answer inputLength input

end OperationalUniformity
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.uniformP_complement
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.canonicalUniformP_subset_repoP
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.canonicalUniformNP_subset_repoNP
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.canonicalUniformP_subset_uniformP
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.canonicalUniformNP_subset_uniformNP
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalUniformity.constantLanguage_in_uniformP
