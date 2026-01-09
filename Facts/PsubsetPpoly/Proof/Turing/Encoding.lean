import Proof.Bitstring
import Mathlib.Data.Fintype.Basic

universe u

/-!
`Turing/Encoding` provides a lightweight operational model for the
deterministic Turing machines mentioned in `ComplexityClasses.lean`.
The model is intentionally simple: we use a single binary tape together
with a finite control.  Despite the simplicity, the definitions below
are powerful enough to support the classical simulation of
polynomial-time machines by polynomial-size circuits.

As part of the collision-avoidance effort we wrap the whole development in the
`Facts.PsubsetPpoly` namespace.  This keeps the exported symbols isolated from
the Turing machine library shipped with the main repository while preserving the standalone usability of
this proof bundle.
-/

namespace Facts
namespace PsubsetPpoly

/--
Direction of the tape head movement.  We explicitly keep a `stay` case
although the construction below never relies on it; it slightly
simplifies some lemmas.
-/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/--
`TM` packages the finite control of a single-tape deterministic Turing
machine operating over the binary alphabet.  The tape alphabet is
implicitly `{0,1}`; the symbol `false` acts as the blank character.

The structure refrains from including any operational semantics.  Those
are developed in the remainder of the file so that other parts of the
project can reason about machine runs without having to rebuild the
standard definitions every time.
-/
structure TM where
  /-- Finite set of control states. -/
  state : Type u
  [stateFintype : Fintype state]
  [stateDecEq : DecidableEq state]
  /-- The start state. -/
  start : state
  /-- The unique accepting state.  Reaching this state after the allotted
      number of steps counts as acceptance. -/
  accept : state
  /-- Transition function.  Given the current state and the bit under the
      head it returns the next control state, the bit to be written and
      the head movement. -/
  step : state → Bool → state × Bool × Move
  /-- A time bound specified as `n ↦ n^c + c` in the applications. -/
  runTime : ℕ → ℕ

attribute [instance] TM.stateFintype
attribute [instance] TM.stateDecEq

namespace TM

variable (M : TM)

/-- Number of tape cells allocated for inputs of length `n`.  The head
may move by at most `runTime n` positions in either direction, hence we
reserve `n + runTime n + 1` cells which suffices to cover all visited
locations. -/
def tapeLength (n : ℕ) : ℕ := n + M.runTime n + 1

lemma tapeLength_pos (n : ℕ) : 0 < M.tapeLength n := by
  simp [TM.tapeLength]

/-- Configurations for inputs of length `n`.  The tape is modelled as a
fixed-length binary vector. -/
structure Configuration (n : ℕ) where
  /-- Current control state. -/
  state : M.state
  /-- Head position encoded as an element of `Fin (tapeLength n)`. -/
  head : Fin (M.tapeLength n)
  /-- Contents of the tape. -/
  tape : Fin (M.tapeLength n) → Bool

namespace Configuration

variable {M}

/-- Tape obtained by writing `b` at position `i`. -/
def write {n : ℕ} (c : Configuration (M := M) n) (i : Fin (M.tapeLength n))
    (b : Bool) : Fin (M.tapeLength n) → Bool := fun j =>
  if h : j = i then b else c.tape j

@[simp]
lemma write_self {n : ℕ} (c : Configuration (M := M) n)
    (i : Fin (M.tapeLength n)) (b : Bool) :
    c.write i b i = b := by
  simp [write]

@[simp]
lemma write_other {n : ℕ} (c : Configuration (M := M) n)
    {i j : Fin (M.tapeLength n)} (h : j ≠ i) (b : Bool) :
    c.write i b j = c.tape j := by
  simp [write, h]

/-- Move the head according to a `Move` command, clamping it to the tape
boundaries. -/
def moveHead {n : ℕ} (c : Configuration (M := M) n)
    (m : Move) : Fin (M.tapeLength n) :=
  match m with
  | Move.left  =>
      if _ : (c.head : ℕ) = 0 then
        c.head
      else
        ⟨(c.head : ℕ) - 1, by
          have hlt := c.head.is_lt
          have hle : (c.head : ℕ) - 1 ≤ (c.head : ℕ) := Nat.sub_le _ _
          exact lt_of_le_of_lt hle hlt⟩
  | Move.stay  => c.head
  | Move.right =>
      if h : (c.head : ℕ) + 1 < M.tapeLength n then
        ⟨(c.head : ℕ) + 1, h⟩
      else
        c.head

end Configuration

/-- Initial configuration for an input `x : Bitstring n`.  The first `n`
cells of the tape store the input bits; the remaining cells are blank. -/
def initialConfig {n : ℕ} (x : Boolcube.Point n) : Configuration (M := M) n where
  state := M.start
  head := ⟨0, by
    simp [TM.tapeLength]⟩
  tape := fun j => if h : (j : ℕ) < n then x ⟨j, h⟩ else false

@[simp]
lemma initial_tape_input {n : ℕ} (x : Boolcube.Point n)
    {i : Fin (M.tapeLength n)} (hi : (i : ℕ) < n) :
    (M.initialConfig x).tape i = x ⟨i, hi⟩ := by
  simp [initialConfig, hi]

@[simp]
lemma initial_tape_blank {n : ℕ} (x : Boolcube.Point n)
    {i : Fin (M.tapeLength n)} (hi : n ≤ (i : ℕ)) :
    (M.initialConfig x).tape i = false := by
  have : ¬ (i : ℕ) < n := by exact not_lt.mpr hi
  simp [initialConfig, this]

@[simp]
lemma initial_head {n : ℕ} (x : Boolcube.Point n) :
    (M.initialConfig x).head = ⟨0, by
      simp [TM.tapeLength]⟩ := rfl

@[simp]
lemma initial_state {n : ℕ} (x : Boolcube.Point n) :
    (M.initialConfig x).state = M.start := rfl

/-- Perform a single transition from configuration `c`. -/
def stepConfig {n : ℕ} (c : Configuration (M := M) n) :
    Configuration (M := M) n :=
  let symbol := c.tape c.head
  let (q', b', m) := M.step c.state symbol
  {
    state := q'
    head := Configuration.moveHead (c := c) m
    tape := c.write c.head b'
  }

/-- Run the machine for exactly `t` steps. -/
def runConfig {n : ℕ} (c : Configuration (M := M) n) (t : ℕ) :
    Configuration (M := M) n :=
  Nat.iterate (stepConfig (M := M)) t c

/-- Execute the machine on input `x` for `runTime n` steps. -/
def run {n : ℕ} (x : Boolcube.Point n) : Configuration (M := M) n :=
  runConfig (M := M) (M.initialConfig x) (M.runTime n)

/-- Acceptance predicate: the state after `runTime n` steps equals the
designated accepting state. -/
def accepts (n : ℕ) (x : Boolcube.Point n) : Bool :=
  decide ((M.run (n := n) x).state = M.accept)

end TM

end PsubsetPpoly
end Facts
