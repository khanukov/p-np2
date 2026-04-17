import Complexity.PsubsetPpolyInternal.TuringEncoding
import Mathlib.Data.Fintype.Sigma

/-!
# Turing toolkit — Session 1: phased programs

Foundation layer for compositional construction of Turing machines in the
`Pnp3.Internal.PsubsetPpoly.TM` model.

A `PhasedProgram` groups a finite family of phases; each phase carries
its own local finite state type.  Compiling the phased program via
`PhasedProgram.toTM` yields a plain `TM` whose global state is
`Σ i : Fin numPhases, phaseState i`.  The compilation is definitionally
transparent: `(toTM P).step ⟨i, q⟩ b = P.transition i q b`, and similar
equations hold for `start`, `accept`, and `runTime`.

This module is the first installment of the toolkit required to
internalize `AsymptoticFormulaTrackData.asymptoticNP_TM` without new
axioms.  Subsequent sessions will layer tape-invariants and
NP-verifier-specific combinators on top of this foundation.

The file introduces no axioms and no unfinished proof placeholders;
every declaration is mathematically exact.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly

universe u

namespace TM

/--
A structured description of a Turing machine split into phases.

Each phase `i : Fin numPhases` has its own local control state type
`phaseState i`, required to be a finite type with decidable equality.
The transition function takes the current phase index, local state and
the scanned bit, and returns the next `(phase, state)` pair together
with the bit to write and the head movement.

Acceptance is determined by a single distinguished pair
`⟨acceptPhase, acceptState⟩`.

Compilation to a flat `TM` is carried out by `toTM`.
-/
structure PhasedProgram where
  /-- Number of phases. -/
  numPhases : Nat
  /-- Local control state type for each phase. -/
  phaseState : Fin numPhases → Type u
  /-- Finiteness of each phase's state type. -/
  instFin : ∀ i, Fintype (phaseState i)
  /-- Decidable equality of each phase's state type. -/
  instDec : ∀ i, DecidableEq (phaseState i)
  /-- Initial phase index. -/
  startPhase : Fin numPhases
  /-- Initial local state within `startPhase`. -/
  startState : phaseState startPhase
  /-- Accepting phase index. -/
  acceptPhase : Fin numPhases
  /-- Accepting local state within `acceptPhase`. -/
  acceptState : phaseState acceptPhase
  /-- Transition: given current phase, local state, and scanned bit,
      return the next global `(phase, state)`, the bit to write and a
      head move. -/
  transition : (i : Fin numPhases) → phaseState i → Bool →
    (Σ j : Fin numPhases, phaseState j) × Bool × Move
  /-- Declared runtime bound (used verbatim as `TM.runTime`). -/
  timeBound : Nat → Nat

namespace PhasedProgram

variable (P : PhasedProgram)

/-- Aggregated state type of the compiled TM. -/
@[reducible] def State : Type u :=
  Σ i : Fin P.numPhases, P.phaseState i

/-- Expose `P.instFin` as a top-level instance so Mathlib's
    `Sigma.instFintype` can synthesise `Fintype P.State`. -/
instance (P : PhasedProgram) (i : Fin P.numPhases) :
    Fintype (P.phaseState i) := P.instFin i

/-- Expose `P.instDec` as a top-level instance so Mathlib's Sigma
    decidable-equality machinery can synthesise `DecidableEq P.State`. -/
instance (P : PhasedProgram) (i : Fin P.numPhases) :
    DecidableEq (P.phaseState i) := P.instDec i

instance (P : PhasedProgram) : Fintype P.State := by
  unfold State
  infer_instance

instance (P : PhasedProgram) : DecidableEq P.State := by
  unfold State
  infer_instance

/--
Compile a phased program into a plain `TM`.

The compilation is a *definitional transparent embedding*: every
relevant projection of `toTM P` reduces to the corresponding field of
`P`, so downstream proofs inherit structure-level equalities for free
(see `toTM_step`, `toTM_start`, `toTM_accept`, `toTM_runTime`).
-/
def toTM (P : PhasedProgram) : TM.{u} where
  state := P.State
  start := ⟨P.startPhase, P.startState⟩
  accept := ⟨P.acceptPhase, P.acceptState⟩
  step := fun s b =>
    let pair := P.transition s.fst s.snd b
    (pair.fst, pair.snd.fst, pair.snd.snd)
  runTime := P.timeBound

/-! ### Transparent compilation lemmas -/

@[simp] theorem toTM_state : (P.toTM).state = P.State := rfl

@[simp] theorem toTM_start :
    (P.toTM).start = (⟨P.startPhase, P.startState⟩ : P.State) := rfl

@[simp] theorem toTM_accept :
    (P.toTM).accept = (⟨P.acceptPhase, P.acceptState⟩ : P.State) := rfl

@[simp] theorem toTM_runTime (n : Nat) :
    (P.toTM).runTime n = P.timeBound n := rfl

@[simp] theorem toTM_step (i : Fin P.numPhases) (q : P.phaseState i) (b : Bool) :
    (P.toTM).step ⟨i, q⟩ b =
      ((P.transition i q b).fst,
       (P.transition i q b).snd.fst,
       (P.transition i q b).snd.snd) := rfl

end PhasedProgram

/-!
## Pilot constructions (smoke-tests)

These minimal programs exercise the framework end-to-end: compilation,
acceptance semantics under `runTime = 0`, and the `toTM_*` transparency
lemmas.  They have no downstream dependencies; their sole purpose is to
guarantee the toolkit boots correctly and to serve as templates for
Session 2.

All proofs are `decide`-resolved, so they contribute no residual proof
obligations to callers.
-/

namespace Pilot

/--
Trivial one-phase program that accepts every input in zero steps.

* Single phase with `Unit` local state.
* `startState = acceptState`, so the initial configuration is already
  accepting, independently of tape contents or input length.
* `runTime = 0` matches the fact that no computation is necessary.
-/
def alwaysAccept : PhasedProgram.{0} where
  numPhases := 1
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := ()
  acceptPhase := 0
  acceptState := ()
  transition := fun _ _ _ => (⟨0, ()⟩, false, Move.stay)
  timeBound := fun _ => 0

theorem alwaysAccept_accepts (n : Nat) (x : Boolcube.Point n) :
    TM.accepts (M := alwaysAccept.toTM) n x = true := by
  -- `runTime = 0` so the run equals the initial configuration, whose
  -- state is `start = accept`.
  unfold TM.accepts TM.run TM.runConfig
  simp [alwaysAccept, PhasedProgram.toTM, TM.initialConfig]

/--
Trivial one-phase program that rejects every input in zero steps.

* Single phase with `Bool` local state.
* `startState = false`, `acceptState = true`, `runTime = 0`.  Starting
  and accepting states differ, and no steps run, so the machine rejects
  on every input regardless of tape contents.
-/
def alwaysReject : PhasedProgram.{0} where
  numPhases := 1
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := false
  acceptPhase := 0
  acceptState := true
  transition := fun _ q _ => (⟨0, q⟩, false, Move.stay)
  timeBound := fun _ => 0

theorem alwaysReject_rejects (n : Nat) (x : Boolcube.Point n) :
    TM.accepts (M := alwaysReject.toTM) n x = false := by
  unfold TM.accepts TM.run TM.runConfig
  simp [alwaysReject, PhasedProgram.toTM, TM.initialConfig]

end Pilot

/-!
## `runConfig` unfolding lemmas

These two equations expose the inductive structure of `runConfig` for
clean step-by-step reasoning in later sessions.  They are the only
non-`rfl` cornerstone between raw `Nat.iterate` and the "TM ran for
`k+1` steps" view.
-/

@[simp] theorem runConfig_zero {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    TM.runConfig (M := M) c 0 = c := rfl

theorem runConfig_succ {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat) :
    TM.runConfig (M := M) c (k + 1) = TM.stepConfig (M := M) (TM.runConfig (M := M) c k) := by
  unfold TM.runConfig
  exact Function.iterate_succ_apply' (TM.stepConfig (M := M)) k c

/-- Specialisation: running exactly one step from any configuration. -/
theorem runConfig_one {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    TM.runConfig (M := M) c 1 = TM.stepConfig (M := M) c := by
  have := runConfig_succ (M := M) (n := n) c 0
  simpa using this

/-- Compositional execution: running `k + m` steps is the same as
running `k` steps followed by `m` more.  This is the workhorse for
breaking multi-step proofs into phase segments.  -/
theorem runConfig_add {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k m : Nat) :
    TM.runConfig (M := M) c (k + m) =
      TM.runConfig (M := M) (TM.runConfig (M := M) c k) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := runConfig_succ (M := M) (n := n) c (k + m)
    have h2 := runConfig_succ (M := M) (n := n)
      (TM.runConfig (M := M) c k) m
    -- `k + (m+1) = (k+m) + 1`.
    have hsucc : k + (m + 1) = (k + m) + 1 := by omega
    rw [hsucc, h1, ih, ← h2]

/-!
### `stepConfig` on a compiled `PhasedProgram`

`toTM_stepConfig_unfolded` specialises `TM.stepConfig` on `P.toTM` so
that the resulting configuration is written in terms of `P.transition`
directly.  Consumers can chain this with `runConfig_succ` to step
through a phased trace without unfolding `PhasedProgram.toTM` by hand.
-/

namespace PhasedProgram

theorem toTM_stepConfig_unfolded {n : Nat} (P : PhasedProgram)
    (c : TM.Configuration (M := P.toTM) n) :
    TM.stepConfig (M := P.toTM) c =
      let bit := c.tape c.head
      let result := P.transition c.state.fst c.state.snd bit
      ({ state := result.fst
         head := TM.Configuration.moveHead (M := P.toTM) (c := c) result.snd.snd
         tape := c.write c.head result.snd.fst } :
         TM.Configuration (M := P.toTM) n) := by
  rfl

/-- `tapeLength` of a compiled `PhasedProgram` reduces to the declared
`timeBound`.  Purely definitional, but stating it lets downstream
proofs rewrite `(P.toTM).tapeLength n` without unfolding `toTM`. -/
@[simp] theorem toTM_tapeLength (P : PhasedProgram) (n : Nat) :
    (P.toTM).tapeLength n = n + P.timeBound n + 1 := rfl

end PhasedProgram

/-!
### Head-movement micro-API

`moveHead` is a dependent `dite` on head position; simp doesn't discharge
the bounds check automatically.  These three rewrite lemmas carve out
the three regimes relevant to Session 4's pilots and subsequent
verifier phases:

* `moveHead_stay` — `Move.stay` leaves the head unchanged (rfl);
* `moveHead_right_lt` — a `Move.right` within bounds advances the head
  by one;
* `moveHead_right_clamp` — a `Move.right` at the tape's right edge stays.

All three are stated so that simp can use them when the corresponding
numeric condition is available as a hypothesis.
-/

namespace Configuration

@[simp] theorem moveHead_stay {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    Configuration.moveHead (c := c) Move.stay = c.head := rfl

theorem moveHead_right_lt {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    (h : (c.head : ℕ) + 1 < M.tapeLength n) :
    Configuration.moveHead (c := c) Move.right = ⟨(c.head : ℕ) + 1, h⟩ := by
  unfold Configuration.moveHead
  rw [dif_pos h]

theorem moveHead_right_clamp {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    (h : ¬ ((c.head : ℕ) + 1 < M.tapeLength n)) :
    Configuration.moveHead (c := c) Move.right = c.head := by
  unfold Configuration.moveHead
  rw [dif_neg h]

end Configuration

/-!
## Session 5: Tape-invariant framework

Foundation for reasoning about *what is on the tape* after `k` steps.
The atomic observation is that `stepConfig` writes only at the current
head position — every other cell is preserved verbatim.  Iterating this
observation gives the compositional fact that **a cell the head never
visits during `runConfig c k` keeps its original value**.

Two versions of the compositional lemma are provided:

* `runConfig_tape_eq_of_unvisited` — per-cell criterion, needed
  whenever reasoning focuses on a specific position;
* `runConfig_tape_eq_on_region` — region-style, needed when reasoning
  about a whole sub-tape (e.g. "the input region is never
  overwritten").

These are the only lemmas required as the input layer to Session 6
(binary counter on tape) and beyond.
-/

/-- One `stepConfig` leaves every tape cell other than `c.head`
unchanged. -/
theorem stepConfig_tape_eq_of_ne {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    {i : Fin (M.tapeLength n)} (h : i ≠ c.head) :
    (TM.stepConfig (M := M) c).tape i = c.tape i := by
  -- `stepConfig` sets `tape := c.write c.head b'` for some `b'`.  The
  -- `write_other` lemma from `TuringEncoding` closes the goal because
  -- `i ≠ c.head` witnesses the "other" branch.
  show (c.write c.head _) i = c.tape i
  exact Configuration.write_other c h _

/-- Compositional version of `stepConfig_tape_eq_of_ne`: if a cell
`i` is never the head position during the first `k` steps of
`runConfig c`, the cell keeps its original value after `runConfig c k`.
-/
theorem runConfig_tape_eq_of_unvisited {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat)
    {i : Fin (M.tapeLength n)}
    (h : ∀ j, j < k → i ≠ (TM.runConfig (M := M) c j).head) :
    (TM.runConfig (M := M) c k).tape i = c.tape i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runConfig_succ]
    have hne : i ≠ (TM.runConfig (M := M) c k).head :=
      h k (Nat.lt_succ_self k)
    have hstep :
        (TM.stepConfig (M := M) (TM.runConfig (M := M) c k)).tape i =
          (TM.runConfig (M := M) c k).tape i :=
      stepConfig_tape_eq_of_ne _ hne
    rw [hstep]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

/-- Region-style corollary: if the head never enters a region `R`
during `k` steps, every cell in `R` retains its original value.

The hypothesis reads as "for every intermediate step `j < k`, the head
position does not satisfy `R`". -/
theorem runConfig_tape_eq_on_region {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat)
    (R : Fin (M.tapeLength n) → Prop)
    (h : ∀ j, j < k → ¬ R (TM.runConfig (M := M) c j).head) :
    ∀ i, R i → (TM.runConfig (M := M) c k).tape i = c.tape i := by
  intro i hi
  apply runConfig_tape_eq_of_unvisited
  intro j hj heq
  -- `i` satisfies `R`, and `heq : i = head j` would force the head to
  -- satisfy `R` — contradicting `h j hj`.
  exact h j hj (heq ▸ hi)

/-- Range-style specialisation of `runConfig_tape_eq_on_region`: if
the head position stays within `[a, b)` at every intermediate step,
every cell *outside* `[a, b)` is preserved.

This is the canonical form for MCSP-verifier reasoning where each
phase works in a contiguous tape window. -/
theorem runConfig_tape_eq_outside_range {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat) (a b : Nat)
    (h : ∀ j, j < k → a ≤ ((TM.runConfig (M := M) c j).head : ℕ) ∧
                        ((TM.runConfig (M := M) c j).head : ℕ) < b) :
    ∀ i : Fin (M.tapeLength n),
        ((i : ℕ) < a ∨ b ≤ (i : ℕ)) →
        (TM.runConfig (M := M) c k).tape i = c.tape i := by
  intro i hout
  apply runConfig_tape_eq_on_region
    (R := fun j => (j : ℕ) < a ∨ b ≤ (j : ℕ))
  · intro j hj hR
    obtain ⟨hge, hlt⟩ := h j hj
    rcases hR with h1 | h2
    · exact (Nat.not_lt.mpr hge) h1
    · exact (Nat.not_le.mpr hlt) h2
  · exact hout

/-!
## Session 6a: Binary counter — increment program definition

A `k`-bit binary counter is encoded as contiguous tape cells with the
LSB at `initial_head` and the MSB at `initial_head + k - 1`.  The
`incrementProgram k` below is the `PhasedProgram` that increments
such a counter by one, modulo `2^k`.

### Phase layout

* Phase `i` for `i < k` — "currently at the bit at offset `i` from
  the initial head; about to decide write/carry".
* Phase `k` — "overflow" phase, reached only when all `k` bits were
  `1` (counter wraps from `2^k-1` to `0`).
* Phase `k+1` — accepting phase, reached once the increment is done.

### Transition rules

* Phase `i` (`i < k`) reads bit `b`:
  - `b = 0`: write `1`, `Move.stay`, jump to phase `k+1` (accepting).
  - `b = 1`: write `0`, `Move.right`, advance to phase `i+1`.
* Phase `k`: write bit back unchanged, `Move.stay`, jump to phase
  `k+1`.  This phase is entered exactly once if the counter overflows.
* Phase `k+1` (accepting): idle — write bit back, `Move.stay`, loop.

### Correctness deferred

Session 6a delivers only the *definition* and structural `@[simp]`
projections (`numPhases`, `startPhase`, `acceptPhase`, `timeBound`).
The full "after `k+1` steps the counter value is `(prev + 1) mod
2^k`" correctness theorem is reserved for Session 7, where induction
on `k` using Session 5's tape-invariant lemmas closes it cleanly.
-/

namespace BinaryCounter

/-- `k`-bit binary counter increment, as a `PhasedProgram`.  The head
must start at the counter's LSB cell; after `k+1` steps the counter
has been incremented modulo `2^k` and the machine sits in its
accepting phase. -/
def incrementProgram (k : Nat) : PhasedProgram.{0} where
  numPhases := k + 2
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨k + 1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if hi : i.val < k then
      if b then
        -- bit = 1: carry.  Write 0, advance to phase `i+1`, move right.
        (⟨⟨i.val + 1, by omega⟩, ()⟩, false, Move.right)
      else
        -- bit = 0: increment complete.  Write 1, jump to accepting.
        (⟨⟨k + 1, by omega⟩, ()⟩, true, Move.stay)
    else
      -- `i.val ≥ k`: overflow phase or accepting phase.  Preserve bit,
      -- jump to accepting phase, no head movement.
      (⟨⟨k + 1, by omega⟩, ()⟩, b, Move.stay)
  timeBound := fun _ => k + 1

/-! ### Transparent structural projections -/

@[simp] theorem incrementProgram_numPhases (k : Nat) :
    (incrementProgram k).numPhases = k + 2 := rfl

@[simp] theorem incrementProgram_startPhase (k : Nat) :
    ((incrementProgram k).startPhase : Fin (k + 2)).val = 0 := rfl

@[simp] theorem incrementProgram_acceptPhase (k : Nat) :
    ((incrementProgram k).acceptPhase : Fin (k + 2)).val = k + 1 := rfl

@[simp] theorem incrementProgram_timeBound (k n : Nat) :
    (incrementProgram k).timeBound n = k + 1 := rfl

@[simp] theorem incrementProgram_phaseState (k : Nat) (i : Fin (k + 2)) :
    (incrementProgram k).phaseState i = Unit := rfl

end BinaryCounter

/-!
## Second-order pilot: read the first input bit

`readFirstBit` is a one-step `PhasedProgram` whose local state is
`Bool`.  It starts in state `false`, reads the bit under the head (the
first input bit, since the initial head is at position `0`), and
transitions to the state equal to that bit.  Acceptance is assigned to
state `true`.

Correctness (`readFirstBit_accepts`) shows:

* for `n ≥ 1`, the compiled TM accepts on `x` iff `x ⟨0, _⟩ = true`,
* for `n = 0`, it rejects (the head reads a blank `false`).

This pilot is the smallest non-trivial demonstration that the
`PhasedProgram` pipeline scales to runtimes beyond `0`.  Its proof
relies solely on the `runConfig_*` lemmas and the `@[simp]`
`initialConfig` lemmas from `TuringEncoding.lean`; no new axioms or
proof holes are introduced.
-/

namespace Pilot

/-- One-step program that copies the first input bit into the control
state and accepts iff that bit is `true`. -/
def readFirstBit : PhasedProgram.{0} where
  numPhases := 1
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := false
  acceptPhase := 0
  acceptState := true
  transition := fun _ _ b => (⟨0, b⟩, b, Move.stay)
  timeBound := fun _ => 1

/-- On `n ≥ 1`, `readFirstBit` accepts iff the first input bit is `true`. -/
theorem readFirstBit_accepts_pos (n : Nat) (hn : 0 < n) (x : Boolcube.Point n) :
    TM.accepts (M := readFirstBit.toTM) n x = x ⟨0, hn⟩ := by
  unfold TM.accepts TM.run
  rw [show readFirstBit.toTM.runTime n = 1 from rfl, runConfig_one]
  simp [TM.stepConfig, readFirstBit, PhasedProgram.toTM, TM.initialConfig, hn]

/-- On `n = 0` the machine has no input bit to read; the head cell is
blank (`false`), so the step moves to state `⟨0, false⟩` and rejects. -/
theorem readFirstBit_accepts_zero (x : Boolcube.Point 0) :
    TM.accepts (M := readFirstBit.toTM) 0 x = false := by
  unfold TM.accepts TM.run
  rw [show readFirstBit.toTM.runTime 0 = 1 from rfl, runConfig_one]
  simp [TM.stepConfig, readFirstBit, PhasedProgram.toTM, TM.initialConfig]

end Pilot

end TM

end PsubsetPpoly
end Internal
end Pnp3
