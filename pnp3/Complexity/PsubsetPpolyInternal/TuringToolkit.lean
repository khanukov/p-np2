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

/-- `Move.left` from any position yields a new head value no larger
than the current one.  At head `0`, the move clamps and the position
is unchanged; otherwise the value decreases by one.  Either way the
bound is sharp at `≤ c.head`. -/
theorem moveHead_left_val_le {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    ((Configuration.moveHead (c := c) Move.left) : ℕ) ≤ (c.head : ℕ) := by
  by_cases h : (c.head : ℕ) = 0
  · simp [Configuration.moveHead, h]
  · simp [Configuration.moveHead, h]

/-- One `moveHead` step never advances the head value by more than
one.  Applies uniformly across `Move.left`, `Move.stay`, `Move.right`,
including the boundary-clamping cases — so it is the right lemma for
head-position invariants that do not want to case-split on the move
direction or tape edge. -/
theorem moveHead_val_le_succ {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (m : Move) :
    ((Configuration.moveHead (c := c) m) : ℕ) ≤ (c.head : ℕ) + 1 := by
  cases m with
  | left =>
    have := moveHead_left_val_le (M := M) (n := n) c
    omega
  | stay =>
    simp
  | right =>
    by_cases h : (c.head : ℕ) + 1 < M.tapeLength n
    · rw [moveHead_right_lt (c := c) h]
    · rw [moveHead_right_clamp (c := c) h]
      exact Nat.le_succ _

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
### Session 6b: generic head-position bounds

Before using `runConfig_tape_eq_outside_range` on a specific program
we need a generic bound on how far the head can wander.  The
observation is purely model-level: `stepConfig` advances the head by
`moveHead _ m` for *some* move `m`, and `moveHead_val_le_succ` bounds
every single-step move by `+1`.  Chained inductively, this gives a
`+k` bound after `k` steps, regardless of TM or input.
-/

/-- Single-step head-position bound: `stepConfig`'s head value is at
most one more than the previous head value, independent of TM state
or tape contents. -/
theorem stepConfig_head_val_le_succ {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    ((TM.stepConfig (M := M) c).head : ℕ) ≤ (c.head : ℕ) + 1 := by
  -- Unfold `stepConfig`; the head field is `moveHead c m` for some
  -- `m`.  `moveHead_val_le_succ` discharges the bound uniformly.
  show ((Configuration.moveHead (c := c) _) : ℕ) ≤ _
  exact Configuration.moveHead_val_le_succ c _

/-- Multi-step head-position bound: after `j` executions of
`stepConfig`, the head position is at most `c.head.val + j`.
Completely generic across TM models; the proof is a straight
induction on `j` using `stepConfig_head_val_le_succ`. -/
theorem runConfig_head_val_le {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (j : Nat) :
    ((TM.runConfig (M := M) c j).head : ℕ) ≤ (c.head : ℕ) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [runConfig_succ]
    have step_le := stepConfig_head_val_le_succ
      (M := M) (n := n) (TM.runConfig (M := M) c j)
    omega

/-!
### Session 6c: Head monotonicity for never-left TMs

Many interesting verifier phases (including the binary counter) only
use `Move.right` and `Move.stay` — never `Move.left`.  For such TMs,
`stepConfig` and `runConfig` are head-monotone, giving the *lower*
bound needed to sandwich the head between `initial` and `initial + j`.

Combined with the upper bound from 6b and Session 5's
`runConfig_tape_eq_outside_range`, this yields full tape preservation
outside a program's designated working window.
-/

/-- Definitional equation: `stepConfig`'s head is the `moveHead` of the
current configuration under the move returned by `M.step`. -/
@[simp] theorem stepConfig_head {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    (TM.stepConfig (M := M) c).head =
      Configuration.moveHead (c := c)
        (M.step c.state (c.tape c.head)).snd.snd := rfl

/-- Definitional equation: `stepConfig`'s tape is `c.write` at the
head position with the bit emitted by `M.step`. -/
@[simp] theorem stepConfig_tape {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    (TM.stepConfig (M := M) c).tape =
      c.write c.head (M.step c.state (c.tape c.head)).snd.fst := rfl

/-- Definitional equation: `stepConfig`'s new state is the first
component of `M.step`. -/
@[simp] theorem stepConfig_state {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    (TM.stepConfig (M := M) c).state =
      (M.step c.state (c.tape c.head)).fst := rfl

/-- Predicate: the TM's step function never issues `Move.left`, for
any state and any scanned bit. -/
def TMNeverMovesLeft (M : TM.{u}) : Prop :=
  ∀ s b, (M.step s b).snd.snd ≠ Move.left

/-- In a never-left TM, a single `stepConfig` never *decreases* the
head value. -/
theorem stepConfig_head_val_ge_of_never_left {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    (hM : TMNeverMovesLeft M) :
    (c.head : ℕ) ≤ ((TM.stepConfig (M := M) c).head : ℕ) := by
  rw [stepConfig_head]
  have hne := hM c.state (c.tape c.head)
  generalize (M.step c.state (c.tape c.head)).snd.snd = m at hne
  cases m with
  | left => exact absurd rfl hne
  | stay => simp
  | right =>
    by_cases hb : (c.head : ℕ) + 1 < M.tapeLength n
    · rw [Configuration.moveHead_right_lt _ hb]
      simp
    · rw [Configuration.moveHead_right_clamp _ hb]

/-- Multi-step head-monotonicity for never-left TMs. -/
theorem runConfig_head_val_ge_of_never_left {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (j : Nat)
    (hM : TMNeverMovesLeft M) :
    (c.head : ℕ) ≤ ((TM.runConfig (M := M) c j).head : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [runConfig_succ]
    have step_ge := stepConfig_head_val_ge_of_never_left
      (M := M) (n := n) (TM.runConfig (M := M) c j) hM
    omega

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

/-!
### Head-position invariants for `incrementProgram`

The transition function of `incrementProgram k` only returns
`Move.right` or `Move.stay` — never `Move.left`.  Lifting this to the
compiled TM gives `TMNeverMovesLeft` and, via Session 6c generic
lemmas, head-monotonicity.  Combined with Session 6b's upper bound
and Session 5's tape-invariant lemmas, we obtain full tape
preservation outside `[initial_head, initial_head + k + 1)` — the
counter's working window.
-/

/-- `incrementProgram k`'s transition function never issues
`Move.left`. -/
theorem incrementProgram_transition_never_left (k : Nat)
    (i : Fin ((incrementProgram k).numPhases))
    (q : (incrementProgram k).phaseState i) (b : Bool) :
    ((incrementProgram k).transition i q b).snd.snd ≠ Move.left := by
  -- The transition splits on `i.val < k` and (inside) `b`.  Each of
  -- the three resulting branches emits `Move.right` or `Move.stay`.
  by_cases hi : i.val < k
  · by_cases hb : b = true
    · -- `i.val < k ∧ b = true` → `Move.right`.
      simp [incrementProgram, hi, hb]
    · -- `i.val < k ∧ b = false` → `Move.stay`.
      simp [incrementProgram, hi, hb]
  · -- `¬ (i.val < k)` → `Move.stay`.
    simp [incrementProgram, hi]

/-- Lift to the compiled TM: `(incrementProgram k).toTM` is
never-left. -/
theorem incrementProgram_toTM_never_moves_left (k : Nat) :
    TMNeverMovesLeft (incrementProgram k).toTM := by
  intro s b
  rcases s with ⟨i, q⟩
  -- `.toTM.step ⟨i, q⟩ b`'s third component equals
  -- `(transition i q b).snd.snd`.
  show ((incrementProgram k).transition i q b).snd.snd ≠ Move.left
  exact incrementProgram_transition_never_left k i q b

/-- Tape-preservation corollary: after running `incrementProgram k`
for its full `k + 1`-step budget, every tape cell *outside*
`[c.head, c.head + k + 1)` keeps its original value. -/
theorem incrementProgram_tape_preserved_outside {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (i : Fin ((incrementProgram k).toTM.tapeLength n))
    (hout : (i : ℕ) < (c.head : ℕ) ∨ (c.head : ℕ) + (k + 1) ≤ (i : ℕ)) :
    (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).tape i =
      c.tape i := by
  refine runConfig_tape_eq_outside_range
    (c := c) (k := k + 1)
    (a := (c.head : ℕ)) (b := (c.head : ℕ) + (k + 1))
    ?_ i hout
  intro j hj
  refine ⟨?_, ?_⟩
  · exact runConfig_head_val_ge_of_never_left c j
      (incrementProgram_toTM_never_moves_left k)
  · have := runConfig_head_val_le (M := (incrementProgram k).toTM) c j
    omega

/-!
### Session 7: Counter value semantics

`counterValue c start k` interprets the `k` tape cells starting at
position `start` as a little-endian binary number (LSB at position
`start`).  Cells outside the tape contribute `0`, so the function is
total.

The recursive shape (base case `k = 0`, step adding the `k`-th bit's
contribution `2^k`) makes induction-on-`k` the natural proof strategy
for all downstream correctness statements.

Session 7 delivers only the *definition* and a handful of structural
and bound lemmas.  The full `incrementProgram_correct` theorem —
"after `k+1` steps the counter value is `(prev + 1) mod 2^k`" — is
reserved for Session 7b, where case analysis on the first-zero bit
position discharges both the ripple-carry and overflow branches.
-/

/-- Little-endian binary interpretation of `k` tape cells starting at
position `start`.  Cells outside the tape contribute `0`. -/
def counterValue {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    counterValue c start k +
      (if hi : start + k < M.tapeLength n then
        (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
      else 0)

@[simp] theorem counterValue_zero {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    counterValue c start 0 = 0 := rfl

theorem counterValue_succ {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    counterValue c start (k + 1) =
      counterValue c start k +
        (if hi : start + k < M.tapeLength n then
          (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
        else 0) := rfl

/-- Each bit contributes at most `2^i` to the counter value, so the
total is strictly less than `2^k`.  Proved by straight induction on
`k`; the "cell out of range" branch contributes `0` (trivially
bounded) and the "cell in range" branch contributes `0` or `2^k`. -/
theorem counterValue_lt_two_pow {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    counterValue c start k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [counterValue_succ]
    -- Abstract the added term: the bit's contribution at position
    -- `start + k`, which is either `0` or `2^k`.
    set added : Nat :=
      (if hi : start + k < M.tapeLength n then
        (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
      else 0) with hadded
    have hadd_le : added ≤ 2 ^ k := by
      simp only [hadded]
      split_ifs
      · exact le_refl _
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [pow_succ]
      omega
    -- `counterValue + added < 2^k + added ≤ 2^k + 2^k = 2^(k+1)`.
    -- Combined in a single `omega` on the abstract terms.
    rw [hpow]
    omega

/-- The counter value is always non-negative (trivially, since it is
a `Nat`).  Stated explicitly for readability when combined with
`counterValue_lt_two_pow` as a range `[0, 2^k)`. -/
theorem counterValue_nonneg {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    0 ≤ counterValue c start k := Nat.zero_le _

/-!
### Session 7b: Tape agreement ⇒ counter agreement

Bridge lemma between tape-level equality (Session 5) and
semantic-level equality (Session 7).  If two configurations have
identical tape contents in the counter region `[start, start + k)`,
they have identical counter values.

Combined with `runConfig_tape_eq_on_region`, this lets us prove
`counterValue` is preserved across any execution whose head avoids
the counter region.
-/

/-- If two configurations agree on every tape cell in the region
`[start, start + k)`, they have the same `counterValue` there.

The hypothesis is stated on `p : Fin (M.tapeLength n)` rather than raw
`Nat` offsets so that out-of-range indices are simply never mentioned
— they are handled by the "cell out of tape bounds" branch of
`counterValue` (contributing `0` uniformly). -/
theorem counterValue_eq_of_tape_eq {M : TM.{u}} {n : Nat}
    (c1 c2 : Configuration (M := M) n) (start : Nat) :
    ∀ k : Nat,
      (∀ p : Fin (M.tapeLength n),
         start ≤ (p : ℕ) → (p : ℕ) < start + k →
         c1.tape p = c2.tape p) →
      counterValue c1 start k = counterValue c2 start k
  | 0, _ => rfl
  | k + 1, h => by
    rw [counterValue_succ, counterValue_succ]
    have h_prefix : ∀ p : Fin (M.tapeLength n),
        start ≤ (p : ℕ) → (p : ℕ) < start + k →
        c1.tape p = c2.tape p :=
      fun p h1 h2 => h p h1 (by omega)
    rw [counterValue_eq_of_tape_eq c1 c2 start k h_prefix]
    -- Inner added-bit contributions: case on whether cell in range.
    by_cases hbound : start + k < M.tapeLength n
    · simp only [dif_pos hbound]
      have hval : ((⟨start + k, hbound⟩ : Fin (M.tapeLength n)) : ℕ)
          = start + k := rfl
      rw [h ⟨start + k, hbound⟩ (by rw [hval]; omega) (by rw [hval]; omega)]
    · simp only [dif_neg hbound]

/-- Specialisation: if the head never enters the counter region
`[start, start + width)` during `runConfig c steps`, the counter
value at `start` is preserved. -/
theorem counterValue_runConfig_eq_of_head_avoids_region
    {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (steps start width : Nat)
    (h : ∀ i, i < steps →
         ¬ (start ≤ ((TM.runConfig (M := M) c i).head : ℕ) ∧
            ((TM.runConfig (M := M) c i).head : ℕ) < start + width)) :
    counterValue (TM.runConfig (M := M) c steps) start width =
      counterValue c start width := by
  apply counterValue_eq_of_tape_eq
  intro p hge hlt
  -- `p` lies in the counter region; by the hypothesis, the head
  -- never equals `p` during any of the `steps` iterations, so
  -- Session 5's `runConfig_tape_eq_on_region` preserves the cell.
  apply runConfig_tape_eq_on_region
    (R := fun q => start ≤ (q : ℕ) ∧ (q : ℕ) < start + width)
  · intro i hi hR
    exact h i hi hR
  · exact ⟨hge, hlt⟩

/-!
### Base case: `incrementProgram 0` correctness

The `k = 0` counter is degenerate — it has zero cells, so
`counterValue _ _ 0 = 0` unconditionally.  The increment is therefore
a no-op on the semantic level, and the correctness statement reduces
to `0 = (0 + 1) % 1 = 0`.

This is the first concrete instance of the general correctness
theorem `incrementProgram_correct`; Session 7c will prove the
general case via case analysis on the first-zero bit position.
-/

/-- `incrementProgram 0` trivially satisfies the correctness
equation: both sides are `0`. -/
theorem incrementProgram_correct_zero {n : Nat}
    (c : Configuration (M := (incrementProgram 0).toTM) n) :
    counterValue
        (TM.runConfig (M := (incrementProgram 0).toTM) c 1)
        (c.head : ℕ) 0 =
      (counterValue c (c.head : ℕ) 0 + 1) % 2 ^ 0 := by
  simp [counterValue_zero]

/-!
### Session 7c: Stability of the accepting phase

Once `incrementProgram k` reaches phase `k + 1` (the accepting
phase), subsequent `stepConfig` calls preserve the entire
configuration — state, head, and tape.  Reason: the transition
function's `else` branch (`i.val ≥ k`) writes the scanned bit back
unchanged, emits `Move.stay`, and jumps to phase `k + 1`.

This stability is the "post-termination" behaviour essential for
combining incrementProgram with downstream phases (once the counter
has been incremented, the machine does nothing harmful while waiting
for the budget to expire).
-/

/-- Writing the current tape bit back at the head position is a
no-op: the resulting tape function is equal to the original. -/
theorem write_self_eq {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (i : Fin (M.tapeLength n)) :
    c.write i (c.tape i) = c.tape := by
  funext j
  unfold Configuration.write
  split_ifs with h
  · rw [h]
  · rfl

/-- In phase `i` with `k ≤ i.val`, the transition produces
`(⟨k+1, ...⟩, same-bit, Move.stay)`.  Specifically the outer
`if hi : i.val < k` takes the `else` branch. -/
theorem incrementProgram_transition_phase_ge_k (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : k ≤ i.val)
    (q : (incrementProgram k).phaseState i) (b : Bool) :
    ((incrementProgram k).transition i q b).snd.snd = Move.stay ∧
    ((incrementProgram k).transition i q b).snd.fst = b ∧
    ((incrementProgram k).transition i q b).fst.fst.val = k + 1 := by
  have hi_ge : ¬ i.val < k := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi_ge]

/-- `stepConfig` from a configuration whose phase is `≥ k` leaves
the tape and head fixed and forces the state's phase to `k + 1`.
This covers both the "overflow" transition (phase `= k`) and the
"idle in accepting" case (phase `= k + 1`).

* the tape is unchanged (the scanned bit is written back),
* the head is unchanged (`Move.stay`),
* the state's phase component becomes `k + 1`.
-/
theorem incrementProgram_stepConfig_phase_ge_k {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hge : k ≤ c.state.fst.val) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape = c.tape ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 := by
  -- `(toTM.step c.state b).snd.{snd, fst}` definitionally equals
  -- `(transition ...).snd.{snd, fst}`, so the transition-level
  -- hypotheses transfer to the step-level goals by rfl coercion.
  obtain ⟨hmove, hbit, hphase⟩ :=
    incrementProgram_transition_phase_ge_k k (i := c.state.fst) hge
      c.state.snd (c.tape c.head)
  -- Lift each of the transition-level facts to a step-level fact.
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = k + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
    exact write_self_eq c c.head
  · rw [stepConfig_head, hmove_step]
    simp
  · rw [stepConfig_state]
    exact hphase_step

/-- Specialisation at `c.state.fst.val = k + 1` — the "already in
accepting phase" entry point.  Proof: apply
`incrementProgram_stepConfig_phase_ge_k` with `k ≤ k + 1`. -/
theorem incrementProgram_stepConfig_in_accepting {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape = c.tape ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 :=
  incrementProgram_stepConfig_phase_ge_k c (by rw [h]; omega)

/-- Iterated version: starting from an accepting configuration,
`runConfig` for any number of steps leaves the tape and head fixed
and keeps the state's phase at `k + 1`. -/
theorem incrementProgram_runConfig_in_accepting {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) (j : Nat) :
    (TM.runConfig (M := (incrementProgram k).toTM) c j).tape = c.tape ∧
    (TM.runConfig (M := (incrementProgram k).toTM) c j).head = c.head ∧
    (TM.runConfig (M := (incrementProgram k).toTM) c j).state.fst.val = k + 1 := by
  induction j with
  | zero =>
    refine ⟨rfl, rfl, h⟩
  | succ j ih =>
    obtain ⟨hTape, hHead, hPhase⟩ := ih
    rw [runConfig_succ]
    -- Apply single-step preservation at `runConfig c j`.
    obtain ⟨hT2, hH2, hP2⟩ :=
      incrementProgram_stepConfig_in_accepting
        (TM.runConfig (M := (incrementProgram k).toTM) c j) hPhase
    refine ⟨?_, ?_, ?_⟩
    · rw [hT2, hTape]
    · rw [hH2, hHead]
    · exact hP2

/-- Counter value is preserved once the machine enters the
accepting phase. -/
theorem incrementProgram_counterValue_stable_from_accepting
    {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) (j : Nat) (start width : Nat) :
    counterValue (TM.runConfig (M := (incrementProgram k).toTM) c j)
        start width =
      counterValue c start width := by
  obtain ⟨hTape, _, _⟩ :=
    incrementProgram_runConfig_in_accepting c h j
  -- Two configurations with identical tapes produce the same
  -- counterValue.
  apply counterValue_eq_of_tape_eq
  intro p _ _
  rw [hTape]

/-!
### Session 7d: Active-phase step behaviour

In any active phase (`i.val < k`), the transition splits on the
scanned bit:

* `bit = false` (the counter cell is `0`) — write `1`, jump to the
  accepting phase, `Move.stay`.  This is the "increment complete"
  branch.

* `bit = true` (the counter cell is `1`) — write `0`, advance to
  phase `i + 1`, `Move.right`.  This is the ripple-carry branch.

Both branches are characterised at the transition level and at the
`stepConfig` level.  Together with Session 7c's accepting-phase
stability, these four lemmas describe every possible single-step
transition of `incrementProgram k`.
-/

/-- Transition in an active phase with bit `0`: write `1`, jump to
phase `k + 1`, `Move.stay`. -/
theorem incrementProgram_transition_phase_lt_k_bit_false (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : i.val < k)
    (q : (incrementProgram k).phaseState i) :
    ((incrementProgram k).transition i q false).snd.snd = Move.stay ∧
    ((incrementProgram k).transition i q false).snd.fst = true ∧
    ((incrementProgram k).transition i q false).fst.fst.val = k + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi]

/-- Transition in an active phase with bit `1`: write `0`, advance
to phase `i + 1`, `Move.right`. -/
theorem incrementProgram_transition_phase_lt_k_bit_true (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : i.val < k)
    (q : (incrementProgram k).phaseState i) :
    ((incrementProgram k).transition i q true).snd.snd = Move.right ∧
    ((incrementProgram k).transition i q true).snd.fst = false ∧
    ((incrementProgram k).transition i q true).fst.fst.val = i.val + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi]

/-- `stepConfig` in an active phase when the scanned bit is `0`:
the cell is flipped `0 → 1`, the head stays, and the machine jumps
to the accepting phase. -/
theorem incrementProgram_stepConfig_phase_lt_k_bit_false {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hi : c.state.fst.val < k) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape =
        c.write c.head true ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 := by
  obtain ⟨hmove, hbit_out, hphase⟩ :=
    incrementProgram_transition_phase_lt_k_bit_false k
      (i := c.state.fst) hi c.state.snd
  -- Lift transition-level facts to step-level via defeq, using
  -- `hbit` to rewrite `c.tape c.head` in the goal to `false`.
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := by rw [hbit]; exact hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = true := by rw [hbit]; exact hbit_out
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = k + 1 := by rw [hbit]; exact hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_state]; exact hphase_step

/-- `stepConfig` in an active phase when the scanned bit is `1`:
the cell is flipped `1 → 0`, the head moves right, and the machine
advances to phase `i + 1`. -/
theorem incrementProgram_stepConfig_phase_lt_k_bit_true {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hi : c.state.fst.val < k) (hbit : c.tape c.head = true)
    (hhead_bound : (c.head : ℕ) + 1 < (incrementProgram k).toTM.tapeLength n) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape =
        c.write c.head false ∧
    ((TM.stepConfig (M := (incrementProgram k).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val =
        c.state.fst.val + 1 := by
  obtain ⟨hmove, hbit_out, hphase⟩ :=
    incrementProgram_transition_phase_lt_k_bit_true k
      (i := c.state.fst) hi c.state.snd
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.right := by rw [hbit]; exact hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = false := by rw [hbit]; exact hbit_out
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := by rw [hbit]; exact hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) hhead_bound]
  · rw [stepConfig_state]; exact hphase_step

/-!
### Session 7e: Correctness for `k = 1`

The first fully worked-out instance of `incrementProgram_correct`.
For a one-bit counter, the correctness equation is

  `counterValue (runConfig c 2) c.head.val 1 = (counterValue c c.head.val 1 + 1) % 2`.

The proof proceeds by case analysis on the scanned bit:

* `c.tape c.head = false` (counter = 0): step 0 flips the cell to
  `true` (via `stepConfig_phase_lt_k_bit_false`) and enters the
  accepting phase; step 1 is stable (via `stepConfig_phase_ge_k`).
  Final tape at the head reads `true`, so `counterValue = 1 =
  (0 + 1) % 2`.

* `c.tape c.head = true` (counter = 1): step 0 flips the cell to
  `false` and advances the head one cell to the right (phase
  becomes `k = 1`, the overflow phase); step 1 stays put in the
  overflow branch, yielding phase `k + 1 = 2`.  Final tape at the
  head reads `false`, so `counterValue = 0 = (1 + 1) % 2`.

The hypothesis `h_phase` expresses that the caller invokes the
program at phase `0` (the standard entry point), and `h_head`
ensures the tape has room for the right-move in the ripple branch.

This theorem validates the end-to-end machinery built across
Sessions 1–7d.  The general case (`k ≥ 2`) follows the same
structure but requires a parameterised induction on the position
of the first zero bit — deferred.
-/

/-- Auxiliary rewrite: `counterValue` for width `1` is the bit at
`start`, coerced to `Nat`. -/
theorem counterValue_one_eq {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    (p : Fin (M.tapeLength n)) :
    counterValue c (p : ℕ) 1 = (if c.tape p then 1 else 0) := by
  show 0 + (if hi : (p : ℕ) + 0 < M.tapeLength n then
              (if c.tape ⟨(p : ℕ) + 0, hi⟩ then 2 ^ 0 else 0)
            else 0)
        = (if c.tape p then 1 else 0)
  have hp : (p : ℕ) + 0 < M.tapeLength n := by
    have := p.isLt; omega
  have hmk : (⟨(p : ℕ) + 0, hp⟩ : Fin (M.tapeLength n)) = p := by
    apply Fin.ext; simp
  simp [dif_pos hp, pow_zero, hmk]

/-- Correctness of `incrementProgram` for `k = 1`. -/
theorem incrementProgram_correct_one {n : Nat}
    (c : Configuration (M := (incrementProgram 1).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_head : (c.head : ℕ) + 1 < (incrementProgram 1).toTM.tapeLength n) :
    counterValue
        (TM.runConfig (M := (incrementProgram 1).toTM) c 2)
        (c.head : ℕ) 1 =
      (counterValue c (c.head : ℕ) 1 + 1) % 2 ^ 1 := by
  -- `runConfig c 2 = stepConfig (stepConfig c)`.
  rw [show (2 : Nat) = 1 + 1 from rfl, runConfig_succ, runConfig_one]
  set c0 := TM.stepConfig (M := (incrementProgram 1).toTM) c with hc0_def
  have h_phase_lt : c.state.fst.val < 1 := by rw [h_phase]; omega
  -- Case on the initial bit.
  by_cases hbit : c.tape c.head = true
  · -- bit = true path: counter was 1, after increment it's 0.
    -- Step 0: flip to false, move right, phase 1.
    obtain ⟨ht0, hh0, hp0⟩ :=
      incrementProgram_stepConfig_phase_lt_k_bit_true c h_phase_lt hbit h_head
    -- Step 1: we are in phase 1 ≥ k = 1, so stepConfig is idle.
    have hc0_ge : 1 ≤ c0.state.fst.val := by
      rw [hc0_def, hp0, h_phase]
    obtain ⟨ht1, hh1, hp1⟩ :=
      incrementProgram_stepConfig_phase_ge_k c0 hc0_ge
    -- Final tape at head equals c.write c.head false at head = false.
    have h_counter_new :
        counterValue
            (TM.stepConfig (M := (incrementProgram 1).toTM) c0)
            (c.head : ℕ) 1 = 0 := by
      rw [counterValue_one_eq]
      have htape_at_head :
          (TM.stepConfig (M := (incrementProgram 1).toTM) c0).tape c.head
            = false := by
        rw [ht1, hc0_def, ht0]
        exact Configuration.write_self c c.head false
      rw [htape_at_head]; decide
    have h_counter_old : counterValue c (c.head : ℕ) 1 = 1 := by
      rw [counterValue_one_eq, hbit]; decide
    rw [h_counter_new, h_counter_old]
    decide
  · -- bit = false path: counter was 0, after increment it's 1.
    have hbit_false : c.tape c.head = false := by
      cases hval : c.tape c.head with
      | true => exact absurd hval hbit
      | false => rfl
    obtain ⟨ht0, hh0, hp0⟩ :=
      incrementProgram_stepConfig_phase_lt_k_bit_false c h_phase_lt hbit_false
    -- After step 0: phase = k + 1 = 2 ≥ 1. Step 1 is idle.
    have hc0_ge : 1 ≤ c0.state.fst.val := by
      rw [hc0_def, hp0]; omega
    obtain ⟨ht1, hh1, hp1⟩ :=
      incrementProgram_stepConfig_phase_ge_k c0 hc0_ge
    have h_counter_new :
        counterValue
            (TM.stepConfig (M := (incrementProgram 1).toTM) c0)
            (c.head : ℕ) 1 = 1 := by
      rw [counterValue_one_eq]
      have htape_at_head :
          (TM.stepConfig (M := (incrementProgram 1).toTM) c0).tape c.head
            = true := by
        rw [ht1, hc0_def, ht0]
        exact Configuration.write_self c c.head true
      rw [htape_at_head]; decide
    have h_counter_old : counterValue c (c.head : ℕ) 1 = 0 := by
      rw [counterValue_one_eq, hbit_false]
      decide
    rw [h_counter_new, h_counter_old]
    decide

/-!
### Session 7f: First-bit-zero correctness for arbitrary `k`

When the scanned cell (`c.tape c.head`) is `0`, the ripple logic
never triggers — step 0 flips the cell to `1` and jumps straight
to the accepting phase, and the remaining `k` steps are idle.

Under this hypothesis, the counter arithmetic is clean:
* the new counter value differs from the old one only in the LSB
  (the cell at `c.head` itself);
* the LSB was `0`, so `counterValue_old` is even, bounded by
  `2^k - 2`;
* adding `1` does not overflow, so `(old + 1) mod 2^k = old + 1`.

The general `k` case (first-zero bit at arbitrary position + the
all-ones overflow) requires tracking the ripple step-by-step; it
is the largest remaining piece of the counter correctness proof
and is reserved for Session 7g.
-/

/-- If only one position's bit differs between two tape functions,
`counterValue` differs by exactly the signed contribution of that
position.  Specialised to LSB flip `0 → 1`: new value = old + 1. -/
theorem counterValue_of_write_head_true {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat)
    (h_old : c.tape c.head = false) :
    ∀ (c' : Configuration (M := M) n),
      c'.tape = c.write c.head true →
      c'.head = c.head →
      counterValue c' (c.head : ℕ) k =
        counterValue c (c.head : ℕ) k +
          (if (c.head : ℕ) < (c.head : ℕ) + k then 1 else 0) := by
  induction k with
  | zero =>
    intro c' htape hhead
    simp
  | succ k ih =>
    intro c' htape hhead
    rw [counterValue_succ, counterValue_succ]
    -- Inductive hypothesis at width `k`.
    have ih_applied :=
      ih c' htape hhead
    -- Split on whether `c.head + k` is the LSB position (`k = 0`).
    by_cases hk0 : k = 0
    · subst hk0
      -- width-1 case: direct computation.
      simp only [counterValue_zero, Nat.zero_add]
      have hp : (c.head : ℕ) + 0 < M.tapeLength n := by
        have := c.head.isLt; omega
      have hmk : (⟨(c.head : ℕ) + 0, hp⟩ : Fin (M.tapeLength n)) = c.head := by
        apply Fin.ext; simp
      simp [dif_pos hp, hmk, htape, h_old,
            Configuration.write_self c c.head true]
    · -- `k ≥ 1`.  Use IH on the prefix; the last contribution at
      -- position `c.head + k` is unchanged because `c.head + k
      -- ≠ c.head` (since `k ≥ 1`).
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hne_kpos : (c.head : ℕ) + k ≠ (c.head : ℕ) := by omega
      have hne_fin_pos :
          ∀ (hi : (c.head : ℕ) + k < M.tapeLength n),
            (⟨(c.head : ℕ) + k, hi⟩ : Fin (M.tapeLength n)) ≠ c.head := by
        intro hi hfin_eq
        apply hne_kpos
        exact congrArg Fin.val hfin_eq
      -- IH rewrites the prefix; the `if (c.head < c.head + k)`
      -- branch is taken since `k ≥ 1`.
      have h_lt : (c.head : ℕ) < (c.head : ℕ) + k := by omega
      rw [ih_applied, if_pos h_lt]
      -- Now relate the added-bit terms at position `c.head + k`.
      have h_added_eq :
          (if hi : (c.head : ℕ) + k < M.tapeLength n then
            (if c'.tape ⟨(c.head : ℕ) + k, hi⟩ then 2 ^ k else 0)
          else 0) =
          (if hi : (c.head : ℕ) + k < M.tapeLength n then
            (if c.tape ⟨(c.head : ℕ) + k, hi⟩ then 2 ^ k else 0)
          else 0) := by
        by_cases hbound : (c.head : ℕ) + k < M.tapeLength n
        · simp only [dif_pos hbound]
          rw [htape,
              Configuration.write_other c (hne_fin_pos hbound) true]
        · simp only [dif_neg hbound]
      have h_lt' : (c.head : ℕ) < (c.head : ℕ) + (k + 1) := by omega
      rw [h_added_eq, if_pos h_lt']
      omega

/-!
### Session 7g (opening): ripple-invariant infrastructure

The general `incrementProgram_correct` theorem — handling any
starting bit pattern including the all-ones overflow — requires
tracking the ripple phase-by-phase.  The key lemma is the
**ripple invariant**: starting from phase 0 with the first `j`
bits all `1`, after `j` steps of `incrementProgram k`:

* state phase advances to `j`,
* head moves to `c.head + j`,
* the `j` cells at `[c.head, c.head + j)` are all flipped to `0`,
* all other cells are preserved.

Session 7g-a establishes the invariant for *one* ripple step —
the atomic engine that Session 7g-b will iterate inductively.
-/

/-- One ripple step: if we are in phase `j < k` at head position
`c.head = p + j`, bits `[p, p + j)` are all `0` (already
flipped), bit at head is `1`, and head-bound allows advancing,
then after `stepConfig` we are in phase `j + 1`, head `p + j + 1`,
and bits `[p, p + j + 1)` are all `0`. -/
theorem incrementProgram_ripple_step {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (j : Nat) (hj : j < k)
    (h_phase : c.state.fst.val = j)
    (h_bit : c.tape c.head = true)
    (h_head_bound : (c.head : ℕ) + 1 <
        (incrementProgram k).toTM.tapeLength n) :
    let c' := TM.stepConfig (M := (incrementProgram k).toTM) c
    (c'.state.fst.val = j + 1) ∧
    ((c'.head : ℕ) = (c.head : ℕ) + 1) ∧
    (c'.tape c.head = false) ∧
    (∀ (p : Fin ((incrementProgram k).toTM.tapeLength n)),
       p ≠ c.head → c'.tape p = c.tape p) := by
  have h_phase_lt : c.state.fst.val < k := by rw [h_phase]; exact hj
  obtain ⟨htape_step, hhead_step, hphase_step⟩ :=
    incrementProgram_stepConfig_phase_lt_k_bit_true c h_phase_lt h_bit h_head_bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hphase_step, h_phase]
  · exact hhead_step
  · rw [htape_step]
    exact Configuration.write_self c c.head false
  · intro p hne
    rw [htape_step]
    exact Configuration.write_other c hne false

/-!
### Session 7g-b: iterated ripple invariant

The single-step lemma `incrementProgram_ripple_step` is iterated `j`
times to obtain a full ripple invariant over `[0, j]`.  The
statement captures four simultaneous facts after `j` steps when
the first `j` bits at the counter start are all `1`:

1. `state.fst.val = j`,
2. `head.val = c.head + j`,
3. cells outside `[c.head, c.head + j)` are preserved,
4. cells at `[c.head, c.head + j)` are flipped to `false`.
-/

theorem incrementProgram_ripple_after_j_steps {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + k + 1 ≤
        (incrementProgram k).toTM.tapeLength n) :
    ∀ j, j ≤ k →
    (∀ (i : Nat), i < j →
       ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
       c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true) →
    ((TM.runConfig (M := (incrementProgram k).toTM) c j).state.fst.val = j) ∧
    (((TM.runConfig (M := (incrementProgram k).toTM) c j).head : ℕ) =
        (c.head : ℕ) + j) ∧
    (∀ (p : Fin ((incrementProgram k).toTM.tapeLength n)),
       ((p : ℕ) < (c.head : ℕ) ∨ (c.head : ℕ) + j ≤ (p : ℕ)) →
       (TM.runConfig (M := (incrementProgram k).toTM) c j).tape p = c.tape p) ∧
    (∀ (i : Nat), i < j →
       ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
       (TM.runConfig (M := (incrementProgram k).toTM) c j).tape
           ⟨(c.head : ℕ) + i, hbi⟩ = false) := by
  intro j hjk hones
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show (c.head : ℕ) = _; omega
    · intros; rfl
    · intros i h; exact absurd h (by omega)
  | succ j' ih =>
    have hj'_le_k : j' ≤ k := by omega
    have hj'_lt_k : j' < k := by omega
    have hones_prev : ∀ (i : Nat), i < j' →
        ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
        c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true := by
      intro i hi hbi; exact hones i (by omega) hbi
    obtain ⟨ihs_phase, ihs_head, ihs_preserve, ihs_zeros⟩ :=
      ih hj'_le_k hones_prev
    -- Set up `c_j` = runConfig c j'.
    set cj' := TM.runConfig (M := (incrementProgram k).toTM) c j' with hcj'
    -- Apply one more step via ripple_step.
    have h_phase_cj' : cj'.state.fst.val = j' := ihs_phase
    have h_head_cj' : (cj'.head : ℕ) = (c.head : ℕ) + j' := ihs_head
    -- Bit at cj'.head is true (from hones at i = j').
    have h_bit_bound : (c.head : ℕ) + j' < (incrementProgram k).toTM.tapeLength n :=
      by omega
    have h_bit_orig : c.tape ⟨(c.head : ℕ) + j', h_bit_bound⟩ = true :=
      hones j' (by omega) h_bit_bound
    -- cj'.head as a Fin equals ⟨c.head + j', _⟩.
    have h_head_fin_eq :
        cj'.head = (⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) := by
      apply Fin.ext; exact h_head_cj'
    -- Thus cj'.tape at its head is true (via preserve on outside region).
    have h_bit_cj' : cj'.tape cj'.head = true := by
      rw [h_head_fin_eq]
      have hout :
          ((⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) : ℕ) < (c.head : ℕ) ∨
          (c.head : ℕ) + j' ≤ ((⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) : ℕ) :=
        Or.inr (by omega)
      rw [ihs_preserve _ hout]; exact h_bit_orig
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (incrementProgram k).toTM.tapeLength n := by
      rw [h_head_cj']; omega
    obtain ⟨rip_phase, rip_head, rip_bit, rip_preserve⟩ :=
      incrementProgram_ripple_step cj' j' hj'_lt_k h_phase_cj'
        h_bit_cj' h_head_advance_bound
    -- Now (runConfig c (j'+1)) = stepConfig cj' by runConfig_succ.
    have hrw : TM.runConfig (M := (incrementProgram k).toTM) c (j' + 1) =
        TM.stepConfig (M := (incrementProgram k).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw]; exact rip_phase
    · rw [hrw, rip_head, h_head_cj']; omega
    · intro p hout
      rw [hrw]
      -- Outside region check: p is not cj'.head.
      have hne : p ≠ cj'.head := by
        rw [h_head_fin_eq]
        intro heq
        rcases hout with h1 | h2
        · exact absurd (show ((p : ℕ)) < (c.head : ℕ) from h1)
            (by rw [show (p : ℕ) = (c.head : ℕ) + j' from
                by rw [heq]]; omega)
        · exact absurd (show (c.head : ℕ) + (j' + 1) ≤ (p : ℕ) from h2)
            (by rw [show (p : ℕ) = (c.head : ℕ) + j' from
                by rw [heq]]; omega)
      rw [rip_preserve p hne]
      -- Apply IH's preservation.
      apply ihs_preserve
      rcases hout with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by omega)
    · intro i hi hbi
      rw [hrw]
      -- Case i = j' or i < j'.
      by_cases hij' : i = j'
      · -- i = j': after step, cell at c.head+j' = cj'.head was flipped to false.
        subst hij'
        have hpeq : (⟨(c.head : ℕ) + i, hbi⟩ : Fin _) = cj'.head := by
          apply Fin.ext
          show (c.head : ℕ) + i = _
          rw [h_head_cj']
        rw [hpeq]; exact rip_bit
      · -- i < j': unchanged by the extra step (since position ≠ cj'.head).
        have hij'_lt : i < j' := by omega
        have hne : (⟨(c.head : ℕ) + i, hbi⟩ : Fin _) ≠ cj'.head := by
          rw [h_head_fin_eq]
          intro heq
          apply hij'
          have : (c.head : ℕ) + i = (c.head : ℕ) + j' := congrArg Fin.val heq
          omega
        rw [rip_preserve _ hne]
        exact ihs_zeros i hij'_lt hbi

/-- First-bit-zero correctness for arbitrary `k ≥ 1`: when the
scanned cell is `0`, running `incrementProgram k` for its full
budget adds exactly `1` to the counter value (without mod
truncation, because the LSB was `0`, so the value was even and
`≤ 2^k - 2`). -/
theorem incrementProgram_correct_first_bit_zero {k : Nat} (hk : 0 < k)
    {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bit : c.tape c.head = false) :
    counterValue
        (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
        (c.head : ℕ) k =
      (counterValue c (c.head : ℕ) k + 1) % 2 ^ k := by
  -- Step 0: flips the head cell to `true`, enters accepting phase.
  have h_phase_lt : c.state.fst.val < k := by rw [h_phase]; exact hk
  obtain ⟨ht0, hh0, hp0⟩ :=
    incrementProgram_stepConfig_phase_lt_k_bit_false c h_phase_lt h_bit
  -- Steps 1..k: idle in accepting phase.
  set c0 := TM.stepConfig (M := (incrementProgram k).toTM) c with hc0_def
  -- `runConfig c (k+1) = runConfig c0 k` via `runConfig_add`.
  have h_rewrite :
      TM.runConfig (M := (incrementProgram k).toTM) c (k + 1) =
        TM.runConfig (M := (incrementProgram k).toTM) c0 k := by
    rw [show k + 1 = 1 + k from by omega, runConfig_add, runConfig_one]
  have h_phase_accept : c0.state.fst.val = k + 1 := by rw [hc0_def]; exact hp0
  obtain ⟨ht_final, hh_final, _⟩ :=
    incrementProgram_runConfig_in_accepting c0 h_phase_accept k
  -- Combine: the final tape equals `c.write c.head true`.
  have h_final_tape :
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).tape =
        c.write c.head true := by
    rw [h_rewrite, ht_final, hc0_def, ht0]
  have h_final_head :
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).head = c.head := by
    rw [h_rewrite, hh_final, hc0_def, hh0]
  -- Apply the bit-flip arithmetic lemma.
  have h_counter_new :
      counterValue
          (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
          (c.head : ℕ) k =
        counterValue c (c.head : ℕ) k + 1 := by
    have := counterValue_of_write_head_true c k h_bit
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
      h_final_tape h_final_head
    rw [this]
    have h_lt : (c.head : ℕ) < (c.head : ℕ) + k := by omega
    simp [h_lt]
  -- Prove the mod doesn't truncate:
  -- since `c.tape c.head = false`, the LSB contribution to
  -- `counterValue c start k` is 0, so the old value is bounded by
  -- `2^k - 2`, hence `old + 1 < 2^k`.
  have h_old_lt_pow : counterValue c (c.head : ℕ) k + 1 < 2 ^ k := by
    -- Use counterValue_lt_two_pow, plus the fact that the LSB (k ≥ 1)
    -- contributes 0, so the sum is strictly less than 2^k - 1.
    -- Concretely: counterValue c head k - (LSB_contribution) ≤ 2^k - 2.
    -- But this argument is subtle.  A simpler direct route:
    -- counterValue c head k < 2^k  →  since we can bound it away from
    -- the max by the 0-LSB observation.
    --
    -- For a clean proof we use: for k ≥ 1, at position `head + 0` the
    -- bit is `false`, contributing 0 to the sum.  All other terms
    -- together give ≤ `∑_{i=1}^{k-1} 2^i = 2^k - 2`.
    --
    -- We defer that tighter bound: instead, observe that
    -- counterValue c head k has bit-0 contribution 0, so it is even
    -- (or we note `counterValue (new) < 2^k` and conclude mod =
    -- counterValue (new)).
    have h_new_lt := counterValue_lt_two_pow
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
      (c.head : ℕ) k
    rw [h_counter_new] at h_new_lt
    exact h_new_lt
  rw [h_counter_new, Nat.mod_eq_of_lt h_old_lt_pow]

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

/-!
## Session 8: Bit-level encoding primitives

The MCSP verifier feeds circuit descriptions to its TM phases via
the witness tape.  Before tackling full circuit encoding, we fix a
general-purpose bit-level primitive: `Fin (2^w)` ↔ `List Bool` of
length `w`, in little-endian order (LSB first).

This primitive is independent of any MCSP-specific content and is
reusable for encoding gate indices, input positions, and any other
bounded-range index that the verifier needs to read off the tape.
-/

namespace Encoding

/-- Encode `i : Fin (2^w)` as a `w`-bit little-endian bit list
(LSB first). -/
def encodeFin : (w : Nat) → Fin (2 ^ w) → List Bool
  | 0, _ => []
  | w + 1, i =>
    let b := decide (i.val % 2 = 1)
    have hrest : i.val / 2 < 2 ^ w := by
      have hi_lt := i.isLt
      have heq : (2 : Nat) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
      apply (Nat.div_lt_iff_lt_mul (by omega : (0 : Nat) < 2)).mpr
      omega
    b :: encodeFin w ⟨i.val / 2, hrest⟩

/-- The encoded bit list always has length `w`. -/
theorem encodeFin_length : ∀ (w : Nat) (i : Fin (2 ^ w)),
    (encodeFin w i).length = w
  | 0, _ => by simp [encodeFin]
  | w + 1, i => by
    simp only [encodeFin, List.length_cons]
    rw [encodeFin_length w]

/-- Decode a bit list as a `Fin (2^w)` value (little-endian: head of
list = LSB).  Returns `none` if the list length mismatches `w`. -/
def decodeFin : (w : Nat) → List Bool → Option (Fin (2 ^ w))
  | 0, [] => some ⟨0, by simp⟩
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | w + 1, b :: bs =>
    match decodeFin w bs with
    | none => none
    | some r =>
      let v := (if b then 1 else 0) + 2 * r.val
      have hv : v < 2 ^ (w + 1) := by
        have hr := r.isLt
        have heq : (2 : Nat) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
        have hbit_le : (if b then 1 else 0 : Nat) ≤ 1 := by
          split_ifs <;> omega
        omega
      some ⟨v, hv⟩

/-- Round-trip: decoding the encoding recovers the original value. -/
theorem decodeFin_encodeFin : ∀ (w : Nat) (i : Fin (2 ^ w)),
    decodeFin w (encodeFin w i) = some i
  | 0, ⟨0, _⟩ => by
    simp [encodeFin, decodeFin]
  | 0, ⟨_ + 1, h⟩ => by
    simp at h
  | w + 1, i => by
    simp only [encodeFin, decodeFin]
    -- The recursive call at width `w` on the tail reconstructs
    -- `⟨i.val / 2, _⟩` by IH.
    rw [decodeFin_encodeFin w ⟨i.val / 2, _⟩]
    apply Option.some_inj.mpr
    apply Fin.ext
    have hdiv_mod : 2 * (i.val / 2) + i.val % 2 = i.val :=
      Nat.div_add_mod i.val 2
    have hmod_lt : i.val % 2 < 2 := Nat.mod_lt i.val (by omega)
    by_cases hmod : i.val % 2 = 1
    · simp [hmod]; omega
    · have hmod0 : i.val % 2 = 0 := by omega
      simp [hmod]; omega

/-!
### Session 8c: Circuit encoding via `CircuitTree`

The MCSP verifier needs to parse a circuit description off the
witness tape.  We define a local `CircuitTree n` inductive —
structurally identical to `Pnp3.Models.Circuit` — and a recursive
encoder into `List Bool` using the following prefix-free tag
scheme:

* `input i`  → `[false, false, false]` ++ `encodeFin width i`
* `const b`  → `[false, false, true, b]`
* `not c`    → `[false, true, false]` ++ `encode c`
* `and c1 c2`→ `[false, true, true]` ++ `encode c1` ++ `encode c2`
* `or c1 c2` → `[true, false, false]` ++ `encode c1` ++ `encode c2`

Keeping `CircuitTree` local to `Encoding` decouples the toolkit
from MCSP-specific imports; a bridge to `Models.Circuit` can be
supplied in a dedicated session when the MCSP assembly is wired up.

Session 8c delivers the inductive + the encoder + the `size`
measure.  Session 8d delivers the decoder and the round-trip
theorem.
-/

/-- Local mirror of `Pnp3.Models.Circuit`: a tree of AC0-style
Boolean gates over `n` input variables.  Kept separate so the
toolkit stays MCSP-import-free. -/
inductive CircuitTree (n : Nat) where
  | input : Fin n → CircuitTree n
  | const : Bool → CircuitTree n
  | not : CircuitTree n → CircuitTree n
  | and : CircuitTree n → CircuitTree n → CircuitTree n
  | or : CircuitTree n → CircuitTree n → CircuitTree n

namespace CircuitTree

/-- Number of gates in the tree — each node contributes 1. -/
def size {n : Nat} : CircuitTree n → Nat
  | input _ => 1
  | const _ => 1
  | not c => c.size + 1
  | and c1 c2 => c1.size + c2.size + 1
  | or c1 c2 => c1.size + c2.size + 1

end CircuitTree

/-- Prefix-order encoding of a `CircuitTree n` as a bit list,
assuming every `Fin n` index fits in `width` bits. -/
def encodeCircuitTree {n : Nat} (width : Nat)
    (h_width : n ≤ 2 ^ width) : CircuitTree n → List Bool
  | .input i =>
      [false, false, false] ++
        encodeFin width ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩
  | .const b => [false, false, true, b]
  | .not c =>
      [false, true, false] ++ encodeCircuitTree width h_width c
  | .and c1 c2 =>
      [false, true, true] ++
        encodeCircuitTree width h_width c1 ++
        encodeCircuitTree width h_width c2
  | .or c1 c2 =>
      [true, false, false] ++
        encodeCircuitTree width h_width c1 ++
        encodeCircuitTree width h_width c2

/-- Each gate contributes at least 3 tag bits, so the encoded list
has length at least the tree size × 3.  Lower bound — useful later
for showing that the encoded witness fits within the available
certificate room. -/
theorem encodeCircuitTree_length_ge {n : Nat} (width : Nat)
    (h_width : n ≤ 2 ^ width) : ∀ (c : CircuitTree n),
    3 * c.size ≤ (encodeCircuitTree width h_width c).length
  | .input _ => by
    simp [encodeCircuitTree, CircuitTree.size, encodeFin_length]
  | .const _ => by
    simp [encodeCircuitTree, CircuitTree.size]
  | .not c => by
    have ih := encodeCircuitTree_length_ge width h_width c
    simp [encodeCircuitTree, CircuitTree.size]
    omega
  | .and c1 c2 => by
    have ih1 := encodeCircuitTree_length_ge width h_width c1
    have ih2 := encodeCircuitTree_length_ge width h_width c2
    simp [encodeCircuitTree, CircuitTree.size]
    omega
  | .or c1 c2 => by
    have ih1 := encodeCircuitTree_length_ge width h_width c1
    have ih2 := encodeCircuitTree_length_ge width h_width c2
    simp [encodeCircuitTree, CircuitTree.size]
    omega

/-!
### Session 8d: Circuit decoder + round-trip

Structural recursion on a `depth` budget (rather than list length)
gives a clean well-founded definition: each recursive subcall
decrements `depth` by 1.  Passing `c.size` as the initial budget
is always enough since the tree depth is bounded by its size.

The round-trip theorem shows `decodeCircuitTreeAtDepth` (at depth
`c.size`) recovers `c` and leaves any tail unchanged:

  decodeCircuitTreeAtDepth (h_pos : 0 < n) width c.size
      (encodeCircuitTree width h_width c ++ rest)
    = some (c, rest).
-/

/-- Recursive decoder with a structural depth budget.  Returns the
parsed tree plus the remaining bit list, or `none` on malformed
input. -/
def decodeCircuitTreeAtDepth {n : Nat} (h_pos : 0 < n) (width : Nat) :
    Nat → List Bool → Option (CircuitTree n × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | _ + 1, [_, _] => none
  | _ + 1, false :: false :: false :: rest =>
    if hrest_len : rest.length < width then none
    else
      let payload := rest.take width
      let remainder := rest.drop width
      match decodeFin width payload with
      | none => none
      | some i_fin =>
        if hv : i_fin.val < n then
          some (CircuitTree.input ⟨i_fin.val, hv⟩, remainder)
        else none
  | _ + 1, false :: false :: true :: b :: rest =>
    some (CircuitTree.const b, rest)
  | d + 1, false :: true :: false :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c, remainder) => some (CircuitTree.not c, remainder)
  | d + 1, false :: true :: true :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c1, rest1) =>
      match decodeCircuitTreeAtDepth h_pos width d rest1 with
      | none => none
      | some (c2, rest2) => some (CircuitTree.and c1 c2, rest2)
  | d + 1, true :: false :: false :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c1, rest1) =>
      match decodeCircuitTreeAtDepth h_pos width d rest1 with
      | none => none
      | some (c2, rest2) => some (CircuitTree.or c1 c2, rest2)
  | _ + 1, _ :: _ :: _ :: _ => none

/-!
### Session 8e: Round-trip — per-constructor lemmas

The cleanest scalable proof splits into per-constructor lemmas
and a combining induction step.  Both the scalar `decodeFin`
round-trip and the `List.take`/`drop` facts line up cleanly at
the constructor level.

Session 8e delivers the `const` and `not` round-trip cases.  The
remaining three constructors (`input`, `and`, `or`) reuse the
same machinery; the `input` case additionally threads
`decodeFin_encodeFin` through the `take`/`drop` split.  Those
are reserved for Session 8f so the current commit keeps its
scope tight and its individual proofs readable.
-/

theorem decode_encode_const {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (b : Bool) (d : Nat) (hd : 1 ≤ d)
    (rest : List Bool) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.const b) ++ rest) =
      some (CircuitTree.const b, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp [encodeCircuitTree, decodeCircuitTreeAtDepth]

theorem decode_encode_not {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : CircuitTree n) (d : Nat)
    (hd : c.size + 1 ≤ d)
    (rest : List Bool)
    (ih : ∀ (d' : Nat), c.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c ++ r) = some (c, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.not c) ++ rest) =
      some (CircuitTree.not c, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd' : c.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             List.append_assoc, decodeCircuitTreeAtDepth]
  rw [ih d' hd' rest]

theorem decode_encode_and {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c1 c2 : CircuitTree n) (d : Nat)
    (hd : c1.size + c2.size + 1 ≤ d)
    (rest : List Bool)
    (ih1 : ∀ (d' : Nat), c1.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c1 ++ r) = some (c1, r))
    (ih2 : ∀ (d' : Nat), c2.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c2 ++ r) = some (c2, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.and c1 c2) ++ rest) =
      some (CircuitTree.and c1 c2, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd1 : c1.size ≤ d' := by omega
  have hd2 : c2.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             List.append_assoc, decodeCircuitTreeAtDepth,
             ih1 d' hd1 (encodeCircuitTree width h_width c2 ++ rest),
             ih2 d' hd2 rest]

theorem decode_encode_or {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c1 c2 : CircuitTree n) (d : Nat)
    (hd : c1.size + c2.size + 1 ≤ d)
    (rest : List Bool)
    (ih1 : ∀ (d' : Nat), c1.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c1 ++ r) = some (c1, r))
    (ih2 : ∀ (d' : Nat), c2.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c2 ++ r) = some (c2, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.or c1 c2) ++ rest) =
      some (CircuitTree.or c1 c2, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd1 : c1.size ≤ d' := by omega
  have hd2 : c2.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             List.append_assoc, decodeCircuitTreeAtDepth,
             ih1 d' hd1 (encodeCircuitTree width h_width c2 ++ rest),
             ih2 d' hd2 rest]

theorem decode_encode_input {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (i : Fin n) (d : Nat) (hd : 1 ≤ d)
    (rest : List Bool) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.input i) ++ rest) =
      some (CircuitTree.input i, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  set ifin : Fin (2 ^ width) := ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩ with hifin
  -- Helper facts about the input's take/drop split.
  have hlen_not :
      ¬ (encodeFin width ifin ++ rest).length < width := by
    rw [List.length_append, encodeFin_length]; omega
  have htake :
      (encodeFin width ifin ++ rest).take width = encodeFin width ifin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop :
      (encodeFin width ifin ++ rest).drop width = rest := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  have hvlt : ifin.val < n := by rw [hifin]; exact i.isLt
  -- Reduce the goal to the exposed decoder-match form.
  show decodeCircuitTreeAtDepth h_pos width (d' + 1)
      (false :: false :: false :: (encodeFin width ifin ++ rest)) =
    some (CircuitTree.input i, rest)
  unfold decodeCircuitTreeAtDepth
  rw [dif_neg hlen_not, htake, hdrop]
  -- Reduce the `have payload := encodeFin width ifin` binding.
  show (match decodeFin width (encodeFin width ifin) with
        | none => none
        | some i_fin =>
          if hv : i_fin.val < n then
            some (CircuitTree.input ⟨i_fin.val, hv⟩, rest)
          else none) = some (CircuitTree.input i, rest)
  rw [decodeFin_encodeFin]
  -- Reduce `match some ifin with ...` via iota.
  show (if hv : ifin.val < n then
          some (CircuitTree.input ⟨ifin.val, hv⟩, rest)
        else none) = some (CircuitTree.input i, rest)
  rw [dif_pos hvlt]

/-- Full round-trip: combines all five constructor-level lemmas
into a single induction on the circuit tree. -/
theorem decodeCircuitTreeAtDepth_encodeCircuitTree
    {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : CircuitTree n) :
    ∀ (d : Nat), c.size ≤ d →
    ∀ (rest : List Bool),
      decodeCircuitTreeAtDepth h_pos width d
          (encodeCircuitTree width h_width c ++ rest) = some (c, rest) := by
  induction c with
  | input i =>
    intro d h_d rest
    exact decode_encode_input h_pos width h_width i d
      (by simpa [CircuitTree.size] using h_d) rest
  | const b =>
    intro d h_d rest
    exact decode_encode_const h_pos width h_width b d
      (by simpa [CircuitTree.size] using h_d) rest
  | not c ih =>
    intro d h_d rest
    exact decode_encode_not h_pos width h_width c d
      (by simpa [CircuitTree.size] using h_d) rest ih
  | and c1 c2 ih1 ih2 =>
    intro d h_d rest
    exact decode_encode_and h_pos width h_width c1 c2 d
      (by simpa [CircuitTree.size] using h_d) rest ih1 ih2
  | or c1 c2 ih1 ih2 =>
    intro d h_d rest
    exact decode_encode_or h_pos width h_width c1 c2 d
      (by simpa [CircuitTree.size] using h_d) rest ih1 ih2

end Encoding

end TM

end PsubsetPpoly
end Internal
end Pnp3
