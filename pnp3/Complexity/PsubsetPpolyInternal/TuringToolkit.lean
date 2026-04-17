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
