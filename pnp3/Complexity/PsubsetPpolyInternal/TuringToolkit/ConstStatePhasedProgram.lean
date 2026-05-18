import Complexity.PsubsetPpolyInternal.TuringToolkit.Foundation

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM


/-! ## ConstStatePhasedProgram: uniform-state phased programs

A restricted form of `PhasedProgram` where every phase has the same
local control state type `S`.  This eliminates the dependent
`phaseState i` entirely, making sequential composition straightforward
(no cast juggling across heterogeneous phase-state families).

The MCSP verifier is expressed as a chain of `ConstStatePhasedProgram`
pieces with `S := Bool × Bool`, composed via `seq`.  Each piece is a
gate evaluator lifted from the underlying `combineAtOffsetProgram`. -/

namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v

/-- A phased program where all phases share a common state type `S`.
The `toPhased` conversion drops this into the general `PhasedProgram`
framework by setting `phaseState := fun _ => S`. -/
structure _root_.Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
    (S : Type v) [Fintype S] [DecidableEq S] where
  /-- Number of phases. -/
  numPhases : Nat
  /-- Initial phase index. -/
  startPhase : Fin numPhases
  /-- Initial local state. -/
  startState : S
  /-- Accepting phase index. -/
  acceptPhase : Fin numPhases
  /-- Accepting local state. -/
  acceptState : S
  /-- Transition: given current phase, local state, scanned bit, return
  next `(phase, state)`, written bit and head move. -/
  transition : Fin numPhases → S → Bool → Fin numPhases × S × Bool × Move
  /-- Runtime bound. -/
  timeBound : Nat → Nat

variable {S : Type v} [Fintype S] [DecidableEq S]

/-- Embed a `ConstStatePhasedProgram` into the general `PhasedProgram`
framework by taking `phaseState := fun _ => S`. -/
def toPhased (U : ConstStatePhasedProgram S) : PhasedProgram.{v} where
  numPhases := U.numPhases
  phaseState := fun _ => S
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := U.startPhase
  startState := U.startState
  acceptPhase := U.acceptPhase
  acceptState := U.acceptState
  transition := fun i q scan =>
    let r := U.transition i q scan
    (⟨r.fst, r.snd.fst⟩, r.snd.snd.fst, r.snd.snd.snd)
  timeBound := U.timeBound

@[simp] theorem toPhased_numPhases (U : ConstStatePhasedProgram S) :
    U.toPhased.numPhases = U.numPhases := rfl

@[simp] theorem toPhased_timeBound (U : ConstStatePhasedProgram S) (n : Nat) :
    U.toPhased.timeBound n = U.timeBound n := rfl

/-- Sequential composition of two uniform-state phased programs.

The composed program has phases `0..P1.numPhases + P2.numPhases - 1`.
Phases `0..P1.numPhases - 1` run `P1`'s transitions, with `P1.acceptPhase`
redirected to `P2.startPhase + P1.numPhases` (one free handoff step
consumed).  Phases `P1.numPhases..end` run `P2`'s transitions, shifted
by `P1.numPhases`. -/
def seq (P1 P2 : ConstStatePhasedProgram S) : ConstStatePhasedProgram S where
  numPhases := P1.numPhases + P2.numPhases
  startPhase := ⟨P1.startPhase.val, by
    have := P1.startPhase.isLt; omega⟩
  startState := P1.startState
  acceptPhase := ⟨P1.numPhases + P2.acceptPhase.val, by
    have := P2.acceptPhase.isLt; omega⟩
  acceptState := P2.acceptState
  transition := fun i q scan =>
    if h1 : i.val < P1.numPhases then
      let i1 : Fin P1.numPhases := ⟨i.val, h1⟩
      if i1.val = P1.acceptPhase.val then
        -- boundary: hand off to P2.startPhase (shifted) with P2.startState.
        (⟨P1.numPhases + P2.startPhase.val, by
            have := P2.startPhase.isLt; omega⟩,
         P2.startState, scan, Move.stay)
      else
        let r := P1.transition i1 q scan
        (⟨r.fst.val, by
            have := r.fst.isLt; omega⟩,
         r.snd.fst, r.snd.snd.fst, r.snd.snd.snd)
    else
      let i2 : Fin P2.numPhases := ⟨i.val - P1.numPhases, by
        have := i.isLt; omega⟩
      let r := P2.transition i2 q scan
      (⟨P1.numPhases + r.fst.val, by
          have := r.fst.isLt; omega⟩,
       r.snd.fst, r.snd.snd.fst, r.snd.snd.snd)
  timeBound := fun n => P1.timeBound n + P2.timeBound n + 1

@[simp] theorem seq_numPhases (P1 P2 : ConstStatePhasedProgram S) :
    (seq P1 P2).numPhases = P1.numPhases + P2.numPhases := rfl

@[simp] theorem seq_timeBound (P1 P2 : ConstStatePhasedProgram S) (n : Nat) :
    (seq P1 P2).timeBound n = P1.timeBound n + P2.timeBound n + 1 := rfl

@[simp] theorem seq_startPhase_val (P1 P2 : ConstStatePhasedProgram S) :
    ((seq P1 P2).startPhase : Nat) = P1.startPhase.val := rfl

@[simp] theorem seq_acceptPhase_val (P1 P2 : ConstStatePhasedProgram S) :
    ((seq P1 P2).acceptPhase : Nat) = P1.numPhases + P2.acceptPhase.val := rfl

/-- Phase of the `seq` transition in the P1 region (not at P1's accept
phase) equals P1's transition's phase. -/
theorem seq_transition_P1_normal_phase (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (hne : i.val ≠ P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).fst.val =
      (P1.transition ⟨i.val, h1⟩ q scan).fst.val := by
  unfold seq
  simp only [dif_pos h1, if_neg hne]

/-- Local state result of the `seq` transition in the P1 region (not at
accept) equals P1's. -/
theorem seq_transition_P1_normal_state (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (hne : i.val ≠ P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.fst =
      (P1.transition ⟨i.val, h1⟩ q scan).snd.fst := by
  unfold seq
  simp only [dif_pos h1, if_neg hne]

/-- Bit written by the `seq` transition in the P1 region (not at accept)
equals P1's. -/
theorem seq_transition_P1_normal_bit (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (hne : i.val ≠ P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.fst =
      (P1.transition ⟨i.val, h1⟩ q scan).snd.snd.fst := by
  unfold seq
  simp only [dif_pos h1, if_neg hne]

/-- Head-move of the `seq` transition in the P1 region (not at accept)
equals P1's. -/
theorem seq_transition_P1_normal_move (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (hne : i.val ≠ P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.snd =
      (P1.transition ⟨i.val, h1⟩ q scan).snd.snd.snd := by
  unfold seq
  simp only [dif_pos h1, if_neg hne]

/-- Transition phase at P1's accept boundary: hands off to P2.startPhase
(shifted by P1.numPhases). -/
theorem seq_transition_P1_accept_phase (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (heq : i.val = P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).fst.val =
      P1.numPhases + P2.startPhase.val := by
  unfold seq
  simp only [dif_pos h1, if_pos heq]

/-- State at P1's accept boundary: becomes P2.startState. -/
theorem seq_transition_P1_accept_state (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (heq : i.val = P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.fst = P2.startState := by
  unfold seq
  simp only [dif_pos h1, if_pos heq]

/-- Bit written at the P1-accept boundary equals the scanned bit (no
modification at handoff). -/
theorem seq_transition_P1_accept_bit (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (heq : i.val = P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.fst = scan := by
  unfold seq
  simp only [dif_pos h1, if_pos heq]

/-- Head-move at the P1-accept boundary is `Move.stay`. -/
theorem seq_transition_P1_accept_move (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h1 : i.val < P1.numPhases)
    (heq : i.val = P1.acceptPhase.val) (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.snd = Move.stay := by
  unfold seq
  simp only [dif_pos h1, if_pos heq]

/-- Phase of the `seq` transition in the P2 region equals P2's phase,
shifted up by `P1.numPhases`. -/
theorem seq_transition_P2_phase (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h2 : P1.numPhases ≤ i.val)
    (hi_lt : i.val - P1.numPhases < P2.numPhases)
    (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).fst.val =
      P1.numPhases + (P2.transition ⟨i.val - P1.numPhases, hi_lt⟩ q scan).fst.val := by
  unfold seq
  simp only [dif_neg (by omega : ¬ i.val < P1.numPhases)]

/-- State of the `seq` transition in the P2 region equals P2's state. -/
theorem seq_transition_P2_state (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h2 : P1.numPhases ≤ i.val)
    (hi_lt : i.val - P1.numPhases < P2.numPhases)
    (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.fst =
      (P2.transition ⟨i.val - P1.numPhases, hi_lt⟩ q scan).snd.fst := by
  unfold seq
  simp only [dif_neg (by omega : ¬ i.val < P1.numPhases)]

/-- Bit written by the `seq` transition in the P2 region equals P2's. -/
theorem seq_transition_P2_bit (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h2 : P1.numPhases ≤ i.val)
    (hi_lt : i.val - P1.numPhases < P2.numPhases)
    (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.fst =
      (P2.transition ⟨i.val - P1.numPhases, hi_lt⟩ q scan).snd.snd.fst := by
  unfold seq
  simp only [dif_neg (by omega : ¬ i.val < P1.numPhases)]

/-- Head-move of the `seq` transition in the P2 region equals P2's. -/
theorem seq_transition_P2_move (P1 P2 : ConstStatePhasedProgram S)
    {i : Fin (seq P1 P2).numPhases} (h2 : P1.numPhases ≤ i.val)
    (hi_lt : i.val - P1.numPhases < P2.numPhases)
    (q : S) (scan : Bool) :
    ((seq P1 P2).transition i q scan).snd.snd.snd =
      (P2.transition ⟨i.val - P1.numPhases, hi_lt⟩ q scan).snd.snd.snd := by
  unfold seq
  simp only [dif_neg (by omega : ¬ i.val < P1.numPhases)]

/-! ### Step lemmas: lift the transition lemmas through `TM.stepConfig`

The four component-level lemmas (phase / state / head / tape) are
proved per regime (P1-internal, P1-boundary, P2-internal). -/

/-- In the P1 region (not at accept), `stepConfig` of `seq` matches
P1's transition: phase `.fst.val` equals the P1-transition-derived
phase. -/
theorem stepConfig_seq_P1_normal_phase (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (hne : c.state.fst.val ≠ P1.acceptPhase.val) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.fst.val : Nat) =
      (P1.transition ⟨c.state.fst.val, h1⟩ c.state.snd (c.tape c.head)).fst.val := by
  rw [stepConfig_state]
  show ((((seq P1 P2).toPhased.toTM.step c.state (c.tape c.head)).fst).fst : Nat) = _
  show (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).fst.val : Nat) = _
  exact seq_transition_P1_normal_phase P1 P2 h1 hne c.state.snd (c.tape c.head)

theorem stepConfig_seq_P1_normal_state (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (hne : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.snd =
      (P1.transition ⟨c.state.fst.val, h1⟩ c.state.snd (c.tape c.head)).snd.fst := by
  have h := seq_transition_P1_normal_state P1 P2 h1 hne c.state.snd (c.tape c.head)
  show ((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.fst = _
  exact h

theorem stepConfig_seq_P1_normal_head (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (hne : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head =
      Configuration.moveHead (c := c)
        (P1.transition ⟨c.state.fst.val, h1⟩ c.state.snd (c.tape c.head)).snd.snd.snd := by
  rw [stepConfig_head]
  show Configuration.moveHead (c := c)
      ((((seq P1 P2).toPhased.toTM.step c.state (c.tape c.head)).snd.snd : Move)) = _
  show Configuration.moveHead (c := c)
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.snd) = _
  rw [seq_transition_P1_normal_move P1 P2 h1 hne c.state.snd (c.tape c.head)]

theorem stepConfig_seq_P1_normal_tape (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (hne : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape =
      c.write c.head
        (P1.transition ⟨c.state.fst.val, h1⟩ c.state.snd (c.tape c.head)).snd.snd.fst := by
  rw [stepConfig_tape]
  show c.write c.head
      ((((seq P1 P2).toPhased.toTM.step c.state (c.tape c.head)).snd.fst : Bool)) = _
  show c.write c.head
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.fst) = _
  rw [seq_transition_P1_normal_bit P1 P2 h1 hne c.state.snd (c.tape c.head)]

/-- At the P1-accept boundary: phase transitions to `P1.numPhases + P2.startPhase.val`. -/
theorem stepConfig_seq_P1_boundary_phase (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (heq : c.state.fst.val = P1.acceptPhase.val) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.fst.val : Nat) =
      P1.numPhases + P2.startPhase.val := by
  rw [stepConfig_state]
  show (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).fst.val : Nat) = _
  exact seq_transition_P1_accept_phase P1 P2 h1 heq c.state.snd (c.tape c.head)

/-- At the P1-accept boundary: state resets to `P2.startState`. -/
theorem stepConfig_seq_P1_boundary_state (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (heq : c.state.fst.val = P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.snd = P2.startState := by
  have h := seq_transition_P1_accept_state P1 P2 h1 heq c.state.snd (c.tape c.head)
  show ((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.fst = _
  exact h

/-- At the P1-accept boundary: head stays (no movement). -/
theorem stepConfig_seq_P1_boundary_head (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (heq : c.state.fst.val = P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head = c.head := by
  rw [stepConfig_head]
  show Configuration.moveHead (c := c)
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.snd) = _
  rw [seq_transition_P1_accept_move P1 P2 h1 heq c.state.snd (c.tape c.head)]
  rfl

/-- At the P1-accept boundary: tape is unchanged (boundary writes the
current scan bit back in place). -/
theorem stepConfig_seq_P1_boundary_tape (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h1 : c.state.fst.val < P1.numPhases)
    (heq : c.state.fst.val = P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape = c.tape := by
  rw [stepConfig_tape]
  show c.write c.head
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.fst) = _
  rw [seq_transition_P1_accept_bit P1 P2 h1 heq c.state.snd (c.tape c.head)]
  funext j
  unfold Configuration.write
  split_ifs with hj
  · rw [hj]
  · rfl

/-- In the P2 region: `stepConfig` matches P2's transition with phase
shifted by `P1.numPhases`. -/
theorem stepConfig_seq_P2_phase (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h2 : P1.numPhases ≤ c.state.fst.val)
    (hi_lt : c.state.fst.val - P1.numPhases < P2.numPhases) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.fst.val : Nat) =
      P1.numPhases +
        (P2.transition ⟨c.state.fst.val - P1.numPhases, hi_lt⟩
            c.state.snd (c.tape c.head)).fst.val := by
  rw [stepConfig_state]
  show (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).fst.val : Nat) = _
  exact seq_transition_P2_phase P1 P2 h2 hi_lt c.state.snd (c.tape c.head)

theorem stepConfig_seq_P2_state (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h2 : P1.numPhases ≤ c.state.fst.val)
    (hi_lt : c.state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state.snd =
      (P2.transition ⟨c.state.fst.val - P1.numPhases, hi_lt⟩
            c.state.snd (c.tape c.head)).snd.fst := by
  have h := seq_transition_P2_state P1 P2 h2 hi_lt c.state.snd (c.tape c.head)
  show ((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.fst = _
  exact h

theorem stepConfig_seq_P2_head (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h2 : P1.numPhases ≤ c.state.fst.val)
    (hi_lt : c.state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head =
      Configuration.moveHead (c := c)
        (P2.transition ⟨c.state.fst.val - P1.numPhases, hi_lt⟩
            c.state.snd (c.tape c.head)).snd.snd.snd := by
  rw [stepConfig_head]
  show Configuration.moveHead (c := c)
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.snd) = _
  rw [seq_transition_P2_move P1 P2 h2 hi_lt c.state.snd (c.tape c.head)]

theorem stepConfig_seq_P2_tape (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (h2 : P1.numPhases ≤ c.state.fst.val)
    (hi_lt : c.state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape =
      c.write c.head
        (P2.transition ⟨c.state.fst.val - P1.numPhases, hi_lt⟩
            c.state.snd (c.tape c.head)).snd.snd.fst := by
  rw [stepConfig_tape]
  show c.write c.head
      (((seq P1 P2).transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.fst) = _
  rw [seq_transition_P2_bit P1 P2 h2 hi_lt c.state.snd (c.tape c.head)]

/-! ### `runConfig_succ` + stepConfig composition: derived one-step
lemmas phrased as rewrites of `runConfig c (t+1)` via the current
config at step `t`.

These are used by downstream induction proofs (for the circuit
evaluator and MCSP verifier) to avoid manual unfolding of
`runConfig_succ` each step. -/

theorem runConfig_seq_succ_P1_normal_phase (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h1 : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val < P1.numPhases)
    (hne : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val ≠ P1.acceptPhase.val) :
    ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.fst.val : Nat) =
      (P1.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val, h1⟩
          (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
          ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).fst.val := by
  rw [runConfig_succ]
  exact stepConfig_seq_P1_normal_phase P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 hne

theorem runConfig_seq_succ_P1_normal_state (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h1 : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val < P1.numPhases)
    (hne : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val ≠ P1.acceptPhase.val) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.snd =
      (P1.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val, h1⟩
          (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
          ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.fst := by
  rw [runConfig_succ]
  exact stepConfig_seq_P1_normal_state P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 hne

theorem runConfig_seq_succ_P1_normal_head (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h1 : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val < P1.numPhases)
    (hne : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val ≠ P1.acceptPhase.val) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).head =
      Configuration.moveHead (c := TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t)
        (P1.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val, h1⟩
            (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
            ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.snd.snd := by
  rw [runConfig_succ]
  exact stepConfig_seq_P1_normal_head P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 hne

theorem runConfig_seq_succ_P1_normal_tape (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h1 : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val < P1.numPhases)
    (hne : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val ≠ P1.acceptPhase.val) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).tape =
      (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).write (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head
        (P1.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val, h1⟩
            (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
            ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.snd.fst := by
  rw [runConfig_succ]
  exact stepConfig_seq_P1_normal_tape P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 hne

/-- Single boundary handoff step: after the step, phase is shifted to
`P1.numPhases + P2.startPhase.val`, state becomes `P2.startState`,
head and tape are unchanged. -/
theorem runConfig_seq_succ_P1_boundary (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h1 : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val < P1.numPhases)
    (heq : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val = P1.acceptPhase.val) :
    ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.fst.val : Nat) =
        P1.numPhases + P2.startPhase.val ∧
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.snd = P2.startState ∧
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).head = (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head ∧
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).tape = (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [runConfig_succ]
  · exact stepConfig_seq_P1_boundary_phase P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 heq
  · exact stepConfig_seq_P1_boundary_state P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 heq
  · exact stepConfig_seq_P1_boundary_head P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 heq
  · exact stepConfig_seq_P1_boundary_tape P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h1 heq

theorem runConfig_seq_succ_P2_phase (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h2 : P1.numPhases ≤ (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val)
    (hi_lt : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases < P2.numPhases) :
    ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.fst.val : Nat) =
      P1.numPhases +
        (P2.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases, hi_lt⟩
            (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
            ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).fst.val := by
  rw [runConfig_succ]
  exact stepConfig_seq_P2_phase P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h2 hi_lt

theorem runConfig_seq_succ_P2_state (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h2 : P1.numPhases ≤ (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val)
    (hi_lt : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).state.snd =
      (P2.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases, hi_lt⟩
          (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
          ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.fst := by
  rw [runConfig_succ]
  exact stepConfig_seq_P2_state P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h2 hi_lt

theorem runConfig_seq_succ_P2_head (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h2 : P1.numPhases ≤ (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val)
    (hi_lt : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).head =
      Configuration.moveHead (c := TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t)
        (P2.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases, hi_lt⟩
            (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
            ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.snd.snd := by
  rw [runConfig_succ]
  exact stepConfig_seq_P2_head P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h2 hi_lt

theorem runConfig_seq_succ_P2_tape (P1 P2 : ConstStatePhasedProgram S)
    {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (t : Nat)
    (h2 : P1.numPhases ≤ (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val)
    (hi_lt : (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases < P2.numPhases) :
    (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c (t + 1)).tape =
      (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).write (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head
        (P2.transition ⟨(TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.fst.val - P1.numPhases, hi_lt⟩
            (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).state.snd
            ((TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).tape (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t).head)).snd.snd.fst := by
  rw [runConfig_succ]
  exact stepConfig_seq_P2_tape P1 P2 (TM.runConfig (M := (seq P1 P2).toPhased.toTM) c t) h2 hi_lt

/-! ### Trivial identity program + list-composition

`idleCS` is a single-phase program that accepts in zero steps (starts
at the accept phase).  It acts as the identity element of `seq` up to
the one-step handoff that `seq` always inserts.

`seqList` folds a list of `ConstStatePhasedProgram` via `seq`.  When
the list is empty it returns `idleCS`; otherwise it chains elements
right-associatively. -/

section IdleSeqList
variable [Inhabited S]

def idleCS : ConstStatePhasedProgram S where
  numPhases := 1
  startPhase := ⟨0, Nat.zero_lt_one⟩
  startState := default
  acceptPhase := ⟨0, Nat.zero_lt_one⟩
  acceptState := default
  transition := fun i q scan => (i, q, scan, Move.stay)
  timeBound := fun _ => 0

@[simp] theorem idleCS_numPhases : (idleCS (S := S)).numPhases = 1 := rfl

@[simp] theorem idleCS_timeBound (n : Nat) :
    (idleCS (S := S)).timeBound n = 0 := rfl

/-- Compose a list of uniform-state phased programs sequentially.  The
result's numPhases is the sum, and its timeBound is the sum of
component timeBounds plus one handoff per composition. -/
def seqList : List (ConstStatePhasedProgram S) → ConstStatePhasedProgram S
  | [] => idleCS
  | p :: rest => seq p (seqList rest)

@[simp] theorem seqList_nil :
    (seqList (S := S) []) = idleCS := rfl

@[simp] theorem seqList_cons (p : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) :
    seqList (p :: rest) = seq p (seqList rest) := rfl

/-- Total `timeBound` of `seqList ps` satisfies the recurrence
`seqList_timeBound_cons`; explicit closed form left as downstream exercise. -/
theorem seqList_timeBound_nil (n : Nat) :
    (seqList (S := S) []).timeBound n = 0 := rfl

theorem seqList_timeBound_cons (p : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) (n : Nat) :
    (seqList (p :: rest)).timeBound n = p.timeBound n + (seqList rest).timeBound n + 1 := rfl

theorem seqList_numPhases_nil :
    (seqList (S := S) []).numPhases = 1 := rfl

theorem seqList_numPhases_cons (p : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) :
    (seqList (p :: rest)).numPhases = p.numPhases + (seqList rest).numPhases := rfl

/-! ### `seqList_run` leaf lemmas (Session 1 of TMVerifier plan)

These leaf lemmas anchor the multi-session `seqList_run_full` chain
documented in `pnp3/Docs/TMVerifier_Session_Plan.md`.  The nil case
is `rfl` modulo `seqList_timeBound_nil`.
-/

/-- For the empty seqList (which compiles to `idleCS`), running for the
declared `timeBound n = 0` steps is the identity.  This is the base case
of the eventual `seqList_run_full` induction. -/
theorem seqList_run_nil {n : Nat}
    (c : Configuration (M := (seqList (S := S) []).toPhased.toTM) n) :
    TM.runConfig (M := (seqList (S := S) []).toPhased.toTM) c
        ((seqList (S := S) []).timeBound n) = c := by
  rw [seqList_timeBound_nil]
  rfl

/-- For a cons seqList, the full run decomposes into "run `p` for its
own timeBound" followed by "run the remaining tail for `(seqList rest).timeBound + 1`
steps".  This is the recursive backbone of the eventual `seqList_run_full`
induction. -/
theorem seqList_run_decomp (p : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) {n : Nat}
    (c : Configuration (M := (seqList (p :: rest)).toPhased.toTM) n) :
    TM.runConfig (M := (seqList (p :: rest)).toPhased.toTM) c
        ((seqList (p :: rest)).timeBound n) =
      TM.runConfig (M := (seqList (p :: rest)).toPhased.toTM)
        (TM.runConfig (M := (seqList (p :: rest)).toPhased.toTM) c (p.timeBound n))
        ((seqList rest).timeBound n + 1) := by
  rw [seqList_timeBound_cons]
  -- Rewrite `(p.tb + (seqList rest).tb + 1) = p.tb + ((seqList rest).tb + 1)` via assoc
  have hassoc : p.timeBound n + (seqList rest).timeBound n + 1 =
      p.timeBound n + ((seqList rest).timeBound n + 1) := by omega
  rw [hassoc, runConfig_add]

/-- Singleton seqList: `seqList [p]` is `seq p idleCS`.  Its `timeBound` is
`p.timeBound + 1` (one handoff step after `p`'s work). -/
theorem seqList_timeBound_singleton (p : ConstStatePhasedProgram S) (n : Nat) :
    (seqList [p]).timeBound n = p.timeBound n + 1 := by
  rw [seqList_timeBound_cons, seqList_timeBound_nil]

/-- Singleton seqList run: `runConfig c (p.tb + 1) = runConfig (runConfig c p.tb) 1`. -/
theorem seqList_run_singleton (p : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seqList [p]).toPhased.toTM) n) :
    TM.runConfig (M := (seqList [p]).toPhased.toTM) c ((seqList [p]).timeBound n) =
      TM.runConfig (M := (seqList [p]).toPhased.toTM)
        (TM.runConfig (M := (seqList [p]).toPhased.toTM) c (p.timeBound n)) 1 := by
  rw [seqList_run_decomp p [] c, seqList_timeBound_nil]

/-- Number of phases in `seqList [p]`: just `p.numPhases + 1` (idleCS contributes 1). -/
theorem seqList_numPhases_singleton (p : ConstStatePhasedProgram S) :
    (seqList [p]).numPhases = p.numPhases + 1 := by
  rw [seqList_numPhases_cons, seqList_numPhases_nil]

/-- Total timeBound for a 2-element seqList. -/
theorem seqList_timeBound_two (p1 p2 : ConstStatePhasedProgram S) (n : Nat) :
    (seqList [p1, p2]).timeBound n = p1.timeBound n + p2.timeBound n + 2 := by
  rw [seqList_timeBound_cons, seqList_timeBound_cons, seqList_timeBound_nil]
  omega

/-- Decomposed run for a 2-element seqList: peel off `p1.timeBound` first,
then run the remaining `p2.timeBound + 2` steps. -/
theorem seqList_run_two (p1 p2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seqList [p1, p2]).toPhased.toTM) n) :
    TM.runConfig (M := (seqList [p1, p2]).toPhased.toTM) c
        ((seqList [p1, p2]).timeBound n) =
      TM.runConfig (M := (seqList [p1, p2]).toPhased.toTM)
        (TM.runConfig (M := (seqList [p1, p2]).toPhased.toTM) c (p1.timeBound n))
        (p2.timeBound n + 2) := by
  rw [seqList_run_decomp p1 [p2] c, seqList_timeBound_singleton]

/-- Total timeBound for a 3-element seqList. -/
theorem seqList_timeBound_three (p1 p2 p3 : ConstStatePhasedProgram S) (n : Nat) :
    (seqList [p1, p2, p3]).timeBound n =
      p1.timeBound n + p2.timeBound n + p3.timeBound n + 3 := by
  rw [seqList_timeBound_cons, seqList_timeBound_two]
  omega

/-- Decomposed run for a 3-element seqList: peel off `p1.timeBound`,
then run the remaining `p2.timeBound + p3.timeBound + 3` steps. -/
theorem seqList_run_three (p1 p2 p3 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seqList [p1, p2, p3]).toPhased.toTM) n) :
    TM.runConfig (M := (seqList [p1, p2, p3]).toPhased.toTM) c
        ((seqList [p1, p2, p3]).timeBound n) =
      TM.runConfig (M := (seqList [p1, p2, p3]).toPhased.toTM)
        (TM.runConfig (M := (seqList [p1, p2, p3]).toPhased.toTM) c
          (p1.timeBound n))
        (p2.timeBound n + p3.timeBound n + 3) := by
  rw [seqList_run_decomp p1 [p2, p3] c, seqList_timeBound_two]

/-- Total timeBound for a 4-element seqList. -/
theorem seqList_timeBound_four
    (p1 p2 p3 p4 : ConstStatePhasedProgram S) (n : Nat) :
    (seqList [p1, p2, p3, p4]).timeBound n =
      p1.timeBound n + p2.timeBound n + p3.timeBound n + p4.timeBound n + 4 := by
  rw [seqList_timeBound_cons, seqList_timeBound_three]
  omega

/-- Decomposed run for a 4-element seqList. -/
theorem seqList_run_four
    (p1 p2 p3 p4 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seqList [p1, p2, p3, p4]).toPhased.toTM) n) :
    TM.runConfig (M := (seqList [p1, p2, p3, p4]).toPhased.toTM) c
        ((seqList [p1, p2, p3, p4]).timeBound n) =
      TM.runConfig (M := (seqList [p1, p2, p3, p4]).toPhased.toTM)
        (TM.runConfig (M := (seqList [p1, p2, p3, p4]).toPhased.toTM) c
          (p1.timeBound n))
        (p2.timeBound n + p3.timeBound n + p4.timeBound n + 4) := by
  rw [seqList_run_decomp p1 [p2, p3, p4] c, seqList_timeBound_three]

/-- Total timeBound for a 5-element seqList (covers the canonical
5-phase verifier composition). -/
theorem seqList_timeBound_five
    (p1 p2 p3 p4 p5 : ConstStatePhasedProgram S) (n : Nat) :
    (seqList [p1, p2, p3, p4, p5]).timeBound n =
      p1.timeBound n + p2.timeBound n + p3.timeBound n +
        p4.timeBound n + p5.timeBound n + 5 := by
  rw [seqList_timeBound_cons, seqList_timeBound_four]
  omega

/-- Decomposed run for a 5-element seqList (covers the canonical
5-phase verifier composition). -/
theorem seqList_run_five
    (p1 p2 p3 p4 p5 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seqList [p1, p2, p3, p4, p5]).toPhased.toTM) n) :
    TM.runConfig (M := (seqList [p1, p2, p3, p4, p5]).toPhased.toTM) c
        ((seqList [p1, p2, p3, p4, p5]).timeBound n) =
      TM.runConfig (M := (seqList [p1, p2, p3, p4, p5]).toPhased.toTM)
        (TM.runConfig (M := (seqList [p1, p2, p3, p4, p5]).toPhased.toTM) c
          (p1.timeBound n))
        (p2.timeBound n + p3.timeBound n + p4.timeBound n +
          p5.timeBound n + 5) := by
  rw [seqList_run_decomp p1 [p2, p3, p4, p5] c, seqList_timeBound_four]

end IdleSeqList

/-! ### Embedding from P1's TM into the composed `seq P1 P2` TM

For a P1-configuration `c`, `embedSeqConfig P1 P2 c` produces the
corresponding configuration of `(seq P1 P2).toPhased.toTM`:
- Phase index is embedded via `Fin.castLE` (P1.numPhases ≤ P1+P2).
- Head is embedded via `Fin.castLE` (P1.tapeLength ≤ seq.tapeLength).
- Tape is extended with `false` padding at positions outside P1's range.

Useful for transporting P1's correctness theorems to the composed TM
during the prefix where the composed TM's phase is in P1's range. -/

theorem seq_tapeLength_ge_P1 (P1 P2 : ConstStatePhasedProgram S) (n : Nat) :
    P1.toPhased.toTM.tapeLength n ≤ (seq P1 P2).toPhased.toTM.tapeLength n := by
  show n + P1.timeBound n + 1 ≤ n + (P1.timeBound n + P2.timeBound n + 1) + 1
  omega

def embedSeqConfig (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    Configuration (M := (seq P1 P2).toPhased.toTM) n where
  state := ⟨⟨c.state.fst.val, by
      have h1 := c.state.fst.isLt
      -- `P1.toPhased.numPhases = P1.numPhases` by toPhased_numPhases
      simp only [toPhased_numPhases] at h1
      show c.state.fst.val < (seq P1 P2).numPhases
      rw [seq_numPhases]
      omega⟩,
    c.state.snd⟩
  head := ⟨c.head.val, by
    have := c.head.isLt
    have := seq_tapeLength_ge_P1 P1 P2 n
    omega⟩
  tape := fun i =>
    if h : i.val < P1.toPhased.toTM.tapeLength n then
      c.tape ⟨i.val, h⟩
    else
      false

@[simp] theorem embedSeqConfig_state_fst_val (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    ((embedSeqConfig P1 P2 c).state.fst : Nat) = c.state.fst.val := rfl

@[simp] theorem embedSeqConfig_state_snd (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    (embedSeqConfig P1 P2 c).state.snd = c.state.snd := rfl

@[simp] theorem embedSeqConfig_head_val (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    ((embedSeqConfig P1 P2 c).head : Nat) = c.head.val := rfl

/-- Tape at a position within P1's tape range is unchanged by embedding. -/
theorem embedSeqConfig_tape_in_range (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h : i.val < P1.toPhased.toTM.tapeLength n) :
    (embedSeqConfig P1 P2 c).tape i = c.tape ⟨i.val, h⟩ := by
  show (if h' : i.val < P1.toPhased.toTM.tapeLength n then _ else _) = _
  rw [dif_pos h]

/-- Tape outside P1's range (padding region) is `false`. -/
theorem embedSeqConfig_tape_out_of_range (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h : P1.toPhased.toTM.tapeLength n ≤ i.val) :
    (embedSeqConfig P1 P2 c).tape i = false := by
  show (if h' : i.val < P1.toPhased.toTM.tapeLength n then _ else _) = _
  rw [dif_neg (by omega)]

/-! ### Projection composite → P1

Inverse of `embedSeqConfig` (without the inverse identity).  The
`projectSeqP1` projection of a composite-config `c` with phase in P1
range and head in P1 range gives a P1-config whose state/head/tape
pointwise agree with `c`'s pre-image.  The identity
`embedSeqConfig P1 P2 (projectSeqP1 c) = c` under a tape-outer-zero
premise is the cornerstone for future F.4 composite-to-P1 transport;
its proof is deferred pending a clean handling of the
`Configuration`/`Sigma` dependent-type decomposition (the naïve
`congr` chain overshoots).  The projection definition alone is
useful downstream for local reasoning. -/

/-- Projection of a composite-config into a P1-config, under the
assumptions `c.state.fst.val < P1.numPhases` and `c.head.val <
P1.tapeLength`.  Tape is restricted to the first `P1.tapeLength` cells. -/
def projectSeqP1 (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (hphase : c.state.fst.val < P1.numPhases)
    (hhead : c.head.val < P1.toPhased.toTM.tapeLength n) :
    Configuration (M := P1.toPhased.toTM) n where
  state := ⟨⟨c.state.fst.val, by
      simp only [toPhased_numPhases]; exact hphase⟩, c.state.snd⟩
  head := ⟨c.head.val, hhead⟩
  tape := fun i =>
    c.tape ⟨i.val, Nat.lt_of_lt_of_le i.isLt (seq_tapeLength_ge_P1 P1 P2 n)⟩

/-- Identity lemma: `embed ∘ project = id` under the assumption that
`c`'s tape outside `P1.tapeLength` is all `false`.  Proved by
structural case analysis on the `Configuration.mk` constructor on both
sides, following the pattern of `embedSeqConfig_stepConfig_eq`. -/
theorem embedSeqConfig_projectSeqP1 (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) n)
    (hphase : c.state.fst.val < P1.numPhases)
    (hhead : c.head.val < P1.toPhased.toTM.tapeLength n)
    (htape_outer : ∀ i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n),
      P1.toPhased.toTM.tapeLength n ≤ i.val → c.tape i = false) :
    embedSeqConfig P1 P2 (projectSeqP1 P1 P2 c hphase hhead) = c := by
  -- Component 1: state equality. Sigma with same .val (Fin.ext) and same .snd.
  have hstate :
      (embedSeqConfig P1 P2 (projectSeqP1 P1 P2 c hphase hhead)).state = c.state := by
    have hfst : (embedSeqConfig P1 P2
        (projectSeqP1 P1 P2 c hphase hhead)).state.fst = c.state.fst :=
      Fin.ext rfl
    have hsnd : (embedSeqConfig P1 P2
        (projectSeqP1 P1 P2 c hphase hhead)).state.snd = c.state.snd := rfl
    exact Sigma.ext hfst (by rw [hfst]; exact heq_of_eq hsnd)
  -- Component 2: head equality via Fin.ext.
  have hhead_eq :
      (embedSeqConfig P1 P2 (projectSeqP1 P1 P2 c hphase hhead)).head = c.head :=
    Fin.ext rfl
  -- Component 3: tape equality via funext + dif case split.
  have htape_eq :
      (embedSeqConfig P1 P2 (projectSeqP1 P1 P2 c hphase hhead)).tape = c.tape := by
    funext i
    by_cases h : i.val < P1.toPhased.toTM.tapeLength n
    · show (if h' : i.val < P1.toPhased.toTM.tapeLength n
          then _ else false) = _
      rw [dif_pos h]
      rfl
    · show (if h' : i.val < P1.toPhased.toTM.tapeLength n
          then _ else false) = _
      rw [dif_neg h]
      exact (htape_outer i (Nat.not_lt.mp h)).symm
  -- Combine via Configuration case analysis.
  cases hL : (embedSeqConfig P1 P2 (projectSeqP1 P1 P2 c hphase hhead)) with
  | mk sL hL_head tL =>
    cases hR : c with
    | mk sR hR_head tR =>
      have hse : sL = sR := by
        rw [hL] at hstate; rw [hR] at hstate; exact hstate
      have hte : tL = tR := by
        rw [hL] at htape_eq; rw [hR] at htape_eq; exact htape_eq
      have hhe : hL_head = hR_head := by
        rw [hL] at hhead_eq; rw [hR] at hhead_eq; exact hhead_eq
      subst hse
      subst hte
      subst hhe
      rfl

/-- Tape value at head position is preserved by embedding: reading at
the embedded head returns the same bit as reading at the original head. -/
@[simp] theorem embedSeqConfig_tape_at_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    (embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head = c.tape c.head := by
  have h : (embedSeqConfig P1 P2 c).head.val < P1.toPhased.toTM.tapeLength n := by
    simp only [embedSeqConfig_head_val]; exact c.head.isLt
  rw [embedSeqConfig_tape_in_range P1 P2 c (embedSeqConfig P1 P2 c).head h]
  congr 1

/-- Phase after one step of the composed seq TM on `embedSeqConfig c`
equals the phase after one step of P1 alone on `c`, when the current
phase is in P1's range and not at accept. -/
theorem embedSeqConfig_stepConfig_state_fst_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).state.fst.val : Nat) =
      ((TM.stepConfig (M := P1.toPhased.toTM) c).state.fst.val : Nat) := by
  have hne : (embedSeqConfig P1 P2 c).state.fst.val ≠ P1.acceptPhase.val := h_not_accept
  have hlt : (embedSeqConfig P1 P2 c).state.fst.val < P1.numPhases := h_phase
  rw [stepConfig_state, stepConfig_state]
  show (((seq P1 P2).transition (embedSeqConfig P1 P2 c).state.fst
          (embedSeqConfig P1 P2 c).state.snd
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).fst.val : Nat) =
       ((P1.transition c.state.fst c.state.snd (c.tape c.head)).fst.val : Nat)
  rw [embedSeqConfig_tape_at_head]
  rw [seq_transition_P1_normal_phase P1 P2 hlt hne
    (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)]
  rfl

/-- State `.snd` after one step of seq TM on `embedSeqConfig c` equals
that after one step of P1 alone, under P1-normal-not-accept conditions. -/
theorem embedSeqConfig_stepConfig_state_snd
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).state.snd =
      (TM.stepConfig (M := P1.toPhased.toTM) c).state.snd := by
  have hne : (embedSeqConfig P1 P2 c).state.fst.val ≠ P1.acceptPhase.val := h_not_accept
  have hlt : (embedSeqConfig P1 P2 c).state.fst.val < P1.numPhases := h_phase
  rw [stepConfig_state, stepConfig_state]
  show ((seq P1 P2).transition (embedSeqConfig P1 P2 c).state.fst
          (embedSeqConfig P1 P2 c).state.snd
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).snd.fst =
       (P1.transition c.state.fst c.state.snd (c.tape c.head)).snd.fst
  rw [embedSeqConfig_tape_at_head]
  rw [seq_transition_P1_normal_state P1 P2 hlt hne
    (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)]
  rfl

/-- Head value after Move.stay on embedded config equals original. -/
theorem embedSeqConfig_moveHead_stay (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    ((Configuration.moveHead (c := embedSeqConfig P1 P2 c) Move.stay : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.stay : Nat) := rfl

/-- Head value after Move.left on embedded config equals original (both
clamp at 0 identically). -/
theorem embedSeqConfig_moveHead_left (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) :
    ((Configuration.moveHead (c := embedSeqConfig P1 P2 c) Move.left : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.left : Nat) := by
  show (if _ : (embedSeqConfig P1 P2 c).head.val = 0 then _ else _ : Fin _).val =
       (if _ : c.head.val = 0 then _ else _ : Fin _).val
  simp only [embedSeqConfig_head_val]
  split_ifs with h
  · simp [embedSeqConfig_head_val, h]
  · rfl

/-- Head value after Move.right on embedded config equals original, when
the head is safely within P1's tape range (head + 1 < P1.tapeLength).
Under this safety hypothesis, neither P1 nor seq clamps. -/
theorem embedSeqConfig_moveHead_right_safe (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_safe : c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    ((Configuration.moveHead (c := embedSeqConfig P1 P2 c) Move.right : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.right : Nat) := by
  have h_safe_seq : (embedSeqConfig P1 P2 c).head.val + 1 <
      (seq P1 P2).toPhased.toTM.tapeLength n := by
    simp only [embedSeqConfig_head_val]
    have := seq_tapeLength_ge_P1 P1 P2 n
    omega
  show (if _ : (embedSeqConfig P1 P2 c).head.val + 1 <
          (seq P1 P2).toPhased.toTM.tapeLength n then _ else _ : Fin _).val =
       (if _ : c.head.val + 1 < P1.toPhased.toTM.tapeLength n then _ else _ : Fin _).val
  rw [dif_pos h_safe_seq, dif_pos h_safe]
  simp [embedSeqConfig_head_val]

/-- Unified head commutation: under a safety hypothesis (non-vacuous
only for Move.right), moveHead commutes with embedSeqConfig. -/
theorem embedSeqConfig_moveHead_val_commutes (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n) (m : Move)
    (h_safe : m = Move.right → c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    ((Configuration.moveHead (c := embedSeqConfig P1 P2 c) m : Fin _) : Nat) =
      (Configuration.moveHead (c := c) m : Nat) := by
  cases m with
  | stay => exact embedSeqConfig_moveHead_stay P1 P2 c
  | left => exact embedSeqConfig_moveHead_left P1 P2 c
  | right => exact embedSeqConfig_moveHead_right_safe P1 P2 c (h_safe rfl)

/-- Bit written by the composed seq's transition on an embedded P1
configuration equals the bit written by P1's transition, under
P1-normal-not-accept conditions. -/
theorem embedSeqConfig_stepConfig_written_bit
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    (((seq P1 P2).toPhased.toTM.step (embedSeqConfig P1 P2 c).state
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).snd.fst : Bool) =
      ((P1.toPhased.toTM.step c.state (c.tape c.head)).snd.fst : Bool) := by
  have hne : (embedSeqConfig P1 P2 c).state.fst.val ≠ P1.acceptPhase.val := h_not_accept
  have hlt : (embedSeqConfig P1 P2 c).state.fst.val < P1.numPhases := h_phase
  rw [embedSeqConfig_tape_at_head]
  show ((seq P1 P2).transition (embedSeqConfig P1 P2 c).state.fst
          (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)).snd.snd.fst =
       (P1.transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.fst
  rw [seq_transition_P1_normal_bit P1 P2 hlt hne
    (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)]
  rfl

/-- Move direction returned by the composed seq's transition on an
embedded P1 configuration equals that returned by P1's transition,
under P1-normal-not-accept conditions. -/
theorem embedSeqConfig_stepConfig_move
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    (((seq P1 P2).toPhased.toTM.step (embedSeqConfig P1 P2 c).state
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).snd.snd : Move) =
      ((P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd : Move) := by
  have hne : (embedSeqConfig P1 P2 c).state.fst.val ≠ P1.acceptPhase.val := h_not_accept
  have hlt : (embedSeqConfig P1 P2 c).state.fst.val < P1.numPhases := h_phase
  rw [embedSeqConfig_tape_at_head]
  show ((seq P1 P2).transition (embedSeqConfig P1 P2 c).state.fst
          (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)).snd.snd.snd =
       (P1.transition c.state.fst c.state.snd (c.tape c.head)).snd.snd.snd
  rw [seq_transition_P1_normal_move P1 P2 hlt hne
    (embedSeqConfig P1 P2 c).state.snd (c.tape c.head)]
  rfl

/-- Data-level commutation summary: all three value-level components
(phase index, local state, written bit, move direction) of one step
commute with embedSeqConfig under P1-normal-not-accept conditions.

Packaged as a conjunction for use in downstream proofs. -/
theorem embedSeqConfig_stepConfig_components
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    -- phase index equality
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).state.fst.val : Nat) =
      ((TM.stepConfig (M := P1.toPhased.toTM) c).state.fst.val : Nat) ∧
    -- local state equality
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).state.snd =
      (TM.stepConfig (M := P1.toPhased.toTM) c).state.snd ∧
    -- written bit equality
    (((seq P1 P2).toPhased.toTM.step (embedSeqConfig P1 P2 c).state
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).snd.fst : Bool) =
      ((P1.toPhased.toTM.step c.state (c.tape c.head)).snd.fst : Bool) ∧
    -- move direction equality
    (((seq P1 P2).toPhased.toTM.step (embedSeqConfig P1 P2 c).state
          ((embedSeqConfig P1 P2 c).tape (embedSeqConfig P1 P2 c).head)).snd.snd : Move) =
      ((P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd : Move) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact embedSeqConfig_stepConfig_state_fst_val P1 P2 c h_phase h_not_accept
  · exact embedSeqConfig_stepConfig_state_snd P1 P2 c h_phase h_not_accept
  · exact embedSeqConfig_stepConfig_written_bit P1 P2 c h_phase h_not_accept
  · exact embedSeqConfig_stepConfig_move P1 P2 c h_phase h_not_accept

/-- Full state equality after one stepConfig: the state (as a Σ-type
value) of `stepConfig (seq TM) (embed c)` equals the state of
`embed (stepConfig P1 c)`.  Combines phase-index Fin.ext with state.snd
equality. -/
theorem embedSeqConfig_stepConfig_state_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).state =
      (embedSeqConfig P1 P2 (TM.stepConfig (M := P1.toPhased.toTM) c)).state := by
  -- Sigma equality: (a, b) = (a', b') iff a = a' and b = b' (up to heq).
  have hval := embedSeqConfig_stepConfig_state_fst_val P1 P2 c h_phase h_not_accept
  have hsnd := embedSeqConfig_stepConfig_state_snd P1 P2 c h_phase h_not_accept
  have hsnd_embed :
      (embedSeqConfig P1 P2 (TM.stepConfig (M := P1.toPhased.toTM) c)).state.snd =
        (TM.stepConfig (M := P1.toPhased.toTM) c).state.snd := rfl
  have hval_embed :
      ((embedSeqConfig P1 P2 (TM.stepConfig (M := P1.toPhased.toTM) c)).state.fst : Nat) =
        ((TM.stepConfig (M := P1.toPhased.toTM) c).state.fst : Nat) := rfl
  -- Construct Sigma equality from component equalities.
  apply Sigma.ext
  · -- fst equality: both Fins have same Nat value
    apply Fin.ext
    rw [hval, ← hval_embed]
  · -- snd equality (heterogeneous to handle the Σ type)
    simp only [hsnd_embed]
    exact heq_of_eq hsnd

/-- Head value after one stepConfig commutes with embed, under the
usual P1-normal-not-accept condition and Move.right safety hypothesis.
(Value-level form; lifting to Fin equality follows by Fin.ext.) -/
theorem embedSeqConfig_stepConfig_head_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).head.val : Nat) =
      ((TM.stepConfig (M := P1.toPhased.toTM) c).head.val : Nat) := by
  rw [stepConfig_head, stepConfig_head]
  have hmove := embedSeqConfig_stepConfig_move P1 P2 c h_phase h_not_accept
  rw [hmove]
  exact embedSeqConfig_moveHead_val_commutes P1 P2 c _ (fun h => h_safe h)

/-- Head after stepConfig — stronger lemma: the Fin-value equality
lifts to Fin equality for positions consistent with the new head. -/
theorem embedSeqConfig_stepConfig_head_embed_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).head.val : Nat) =
      ((embedSeqConfig P1 P2
        (TM.stepConfig (M := P1.toPhased.toTM) c)).head.val : Nat) := by
  rw [embedSeqConfig_head_val]
  exact embedSeqConfig_stepConfig_head_val P1 P2 c h_phase h_not_accept h_safe

/-- After stepConfig, head moved plus-one is in P1's tape range iff
the original head plus-one was in P1's range (via move-commutation).
Technical helper for tape commutation. -/
theorem embedSeqConfig_stepConfig_head_in_P1
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).head.val : Nat) <
      P1.toPhased.toTM.tapeLength n := by
  rw [embedSeqConfig_stepConfig_head_val P1 P2 c h_phase h_not_accept h_safe]
  exact (TM.stepConfig (M := P1.toPhased.toTM) c).head.isLt

/-- Tape at a position OUTSIDE P1's tape range, after one stepConfig
on embed(c), remains `false`.  Useful for tape-commutation funext
proofs at out-of-range positions. -/
theorem embedSeqConfig_stepConfig_tape_out_of_range
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (_h_phase : c.state.fst.val < P1.numPhases)
    (_h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (_h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h_out : P1.toPhased.toTM.tapeLength n ≤ i.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).tape i = false := by
  rw [stepConfig_tape]
  have h_head_ne : i ≠ (embedSeqConfig P1 P2 c).head := by
    intro hEq
    have : i.val = (embedSeqConfig P1 P2 c).head.val := by rw [hEq]
    rw [embedSeqConfig_head_val] at this
    have := c.head.isLt
    omega
  unfold Configuration.write
  rw [dif_neg h_head_ne]
  exact embedSeqConfig_tape_out_of_range P1 P2 c i h_out

/-- Tape at a position INSIDE P1's tape range that is NOT the head,
after one stepConfig on embed(c), equals what it was on c (no change). -/
theorem embedSeqConfig_stepConfig_tape_in_range_not_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h_in : i.val < P1.toPhased.toTM.tapeLength n)
    (h_not_head : i.val ≠ c.head.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).tape i = c.tape ⟨i.val, h_in⟩ := by
  rw [stepConfig_tape]
  have h_head_ne : i ≠ (embedSeqConfig P1 P2 c).head := by
    intro hEq
    have : i.val = (embedSeqConfig P1 P2 c).head.val := by rw [hEq]
    rw [embedSeqConfig_head_val] at this
    exact h_not_head this
  unfold Configuration.write
  rw [dif_neg h_head_ne]
  exact embedSeqConfig_tape_in_range P1 P2 c i h_in

/-- Tape at the head position after one stepConfig on embed(c) equals
the bit that P1's step would write, under P1-normal-not-accept. -/
theorem embedSeqConfig_stepConfig_tape_at_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).tape (embedSeqConfig P1 P2 c).head =
      (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.fst := by
  rw [stepConfig_tape]
  unfold Configuration.write
  rw [dif_pos rfl]
  exact embedSeqConfig_stepConfig_written_bit P1 P2 c h_phase h_not_accept

/-- **Full tape commutation** after one stepConfig: funext over all
Fin positions, combining the three case lemmas (out-of-range, in-range
not-head, in-range at-head). -/
theorem embedSeqConfig_stepConfig_tape_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c)).tape =
      (embedSeqConfig P1 P2
        (TM.stepConfig (M := P1.toPhased.toTM) c)).tape := by
  funext i
  by_cases h : i.val < P1.toPhased.toTM.tapeLength n
  · -- Inside P1 range.
    rw [embedSeqConfig_tape_in_range P1 P2 _ i h]
    simp only [stepConfig_tape]
    by_cases heq : i.val = c.head.val
    · -- At head.
      have hLHS : i = (embedSeqConfig P1 P2 c).head := by
        apply Fin.ext; rw [embedSeqConfig_head_val]; exact heq
      have hRHS : (⟨i.val, h⟩ : Fin _) = c.head := Fin.ext heq
      unfold Configuration.write
      rw [dif_pos hLHS, dif_pos hRHS]
      exact embedSeqConfig_stepConfig_written_bit P1 P2 c h_phase h_not_accept
    · -- Not at head.
      have hLHS : i ≠ (embedSeqConfig P1 P2 c).head := by
        intro hEq
        apply heq
        have : i.val = (embedSeqConfig P1 P2 c).head.val := by rw [hEq]
        rw [embedSeqConfig_head_val] at this; exact this
      have hRHS : (⟨i.val, h⟩ : Fin _) ≠ c.head := by
        intro hEq
        apply heq
        have : (⟨i.val, h⟩ : Fin _).val = c.head.val := by rw [hEq]
        exact this
      unfold Configuration.write
      rw [dif_neg hLHS, dif_neg hRHS]
      exact embedSeqConfig_tape_in_range P1 P2 c i h
  · -- Outside P1 range.
    have h_out : P1.toPhased.toTM.tapeLength n ≤ i.val := by omega
    rw [embedSeqConfig_stepConfig_tape_out_of_range P1 P2 c h_phase h_not_accept h_safe i h_out,
        embedSeqConfig_tape_out_of_range P1 P2 _ i h_out]

/-- **FULL stepConfig commutation**: running one step on `embedSeqConfig c`
in the composed seq TM produces the same Configuration as embedding
one step of P1 alone on `c`. -/
theorem embedSeqConfig_stepConfig_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P1.numPhases)
    (h_not_accept : c.state.fst.val ≠ P1.acceptPhase.val)
    (h_safe : (P1.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P1.toPhased.toTM.tapeLength n) :
    TM.stepConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqConfig P1 P2 c) =
      embedSeqConfig P1 P2 (TM.stepConfig (M := P1.toPhased.toTM) c) := by
  have h_state := embedSeqConfig_stepConfig_state_eq P1 P2 c h_phase h_not_accept
  have h_tape := embedSeqConfig_stepConfig_tape_eq P1 P2 c h_phase h_not_accept h_safe
  have h_head_val :=
    embedSeqConfig_stepConfig_head_embed_val P1 P2 c h_phase h_not_accept h_safe
  -- Construct Configuration equality via structural ext.
  cases hL : (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
                (embedSeqConfig P1 P2 c)) with
  | mk sL hL_head tL =>
    cases hR : (embedSeqConfig P1 P2 (TM.stepConfig (M := P1.toPhased.toTM) c)) with
    | mk sR hR_head tR =>
      have hse : sL = sR := by rw [hL] at h_state; rw [hR] at h_state; exact h_state
      have hte : tL = tR := by rw [hL] at h_tape; rw [hR] at h_tape; exact h_tape
      have hhe : hL_head = hR_head := by
        apply Fin.ext
        have : (hL_head : Nat) = (hR_head : Nat) := by
          rw [hL] at h_head_val; rw [hR] at h_head_val; exact h_head_val
        exact this
      subst hse
      subst hte
      subst hhe
      rfl

/-- **runConfig commutation** by induction on step count.  If the
run-invariants hold for all intermediate steps < t, then running the
composed seq TM on `embed c` for t steps gives the same result as
embedding the t-step run of P1 alone. -/
theorem embedSeqConfig_runConfig_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P1.toPhased.toTM) n)
    (t : Nat)
    (h_safe_all : ∀ s < t,
      let c_s := TM.runConfig (M := P1.toPhased.toTM) c s
      c_s.state.fst.val < P1.numPhases ∧
      c_s.state.fst.val ≠ P1.acceptPhase.val ∧
      ((P1.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < P1.toPhased.toTM.tapeLength n)) :
    TM.runConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqConfig P1 P2 c) t =
      embedSeqConfig P1 P2 (TM.runConfig (M := P1.toPhased.toTM) c t) := by
  induction t with
  | zero => rfl
  | succ t' ih =>
    have ih' : TM.runConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqConfig P1 P2 c) t' =
        embedSeqConfig P1 P2 (TM.runConfig (M := P1.toPhased.toTM) c t') :=
      ih (fun s hs => h_safe_all s (by omega))
    rw [runConfig_succ, runConfig_succ, ih']
    have hinv := h_safe_all t' (by omega)
    exact embedSeqConfig_stepConfig_eq P1 P2
      (TM.runConfig (M := P1.toPhased.toTM) c t') hinv.1 hinv.2.1 hinv.2.2

/-! ### P2-region embedding: mirror of `embedSeqConfig` for the P2 side

After `seq P1 P2` has completed its P1 prefix + boundary handoff, the
remaining run takes place entirely in P2's phase range (phases
`[P1.numPhases, P1.numPhases + P2.numPhases)`).  To reuse P2's
standalone correctness, we need a dual of `embedSeqConfig`:
given a P2-config `c` (of `P2.toPhased.toTM`), produce a seq-config
with phase shifted by `P1.numPhases`, head / tape embedded as-is in
the first `P2.tapeLength` cells, and `false` padding for the extra
P1-slack cells.

Then we prove that stepping the seq-TM on such an embedded config
matches stepping P2 alone (when phase is in P2's range and not at
P2-accept), yielding a multi-step commutation analogous to
`embedSeqConfig_runConfig_eq`.  Used directly in the multi-gate
`circuitEvaluatorCS` induction. -/

theorem seq_tapeLength_ge_P2 (P1 P2 : ConstStatePhasedProgram S) (n : Nat) :
    P2.toPhased.toTM.tapeLength n ≤ (seq P1 P2).toPhased.toTM.tapeLength n := by
  show n + P2.timeBound n + 1 ≤ n + (P1.timeBound n + P2.timeBound n + 1) + 1
  omega

def embedSeqP2Config (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    Configuration (M := (seq P1 P2).toPhased.toTM) n where
  state := ⟨⟨P1.numPhases + c.state.fst.val, by
      have h2 := c.state.fst.isLt
      simp only [toPhased_numPhases] at h2
      show P1.numPhases + c.state.fst.val < (seq P1 P2).numPhases
      rw [seq_numPhases]; omega⟩,
    c.state.snd⟩
  head := ⟨c.head.val, by
    have := c.head.isLt
    have := seq_tapeLength_ge_P2 P1 P2 n
    omega⟩
  tape := fun i =>
    if h : i.val < P2.toPhased.toTM.tapeLength n then
      c.tape ⟨i.val, h⟩
    else
      false

@[simp] theorem embedSeqP2Config_state_fst_val (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    ((embedSeqP2Config P1 P2 c).state.fst : Nat) = P1.numPhases + c.state.fst.val := rfl

@[simp] theorem embedSeqP2Config_state_snd (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    (embedSeqP2Config P1 P2 c).state.snd = c.state.snd := rfl

@[simp] theorem embedSeqP2Config_head_val (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    ((embedSeqP2Config P1 P2 c).head : Nat) = c.head.val := rfl

/-- Tape at a position within P2's tape range is unchanged by embedding. -/
theorem embedSeqP2Config_tape_in_range (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h : i.val < P2.toPhased.toTM.tapeLength n) :
    (embedSeqP2Config P1 P2 c).tape i = c.tape ⟨i.val, h⟩ := by
  show (if h' : i.val < P2.toPhased.toTM.tapeLength n then _ else _) = _
  rw [dif_pos h]

/-- Tape outside P2's range (P1-slack padding) is `false`. -/
theorem embedSeqP2Config_tape_out_of_range (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h : P2.toPhased.toTM.tapeLength n ≤ i.val) :
    (embedSeqP2Config P1 P2 c).tape i = false := by
  show (if h' : i.val < P2.toPhased.toTM.tapeLength n then _ else _) = _
  rw [dif_neg (by omega)]

@[simp] theorem embedSeqP2Config_tape_at_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    (embedSeqP2Config P1 P2 c).tape (embedSeqP2Config P1 P2 c).head = c.tape c.head := by
  have h : (embedSeqP2Config P1 P2 c).head.val < P2.toPhased.toTM.tapeLength n := by
    simp only [embedSeqP2Config_head_val]; exact c.head.isLt
  rw [embedSeqP2Config_tape_in_range P1 P2 c (embedSeqP2Config P1 P2 c).head h]
  congr 1

/-! ### Single-step commutation for the P2-region embedding

Under the standard run-invariants on P2's config (phase in P2's range,
phase ≠ P2.accept, Move.right head-safe), stepping the seq TM on
`embedSeqP2Config c` equals `embedSeqP2Config (stepConfig P2 c)`.  The
proof structure mirrors the P1-side `embedSeqConfig_stepConfig_eq`. -/

/-- Phase-value after one step of seq TM on P2-embedding equals
`P1.numPhases + (phase after P2's step)`. -/
theorem embedSeqP2Config_stepConfig_state_fst_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).state.fst.val : Nat) =
      P1.numPhases + ((TM.stepConfig (M := P2.toPhased.toTM) c).state.fst.val : Nat) := by
  have h2 : P1.numPhases ≤ (embedSeqP2Config P1 P2 c).state.fst.val := by
    simp [embedSeqP2Config_state_fst_val]
  have hi_lt : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases < P2.numPhases := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases < P2.numPhases
    have : (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val := by omega
    rw [this]; exact h_phase
  rw [stepConfig_seq_P2_phase P1 P2 (embedSeqP2Config P1 P2 c) h2 hi_lt]
  rw [embedSeqP2Config_tape_at_head]
  have hshift : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases = c.state.fst.val := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val; omega
  have hfin : (⟨(embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases, hi_lt⟩ :
      Fin P2.numPhases) = c.state.fst := by
    apply Fin.ext; exact hshift
  -- Goal: P1.numPhases + (P2.transition ⟨shifted⟩ (embed).state.snd (c.tape c.head)).fst.val =
  --       P1.numPhases + ((stepConfig c).state.fst.val : Nat)
  rw [stepConfig_state]
  show P1.numPhases + (P2.transition
      ⟨(embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases, hi_lt⟩
      (embedSeqP2Config P1 P2 c).state.snd (c.tape c.head)).fst.val =
    P1.numPhases + ((P2.toPhased.toTM.step c.state (c.tape c.head)).fst.fst.val : Nat)
  congr 1
  rw [hfin]
  -- (embed).state.snd = c.state.snd and P2.toPhased.toTM.step = P2.transition wrapped.
  rfl

/-- State.snd after one step on P2-embedding equals P2.stepConfig's state.snd. -/
theorem embedSeqP2Config_stepConfig_state_snd
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).state.snd =
      (TM.stepConfig (M := P2.toPhased.toTM) c).state.snd := by
  have h2 : P1.numPhases ≤ (embedSeqP2Config P1 P2 c).state.fst.val := by
    simp [embedSeqP2Config_state_fst_val]
  have hi_lt : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases < P2.numPhases := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases < P2.numPhases
    have : (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val := by omega
    rw [this]; exact h_phase
  rw [stepConfig_seq_P2_state P1 P2 (embedSeqP2Config P1 P2 c) h2 hi_lt]
  rw [embedSeqP2Config_tape_at_head]
  have hshift : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases = c.state.fst.val := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val; omega
  have hfin : (⟨(embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases, hi_lt⟩ :
      Fin P2.numPhases) = c.state.fst := Fin.ext hshift
  rw [stepConfig_state]
  rw [hfin]
  -- (embedSeqP2Config P1 P2 c).state.snd = c.state.snd by rfl.
  rfl

/-- Head value after Move.stay on P2-embedded config equals original. -/
theorem embedSeqP2Config_moveHead_stay (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    ((Configuration.moveHead (c := embedSeqP2Config P1 P2 c) Move.stay : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.stay : Nat) := rfl

theorem embedSeqP2Config_moveHead_left (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) :
    ((Configuration.moveHead (c := embedSeqP2Config P1 P2 c) Move.left : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.left : Nat) := by
  show (if _ : (embedSeqP2Config P1 P2 c).head.val = 0 then _ else _ : Fin _).val =
       (if _ : c.head.val = 0 then _ else _ : Fin _).val
  simp only [embedSeqP2Config_head_val]
  split_ifs with h
  · simp [embedSeqP2Config_head_val, h]
  · rfl

theorem embedSeqP2Config_moveHead_right_safe (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_safe : c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    ((Configuration.moveHead (c := embedSeqP2Config P1 P2 c) Move.right : Fin _) : Nat) =
      (Configuration.moveHead (c := c) Move.right : Nat) := by
  have h_safe_seq : (embedSeqP2Config P1 P2 c).head.val + 1 <
      (seq P1 P2).toPhased.toTM.tapeLength n := by
    simp only [embedSeqP2Config_head_val]
    have := seq_tapeLength_ge_P2 P1 P2 n
    omega
  show (if _ : (embedSeqP2Config P1 P2 c).head.val + 1 <
          (seq P1 P2).toPhased.toTM.tapeLength n then _ else _ : Fin _).val =
       (if _ : c.head.val + 1 < P2.toPhased.toTM.tapeLength n then _ else _ : Fin _).val
  rw [dif_pos h_safe_seq, dif_pos h_safe]
  simp [embedSeqP2Config_head_val]

theorem embedSeqP2Config_moveHead_val_commutes (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n) (m : Move)
    (h_safe : m = Move.right → c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    ((Configuration.moveHead (c := embedSeqP2Config P1 P2 c) m : Fin _) : Nat) =
      (Configuration.moveHead (c := c) m : Nat) := by
  cases m with
  | stay => exact embedSeqP2Config_moveHead_stay P1 P2 c
  | left => exact embedSeqP2Config_moveHead_left P1 P2 c
  | right => exact embedSeqP2Config_moveHead_right_safe P1 P2 c (h_safe rfl)

/-- Written bit after one step on P2-embedding equals P2's step's written bit. -/
theorem embedSeqP2Config_stepConfig_written_bit
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    (((seq P1 P2).toPhased.toTM.step (embedSeqP2Config P1 P2 c).state
          ((embedSeqP2Config P1 P2 c).tape (embedSeqP2Config P1 P2 c).head)).snd.fst : Bool) =
      ((P2.toPhased.toTM.step c.state (c.tape c.head)).snd.fst : Bool) := by
  have h2 : P1.numPhases ≤ (embedSeqP2Config P1 P2 c).state.fst.val := by
    simp [embedSeqP2Config_state_fst_val]
  have hi_lt : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases < P2.numPhases := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases < P2.numPhases
    have : (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val := by omega
    rw [this]; exact h_phase
  rw [embedSeqP2Config_tape_at_head]
  show ((seq P1 P2).transition (embedSeqP2Config P1 P2 c).state.fst
          (embedSeqP2Config P1 P2 c).state.snd (c.tape c.head)).snd.snd.fst =
       ((P2.toPhased.toTM.step c.state (c.tape c.head)).snd.fst : Bool)
  rw [seq_transition_P2_bit P1 P2 h2 hi_lt
    (embedSeqP2Config P1 P2 c).state.snd (c.tape c.head)]
  have hshift : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases = c.state.fst.val := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val; omega
  have hfin : (⟨(embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases, hi_lt⟩ :
      Fin P2.numPhases) = c.state.fst := Fin.ext hshift
  rw [hfin]
  rfl

/-- Move direction after one step on P2-embedding equals P2's step's move. -/
theorem embedSeqP2Config_stepConfig_move
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    (((seq P1 P2).toPhased.toTM.step (embedSeqP2Config P1 P2 c).state
          ((embedSeqP2Config P1 P2 c).tape (embedSeqP2Config P1 P2 c).head)).snd.snd : Move) =
      ((P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd : Move) := by
  have h2 : P1.numPhases ≤ (embedSeqP2Config P1 P2 c).state.fst.val := by
    simp [embedSeqP2Config_state_fst_val]
  have hi_lt : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases < P2.numPhases := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases < P2.numPhases
    have : (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val := by omega
    rw [this]; exact h_phase
  rw [embedSeqP2Config_tape_at_head]
  show ((seq P1 P2).transition (embedSeqP2Config P1 P2 c).state.fst
          (embedSeqP2Config P1 P2 c).state.snd (c.tape c.head)).snd.snd.snd =
       ((P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd : Move)
  rw [seq_transition_P2_move P1 P2 h2 hi_lt
    (embedSeqP2Config P1 P2 c).state.snd (c.tape c.head)]
  have hshift : (embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases = c.state.fst.val := by
    show (P1.numPhases + c.state.fst.val) - P1.numPhases = c.state.fst.val; omega
  have hfin : (⟨(embedSeqP2Config P1 P2 c).state.fst.val - P1.numPhases, hi_lt⟩ :
      Fin P2.numPhases) = c.state.fst := Fin.ext hshift
  rw [hfin]
  rfl

/-- Head.val after one step commutes with P2-embedding. -/
theorem embedSeqP2Config_stepConfig_head_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases)
    (h_safe : (P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).head.val : Nat) =
      ((TM.stepConfig (M := P2.toPhased.toTM) c).head.val : Nat) := by
  rw [stepConfig_head, stepConfig_head]
  have hmove := embedSeqP2Config_stepConfig_move P1 P2 c h_phase
  rw [hmove]
  exact embedSeqP2Config_moveHead_val_commutes P1 P2 c _ h_safe

/-- Tape outside P2's range remains `false` after one step on P2-embedding. -/
theorem embedSeqP2Config_stepConfig_tape_out_of_range
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h_out : P2.toPhased.toTM.tapeLength n ≤ i.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).tape i = false := by
  rw [stepConfig_tape]
  have h_head_ne : i ≠ (embedSeqP2Config P1 P2 c).head := by
    intro hEq
    have : i.val = (embedSeqP2Config P1 P2 c).head.val := by rw [hEq]
    rw [embedSeqP2Config_head_val] at this
    have := c.head.isLt
    omega
  unfold Configuration.write
  rw [dif_neg h_head_ne]
  exact embedSeqP2Config_tape_out_of_range P1 P2 c i h_out

/-- Tape INSIDE P2's range but not at head is unchanged after step. -/
theorem embedSeqP2Config_stepConfig_tape_in_range_not_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (i : Fin ((seq P1 P2).toPhased.toTM.tapeLength n))
    (h_in : i.val < P2.toPhased.toTM.tapeLength n)
    (h_not_head : i.val ≠ c.head.val) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).tape i = c.tape ⟨i.val, h_in⟩ := by
  rw [stepConfig_tape]
  have h_head_ne : i ≠ (embedSeqP2Config P1 P2 c).head := by
    intro hEq
    have : i.val = (embedSeqP2Config P1 P2 c).head.val := by rw [hEq]
    rw [embedSeqP2Config_head_val] at this
    exact h_not_head this
  unfold Configuration.write
  rw [dif_neg h_head_ne]
  exact embedSeqP2Config_tape_in_range P1 P2 c i h_in

/-- Tape at head after step equals the bit P2 wrote. -/
theorem embedSeqP2Config_stepConfig_tape_at_head
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).tape (embedSeqP2Config P1 P2 c).head =
      (P2.toPhased.toTM.step c.state (c.tape c.head)).snd.fst := by
  rw [stepConfig_tape]
  unfold Configuration.write
  rw [dif_pos rfl]
  exact embedSeqP2Config_stepConfig_written_bit P1 P2 c h_phase

/-- Full tape commutation after one step on P2-embedding. -/
theorem embedSeqP2Config_stepConfig_tape_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases)
    (_h_safe : (P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).tape =
      (embedSeqP2Config P1 P2
        (TM.stepConfig (M := P2.toPhased.toTM) c)).tape := by
  funext i
  by_cases h : i.val < P2.toPhased.toTM.tapeLength n
  · rw [embedSeqP2Config_tape_in_range P1 P2 _ i h]
    simp only [stepConfig_tape]
    by_cases heq : i.val = c.head.val
    · have hLHS : i = (embedSeqP2Config P1 P2 c).head := by
        apply Fin.ext; rw [embedSeqP2Config_head_val]; exact heq
      have hRHS : (⟨i.val, h⟩ : Fin _) = c.head := Fin.ext heq
      unfold Configuration.write
      rw [dif_pos hLHS, dif_pos hRHS]
      exact embedSeqP2Config_stepConfig_written_bit P1 P2 c h_phase
    · have hLHS : i ≠ (embedSeqP2Config P1 P2 c).head := by
        intro hEq
        apply heq
        have : i.val = (embedSeqP2Config P1 P2 c).head.val := by rw [hEq]
        rw [embedSeqP2Config_head_val] at this; exact this
      have hRHS : (⟨i.val, h⟩ : Fin _) ≠ c.head := by
        intro hEq
        apply heq
        have : (⟨i.val, h⟩ : Fin _).val = c.head.val := by rw [hEq]
        exact this
      unfold Configuration.write
      rw [dif_neg hLHS, dif_neg hRHS]
      exact embedSeqP2Config_tape_in_range P1 P2 c i h
  · have h_out : P2.toPhased.toTM.tapeLength n ≤ i.val := by omega
    rw [embedSeqP2Config_stepConfig_tape_out_of_range P1 P2 c i h_out,
        embedSeqP2Config_tape_out_of_range P1 P2 _ i h_out]

/-- Full state equality after one step on P2-embedding: constructs Sigma equality from component equalities. -/
theorem embedSeqP2Config_stepConfig_state_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).state =
      (embedSeqP2Config P1 P2 (TM.stepConfig (M := P2.toPhased.toTM) c)).state := by
  have hval := embedSeqP2Config_stepConfig_state_fst_val P1 P2 c h_phase
  have hsnd := embedSeqP2Config_stepConfig_state_snd P1 P2 c h_phase
  have hsnd_embed :
      (embedSeqP2Config P1 P2 (TM.stepConfig (M := P2.toPhased.toTM) c)).state.snd =
        (TM.stepConfig (M := P2.toPhased.toTM) c).state.snd := rfl
  have hval_embed :
      ((embedSeqP2Config P1 P2 (TM.stepConfig (M := P2.toPhased.toTM) c)).state.fst : Nat) =
        P1.numPhases + ((TM.stepConfig (M := P2.toPhased.toTM) c).state.fst : Nat) := rfl
  apply Sigma.ext
  · apply Fin.ext
    rw [hval, ← hval_embed]
  · simp only [hsnd_embed]
    exact heq_of_eq hsnd

/-- Head.val-level equality lifted to Fin equality (strong form). -/
theorem embedSeqP2Config_stepConfig_head_embed_val
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases)
    (h_safe : (P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqP2Config P1 P2 c)).head.val : Nat) =
      ((embedSeqP2Config P1 P2
        (TM.stepConfig (M := P2.toPhased.toTM) c)).head.val : Nat) := by
  rw [embedSeqP2Config_head_val]
  exact embedSeqP2Config_stepConfig_head_val P1 P2 c h_phase h_safe

/-- **FULL stepConfig commutation on P2-embedding**. -/
theorem embedSeqP2Config_stepConfig_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (h_phase : c.state.fst.val < P2.numPhases)
    (h_safe : (P2.toPhased.toTM.step c.state (c.tape c.head)).snd.snd = Move.right →
        c.head.val + 1 < P2.toPhased.toTM.tapeLength n) :
    TM.stepConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqP2Config P1 P2 c) =
      embedSeqP2Config P1 P2 (TM.stepConfig (M := P2.toPhased.toTM) c) := by
  have h_state := embedSeqP2Config_stepConfig_state_eq P1 P2 c h_phase
  have h_tape := embedSeqP2Config_stepConfig_tape_eq P1 P2 c h_phase h_safe
  have h_head_val :=
    embedSeqP2Config_stepConfig_head_embed_val P1 P2 c h_phase h_safe
  cases hL : (TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
                (embedSeqP2Config P1 P2 c)) with
  | mk sL hL_head tL =>
    cases hR : (embedSeqP2Config P1 P2 (TM.stepConfig (M := P2.toPhased.toTM) c)) with
    | mk sR hR_head tR =>
      have hse : sL = sR := by rw [hL] at h_state; rw [hR] at h_state; exact h_state
      have hte : tL = tR := by rw [hL] at h_tape; rw [hR] at h_tape; exact h_tape
      have hhe : hL_head = hR_head := by
        apply Fin.ext
        have : (hL_head : Nat) = (hR_head : Nat) := by
          rw [hL] at h_head_val; rw [hR] at h_head_val; exact h_head_val
        exact this
      subst hse
      subst hte
      subst hhe
      rfl

/-- **Multi-step commutation on P2-embedding** via induction. -/
theorem embedSeqP2Config_runConfig_eq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P2.toPhased.toTM) n)
    (t : Nat)
    (h_safe_all : ∀ s < t,
      let c_s := TM.runConfig (M := P2.toPhased.toTM) c s
      c_s.state.fst.val < P2.numPhases ∧
      ((P2.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < P2.toPhased.toTM.tapeLength n)) :
    TM.runConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqP2Config P1 P2 c) t =
      embedSeqP2Config P1 P2 (TM.runConfig (M := P2.toPhased.toTM) c t) := by
  induction t with
  | zero => rfl
  | succ t' ih =>
    have ih' : TM.runConfig (M := (seq P1 P2).toPhased.toTM) (embedSeqP2Config P1 P2 c) t' =
        embedSeqP2Config P1 P2 (TM.runConfig (M := P2.toPhased.toTM) c t') :=
      ih (fun s hs => h_safe_all s (by omega))
    rw [runConfig_succ, runConfig_succ, ih']
    have hinv := h_safe_all t' (by omega)
    exact embedSeqP2Config_stepConfig_eq P1 P2
      (TM.runConfig (M := P2.toPhased.toTM) c t') hinv.1 hinv.2

/-! ### Lifting a P1-run to a P2-config for the boundary handoff

After the boundary step in `seq P1 P2`, the composite's tape is
`embedSeqConfig P1 P2 (P1.run c_P1 P1.timeBound)`-shaped — i.e.,
P1-padded.  To apply `embedSeqP2Config_runConfig_eq` for the tail, we
need a P2-config whose embed matches this shape.  `liftP1ToP2` below
constructs such a P2-config: its tape is the P1-run's tape on
`[0, P1.tapeLength)` and `false` elsewhere.

Applies under `P1.tapeLength ≤ P2.tapeLength`, which holds in the
multi-gate induction step whenever the tail `rest` is non-empty. -/

/-- Lift the `P1.timeBound`-run of `c_P1` to a P2-initial-config. -/
def liftP1ToP2 (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c_P1_final : Configuration (M := P1.toPhased.toTM) n)
    (h_head : c_P1_final.head.val < P2.toPhased.toTM.tapeLength n) :
    Configuration (M := P2.toPhased.toTM) n where
  state := ⟨⟨P2.startPhase.val, by simp only [toPhased_numPhases]; exact P2.startPhase.isLt⟩,
           P2.startState⟩
  head := ⟨c_P1_final.head.val, h_head⟩
  tape := fun i =>
    if h : i.val < P1.toPhased.toTM.tapeLength n
      then c_P1_final.tape ⟨i.val, h⟩
      else false

/-- The lift's embed in `seq P1 P2` has phase = P1.numPhases + P2.startPhase.val,
snd = P2.startState, head = c_P1_final.head (value-wise), and tape equal to
the embed of `c_P1_final` under `P1.tapeLength ≤ P2.tapeLength`. -/
theorem embedSeqP2Config_liftP1ToP2_tape
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c_P1_final : Configuration (M := P1.toPhased.toTM) n)
    (h_head : c_P1_final.head.val < P2.toPhased.toTM.tapeLength n)
    (h_len_le : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    (embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).tape =
    (embedSeqConfig P1 P2 c_P1_final).tape := by
  funext i
  by_cases h : i.val < P1.toPhased.toTM.tapeLength n
  · have h_P2 : i.val < P2.toPhased.toTM.tapeLength n := Nat.lt_of_lt_of_le h h_len_le
    show (if h' : i.val < P2.toPhased.toTM.tapeLength n
              then (liftP1ToP2 P1 P2 c_P1_final h_head).tape ⟨i.val, h'⟩ else false) =
          (if h'' : i.val < P1.toPhased.toTM.tapeLength n
              then c_P1_final.tape ⟨i.val, h''⟩ else false)
    rw [dif_pos h_P2, dif_pos h]
    show (if h' : i.val < P1.toPhased.toTM.tapeLength n
              then c_P1_final.tape ⟨i.val, h'⟩ else false) =
          c_P1_final.tape ⟨i.val, h⟩
    rw [dif_pos h]
  · show (if h' : i.val < P2.toPhased.toTM.tapeLength n
              then (liftP1ToP2 P1 P2 c_P1_final h_head).tape ⟨i.val, h'⟩ else false) =
          (if h'' : i.val < P1.toPhased.toTM.tapeLength n
              then c_P1_final.tape ⟨i.val, h''⟩ else false)
    rw [dif_neg h]
    by_cases h_P2 : i.val < P2.toPhased.toTM.tapeLength n
    · rw [dif_pos h_P2]
      show (if h' : i.val < P1.toPhased.toTM.tapeLength n
              then c_P1_final.tape ⟨i.val, h'⟩ else false) = false
      rw [dif_neg h]
    · rw [dif_neg h_P2]

/-- Configuration equality: under `P1.tapeLength ≤ P2.tapeLength`,
`embedSeqP2Config P1 P2 (liftP1ToP2 c_P1_final _)` equals the full config
with phase = `P1.numPhases + P2.startPhase.val`, snd = `P2.startState`,
head = `embed-head of c_P1_final`, and tape = `embed-tape of c_P1_final`.
This is the Configuration-level version of
`embedSeqP2Config_liftP1ToP2_tape`. -/
theorem embedSeqP2Config_liftP1ToP2_eq_embedded_shape
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c_P1_final : Configuration (M := P1.toPhased.toTM) n)
    (h_head : c_P1_final.head.val < P2.toPhased.toTM.tapeLength n)
    (h_len_le : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    -- Component identities sufficient to Identify both Configurations:
    ((embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).state.fst.val : Nat) =
      P1.numPhases + P2.startPhase.val ∧
    (embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).state.snd =
      P2.startState ∧
    ((embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).head.val : Nat) =
      c_P1_final.head.val ∧
    (embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).tape =
      (embedSeqConfig P1 P2 c_P1_final).tape := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact embedSeqP2Config_liftP1ToP2_tape P1 P2 c_P1_final h_head h_len_le

/-- Consequence of `embedSeqP2Config_liftP1ToP2_tape` combined with the
individual `.state` and `.head` identities: the full
`embedSeqP2Config (liftP1ToP2 c)` Configuration satisfies head-value and
tape pointwise equality with the composite's post-boundary shape.
Packaged as a single Configuration equality (via structural case
analysis). -/
theorem embedSeqP2Config_liftP1ToP2_headTape_agrees
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c_P1_final : Configuration (M := P1.toPhased.toTM) n)
    (h_head : c_P1_final.head.val < P2.toPhased.toTM.tapeLength n)
    (h_len_le : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    (embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).head =
      (embedSeqConfig P1 P2 c_P1_final).head ∧
    (embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_final h_head)).tape =
      (embedSeqConfig P1 P2 c_P1_final).tape := by
  refine ⟨?_, embedSeqP2Config_liftP1ToP2_tape P1 P2 c_P1_final h_head h_len_le⟩
  exact Fin.ext rfl

end ConstStatePhasedProgram

end TM

end PsubsetPpoly
end Internal
end Pnp3
