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

end ConstStatePhasedProgram

end TM

end PsubsetPpoly
end Internal
end Pnp3
