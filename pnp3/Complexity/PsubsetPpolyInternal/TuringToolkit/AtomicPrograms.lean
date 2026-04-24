import Complexity.PsubsetPpolyInternal.TuringToolkit.Encoding

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace SeekRight

/-- The head-right-only program: `Δ` copies of the move-right
transition, followed by an accepting idle phase. -/
def seekRightProgram (Δ : Nat) : PhasedProgram.{0} where
  numPhases := Δ + 1
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨Δ, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if hi : i.val < Δ then
      (⟨⟨i.val + 1, by omega⟩, ()⟩, b, Move.right)
    else
      (⟨⟨Δ, by omega⟩, ()⟩, b, Move.stay)
  timeBound := fun _ => Δ

/-! ### Structural projections -/

@[simp] theorem seekRightProgram_numPhases (Δ : Nat) :
    (seekRightProgram Δ).numPhases = Δ + 1 := rfl

@[simp] theorem seekRightProgram_startPhase (Δ : Nat) :
    ((seekRightProgram Δ).startPhase : Fin (Δ + 1)).val = 0 := rfl

@[simp] theorem seekRightProgram_acceptPhase (Δ : Nat) :
    ((seekRightProgram Δ).acceptPhase : Fin (Δ + 1)).val = Δ := rfl

@[simp] theorem seekRightProgram_timeBound (Δ n : Nat) :
    (seekRightProgram Δ).timeBound n = Δ := rfl

/-- `seekRightProgram` never moves left. -/
theorem seekRightProgram_toTM_never_moves_left (Δ : Nat) :
    TMNeverMovesLeft (seekRightProgram Δ).toTM := by
  intro s b
  rcases s with ⟨i, q⟩
  show ((seekRightProgram Δ).transition i q b).snd.snd ≠ Move.left
  by_cases hi : i.val < Δ
  · simp [seekRightProgram, hi]
  · simp [seekRightProgram, hi]

/-- In the active phase `i < Δ` with bit `b`, the transition writes
`b` back (tape unchanged at head) and moves right, advancing the
phase. -/
theorem seekRightProgram_transition_active (Δ : Nat)
    {i : Fin ((seekRightProgram Δ).numPhases)} (hi : i.val < Δ)
    (q : (seekRightProgram Δ).phaseState i) (b : Bool) :
    ((seekRightProgram Δ).transition i q b).fst.fst.val = i.val + 1 ∧
    ((seekRightProgram Δ).transition i q b).snd.fst = b ∧
    ((seekRightProgram Δ).transition i q b).snd.snd = Move.right := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [seekRightProgram, hi]

/-- In the accepting phase `i = Δ`, the transition writes the bit
back (no change) and stays, looping on the accepting phase. -/
theorem seekRightProgram_transition_accept (Δ : Nat)
    {i : Fin ((seekRightProgram Δ).numPhases)} (hi : i.val = Δ)
    (q : (seekRightProgram Δ).phaseState i) (b : Bool) :
    ((seekRightProgram Δ).transition i q b).fst.fst.val = Δ ∧
    ((seekRightProgram Δ).transition i q b).snd.fst = b ∧
    ((seekRightProgram Δ).transition i q b).snd.snd = Move.stay := by
  have hni : ¬ i.val < Δ := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp [seekRightProgram, hni]

/-- `stepConfig` in the active phase: advances phase by one, head
by one (within bounds), tape unchanged. -/
theorem seekRightProgram_stepConfig_active (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekRightProgram Δ).toTM) n)
    (hi : c.state.fst.val < Δ)
    (hhead_bound : (c.head : ℕ) + 1 <
        (seekRightProgram Δ).toTM.tapeLength n) :
    (TM.stepConfig (M := (seekRightProgram Δ).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    ((TM.stepConfig (M := (seekRightProgram Δ).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (seekRightProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    seekRightProgram_transition_active Δ (i := c.state.fst) hi
      c.state.snd (c.tape c.head)
  have hmove_step :
      (((seekRightProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.right := hmove
  have hbit_step :
      (((seekRightProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((seekRightProgram Δ).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) hhead_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-! ### J-fold seek invariant

After `j ≤ Δ` steps starting from phase 0, the seek program is in
phase `j` with the head advanced by `j` and the tape unchanged.
Proved by induction on `j`.
-/

theorem seekRightProgram_run_invariant (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekRightProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + Δ <
        (seekRightProgram Δ).toTM.tapeLength n) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (seekRightProgram Δ).toTM) c j
    cj.state.fst.val = j ∧
    ((cj.head : ℕ) = (c.head : ℕ) + j) ∧
    cj.tape = c.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show (c.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (seekRightProgram Δ).toTM) c j' with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ := by rw [ih_phase]; exact hj'_lt_Δ
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (seekRightProgram Δ).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨rip_phase, rip_head, rip_tape⟩ :=
      seekRightProgram_stepConfig_active Δ cj' h_phase_cj' h_head_advance_bound
    have hrw : TM.runConfig (M := (seekRightProgram Δ).toTM) c (j' + 1) =
        TM.stepConfig (M := (seekRightProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_head, ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- After the full `Δ`-step budget, the head has advanced by `Δ`
and the tape is unchanged. -/
theorem seekRightProgram_run_Δ (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekRightProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + Δ <
        (seekRightProgram Δ).toTM.tapeLength n) :
    ((TM.runConfig (M := (seekRightProgram Δ).toTM) c Δ).head : ℕ) =
        (c.head : ℕ) + Δ ∧
    (TM.runConfig (M := (seekRightProgram Δ).toTM) c Δ).tape = c.tape :=
  let ⟨_, h_head, h_tape⟩ :=
    seekRightProgram_run_invariant Δ c h_phase h_bound Δ le_rfl
  ⟨h_head, h_tape⟩

end SeekRight

/-!
## Session 9e-d (step 3): `writeBitProgram` primitive

`writeBitProgram b` is a `PhasedProgram` that writes the Bool `b`
at the current head position and stops (one TM step total).

Combined with `seekRightProgram`, this covers both tape-read
navigation and tape-write primitives.  Together they suffice for
composing the gate-evaluator phases.
-/

namespace WriteBit

/-- Two-phase program: phase 0 writes `b` and jumps to accepting;
phase 1 (accepting) idles. -/
def writeBitProgram (b : Bool) : PhasedProgram.{0} where
  numPhases := 2
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ _ =>
    if i.val = 0 then
      (⟨⟨1, by omega⟩, ()⟩, b, Move.stay)
    else
      (⟨⟨1, by omega⟩, ()⟩, false, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem writeBitProgram_numPhases (b : Bool) :
    (writeBitProgram b).numPhases = 2 := rfl

@[simp] theorem writeBitProgram_startPhase (b : Bool) :
    ((writeBitProgram b).startPhase : Fin 2).val = 0 := rfl

@[simp] theorem writeBitProgram_acceptPhase (b : Bool) :
    ((writeBitProgram b).acceptPhase : Fin 2).val = 1 := rfl

@[simp] theorem writeBitProgram_timeBound (b : Bool) (n : Nat) :
    (writeBitProgram b).timeBound n = 1 := rfl

/-- `writeBitProgram` never moves left. -/
theorem writeBitProgram_toTM_never_moves_left (b : Bool) :
    TMNeverMovesLeft (writeBitProgram b).toTM := by
  intro s scannedBit
  rcases s with ⟨i, q⟩
  show ((writeBitProgram b).transition i q scannedBit).snd.snd ≠ Move.left
  by_cases hi : i.val = 0
  · simp [writeBitProgram, hi]
  · simp [writeBitProgram, hi]

/-- Transition at start (phase 0): write `b`, stay, advance phase. -/
theorem writeBitProgram_transition_start (b : Bool)
    {i : Fin ((writeBitProgram b).numPhases)} (hi : i.val = 0)
    (q : (writeBitProgram b).phaseState i) (scannedBit : Bool) :
    ((writeBitProgram b).transition i q scannedBit).fst.fst.val = 1 ∧
    ((writeBitProgram b).transition i q scannedBit).snd.fst = b ∧
    ((writeBitProgram b).transition i q scannedBit).snd.snd = Move.stay := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [writeBitProgram, hi]

/-- `stepConfig` from the start phase: writes `b` at the current head
position, the head does not move, and the phase advances to 1. -/
theorem writeBitProgram_stepConfig_start (b : Bool) {n : Nat}
    (c : Configuration (M := (writeBitProgram b).toTM) n)
    (h_phase : c.state.fst.val = 0) :
    (TM.stepConfig (M := (writeBitProgram b).toTM) c).state.fst.val = 1 ∧
    (TM.stepConfig (M := (writeBitProgram b).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (writeBitProgram b).toTM) c).tape = c.write c.head b := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    writeBitProgram_transition_start b (i := c.state.fst) h_phase
      c.state.snd (c.tape c.head)
  have hmove_step :
      (((writeBitProgram b).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := hmove
  have hbit_step :
      (((writeBitProgram b).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = b := hbit
  have hphase_step :
      ((((writeBitProgram b).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]

/-- After the full 1-step run from phase 0, `writeBitProgram b` has
written `b` at the initial head position, left the head where it
was, and entered the accepting phase. -/
theorem writeBitProgram_run_1 (b : Bool) {n : Nat}
    (c : Configuration (M := (writeBitProgram b).toTM) n)
    (h_phase : c.state.fst.val = 0) :
    (TM.runConfig (M := (writeBitProgram b).toTM) c 1).state.fst.val = 1 ∧
    (TM.runConfig (M := (writeBitProgram b).toTM) c 1).head = c.head ∧
    (TM.runConfig (M := (writeBitProgram b).toTM) c 1).tape = c.write c.head b := by
  rw [runConfig_one]
  exact writeBitProgram_stepConfig_start b c h_phase

end WriteBit

/-!
## Session 9e-d (step 4): `seekLeftProgram` primitive

Symmetric counterpart to `seekRightProgram`: moves the head left
by exactly `Δ` cells, provided the initial head is far enough from
the left edge.

Correctness requires `head.val ≥ Δ` (so the leftward moves never
clamp at position 0).  Under this precondition, each step
decrements the head by one and the tape is unchanged.
-/

namespace SeekLeft

/-- `Δ`-step left-shift PhasedProgram. -/
def seekLeftProgram (Δ : Nat) : PhasedProgram.{0} where
  numPhases := Δ + 1
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨Δ, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if hi : i.val < Δ then
      (⟨⟨i.val + 1, by omega⟩, ()⟩, b, Move.left)
    else
      (⟨⟨Δ, by omega⟩, ()⟩, b, Move.stay)
  timeBound := fun _ => Δ

@[simp] theorem seekLeftProgram_numPhases (Δ : Nat) :
    (seekLeftProgram Δ).numPhases = Δ + 1 := rfl

@[simp] theorem seekLeftProgram_startPhase (Δ : Nat) :
    ((seekLeftProgram Δ).startPhase : Fin (Δ + 1)).val = 0 := rfl

@[simp] theorem seekLeftProgram_acceptPhase (Δ : Nat) :
    ((seekLeftProgram Δ).acceptPhase : Fin (Δ + 1)).val = Δ := rfl

@[simp] theorem seekLeftProgram_timeBound (Δ n : Nat) :
    (seekLeftProgram Δ).timeBound n = Δ := rfl

/-- In the active phase: writes bit back, `Move.left`, advances phase. -/
theorem seekLeftProgram_transition_active (Δ : Nat)
    {i : Fin ((seekLeftProgram Δ).numPhases)} (hi : i.val < Δ)
    (q : (seekLeftProgram Δ).phaseState i) (b : Bool) :
    ((seekLeftProgram Δ).transition i q b).fst.fst.val = i.val + 1 ∧
    ((seekLeftProgram Δ).transition i q b).snd.fst = b ∧
    ((seekLeftProgram Δ).transition i q b).snd.snd = Move.left := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [seekLeftProgram, hi]

/-- One `stepConfig` in active phase, given head > 0 to avoid clamping:
phase advances by 1, head decrements by 1, tape unchanged. -/
theorem seekLeftProgram_stepConfig_active (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekLeftProgram Δ).toTM) n)
    (hi : c.state.fst.val < Δ)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (seekLeftProgram Δ).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    ((TM.stepConfig (M := (seekLeftProgram Δ).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (seekLeftProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    seekLeftProgram_transition_active Δ (i := c.state.fst) hi
      c.state.snd (c.tape c.head)
  have hmove_step :
      (((seekLeftProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.left := hmove
  have hbit_step :
      (((seekLeftProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((seekLeftProgram Δ).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-- j-fold invariant under `head.val ≥ Δ`. -/
theorem seekLeftProgram_run_invariant (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekLeftProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_head_ge : Δ ≤ (c.head : ℕ)) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (seekLeftProgram Δ).toTM) c j
    cj.state.fst.val = j ∧
    ((cj.head : ℕ) = (c.head : ℕ) - j) ∧
    cj.tape = c.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show (c.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (seekLeftProgram Δ).toTM) c j' with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ := by rw [ih_phase]; exact hj'_lt_Δ
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_head, rip_tape⟩ :=
      seekLeftProgram_stepConfig_active Δ cj' h_phase_cj' h_head_pos
    have hrw : TM.runConfig (M := (seekLeftProgram Δ).toTM) c (j' + 1) =
        TM.stepConfig (M := (seekLeftProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_head, ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- Full-budget result: after Δ steps, head has decreased by Δ, tape
unchanged. -/
theorem seekLeftProgram_run_Δ (Δ : Nat) {n : Nat}
    (c : Configuration (M := (seekLeftProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_head_ge : Δ ≤ (c.head : ℕ)) :
    ((TM.runConfig (M := (seekLeftProgram Δ).toTM) c Δ).head : ℕ) =
        (c.head : ℕ) - Δ ∧
    (TM.runConfig (M := (seekLeftProgram Δ).toTM) c Δ).tape = c.tape :=
  let ⟨_, h_head, h_tape⟩ :=
    seekLeftProgram_run_invariant Δ c h_phase h_head_ge Δ le_rfl
  ⟨h_head, h_tape⟩

end SeekLeft

/-!
## Session 9e-d (step 5): `readBitProgram` primitive

`readBitProgram` is a one-step program that reads the bit at the
current head position *into its own state* and stops.  Acceptance:
the compiled TM accepts iff the scanned bit was `true`.

Together with `seekRightProgram` / `seekLeftProgram` / `writeBitProgram`
this is the last of the four atomic tape operations: navigate, read,
write, mutate.  Higher-level verifier phases (gate dispatch,
iteration, consistency check) will compose these.
-/

namespace ReadBit

/-- Two-phase program.  Phase 0 (`Bool` state, ignored): reads the
scanned bit, moves to phase 1 carrying the bit as state, stays.
Phase 1 (accepting): state `true` = accept, state `false` = reject. -/
def readBitProgram : PhasedProgram.{0} where
  numPhases := 2
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := false
  acceptPhase := ⟨1, by omega⟩
  acceptState := true
  transition := fun i q b =>
    if i.val = 0 then
      -- Phase 0: read `b`, enter phase 1 with state = b, stay,
      -- write bit back unchanged.
      (⟨⟨1, by omega⟩, b⟩, b, Move.stay)
    else
      -- Phase 1: idle (not executed when runTime = 1).
      (⟨⟨i.val, by omega⟩, q⟩, b, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem readBitProgram_numPhases :
    readBitProgram.numPhases = 2 := rfl

@[simp] theorem readBitProgram_timeBound (n : Nat) :
    readBitProgram.timeBound n = 1 := rfl

/-- `readBitProgram` never moves left. -/
theorem readBitProgram_toTM_never_moves_left :
    TMNeverMovesLeft readBitProgram.toTM := by
  intro s b
  rcases s with ⟨i, q⟩
  show (readBitProgram.transition i q b).snd.snd ≠ Move.left
  by_cases hi : i.val = 0
  · simp [readBitProgram, hi]
  · simp [readBitProgram, hi]

/-- Transition in phase 0: read bit `b`, carry it as new state,
stay, write back. -/
theorem readBitProgram_transition_read
    {i : Fin readBitProgram.numPhases} (hi : i.val = 0)
    (q : readBitProgram.phaseState i) (b : Bool) :
    (readBitProgram.transition i q b).fst = (⟨⟨1, by decide⟩, b⟩) ∧
    (readBitProgram.transition i q b).snd.fst = b ∧
    (readBitProgram.transition i q b).snd.snd = Move.stay := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [readBitProgram, hi]

/-- One step from the start phase: state becomes ⟨1, b⟩ where `b` is
the bit under the head; head unchanged; tape unchanged. -/
theorem readBitProgram_stepConfig_start {n : Nat}
    (c : Configuration (M := readBitProgram.toTM) n)
    (h_phase : c.state.fst.val = 0) :
    (TM.stepConfig (M := readBitProgram.toTM) c).state =
        (⟨⟨1, by decide⟩, c.tape c.head⟩ :
          Σ i : Fin readBitProgram.numPhases, readBitProgram.phaseState i) ∧
    (TM.stepConfig (M := readBitProgram.toTM) c).head = c.head ∧
    (TM.stepConfig (M := readBitProgram.toTM) c).tape = c.tape := by
  obtain ⟨hnext, hbit, hmove⟩ :=
    readBitProgram_transition_read (i := c.state.fst) h_phase
      c.state.snd (c.tape c.head)
  have hmove_step :
      ((readBitProgram.toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := hmove
  have hbit_step :
      ((readBitProgram.toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hnext
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-- After the full 1-step run from phase 0 on any configuration, the
state holds `⟨1, bit⟩` where `bit` was read from head; head and tape
are unchanged. -/
theorem readBitProgram_run_1 {n : Nat}
    (c : Configuration (M := readBitProgram.toTM) n)
    (h_phase : c.state.fst.val = 0) :
    (TM.runConfig (M := readBitProgram.toTM) c 1).state =
        (⟨⟨1, by decide⟩, c.tape c.head⟩ :
          Σ i : Fin readBitProgram.numPhases, readBitProgram.phaseState i) ∧
    (TM.runConfig (M := readBitProgram.toTM) c 1).head = c.head ∧
    (TM.runConfig (M := readBitProgram.toTM) c 1).tape = c.tape := by
  rw [runConfig_one]
  exact readBitProgram_stepConfig_start c h_phase

end ReadBit

/-!
## Session 9e-d (step 6): `writeAtOffsetProgram` compound

`writeAtOffsetProgram Δ b` is the first compound (monolithic)
PhasedProgram in the toolkit.  It composes the effects of three
atomic primitives into a single TM:

1. seek head right by `Δ` cells,
2. write bit `b` at the new head position,
3. seek head back left by `Δ` cells.

Resulting effect (under `head + Δ` fits + `head ≥ 0`): the tape
has `b` written at position `head + Δ`; everything else unchanged;
head back at its initial position.

This is the canonical "write-at-scratch" primitive for the
MCSP evaluator: given a computed gate value `b` and the scratch
offset `Δ`, it commits the value and returns to the main cursor.

Phases:
* 0..Δ-1: seek right (`Δ` phases).
* Δ: write `b`, stay (1 phase).
* Δ+1..2Δ: seek left (`Δ` phases).
* 2Δ+1: accepting idle (1 phase).

Total phases: `2Δ + 2`.  runTime: `2Δ + 1`.
-/

end TM

end PsubsetPpoly
end Internal
end Pnp3
