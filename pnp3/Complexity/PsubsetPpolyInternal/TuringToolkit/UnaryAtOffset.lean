import Complexity.PsubsetPpolyInternal.TuringToolkit.AtomicPrograms

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM


namespace WriteAtOffset

/-- Three-block compound: seek right Δ, write b, seek left Δ. -/
def writeAtOffsetProgram (Δ : Nat) (b : Bool) : PhasedProgram.{0} where
  numPhases := 2 * Δ + 2
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨2 * Δ + 1, by omega⟩
  acceptState := ()
  transition := fun i _ scan =>
    if hi1 : i.val < Δ then
      -- seeking right: write scan back, Move.right, advance phase.
      (⟨⟨i.val + 1, by omega⟩, ()⟩, scan, Move.right)
    else if hi2 : i.val = Δ then
      -- write phase: emit bit b, stay, advance to Δ+1.
      (⟨⟨Δ + 1, by omega⟩, ()⟩, b, Move.stay)
    else if hi3 : i.val < 2 * Δ + 1 then
      -- seeking left: write scan back, Move.left, advance phase.
      (⟨⟨i.val + 1, by omega⟩, ()⟩, scan, Move.left)
    else
      -- accepting idle.
      (⟨⟨2 * Δ + 1, by omega⟩, ()⟩, scan, Move.stay)
  timeBound := fun _ => 2 * Δ + 1

@[simp] theorem writeAtOffsetProgram_numPhases (Δ : Nat) (b : Bool) :
    (writeAtOffsetProgram Δ b).numPhases = 2 * Δ + 2 := rfl

@[simp] theorem writeAtOffsetProgram_startPhase (Δ : Nat) (b : Bool) :
    ((writeAtOffsetProgram Δ b).startPhase :
      Fin ((writeAtOffsetProgram Δ b).numPhases)).val = 0 := rfl

@[simp] theorem writeAtOffsetProgram_acceptPhase (Δ : Nat) (b : Bool) :
    ((writeAtOffsetProgram Δ b).acceptPhase :
      Fin ((writeAtOffsetProgram Δ b).numPhases)).val = 2 * Δ + 1 := rfl

@[simp] theorem writeAtOffsetProgram_timeBound (Δ : Nat) (b : Bool) (n : Nat) :
    (writeAtOffsetProgram Δ b).timeBound n = 2 * Δ + 1 := rfl

/-! ### Transition helpers — per-block behaviour -/

/-- Phases `0..Δ-1` (seeking right): write scan back, advance phase,
move right. -/
theorem transition_seeking_right (Δ : Nat) (b : Bool)
    {i : Fin ((writeAtOffsetProgram Δ b).numPhases)} (hi : i.val < Δ)
    (q : (writeAtOffsetProgram Δ b).phaseState i) (scan : Bool) :
    ((writeAtOffsetProgram Δ b).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.fst = scan ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.snd = Move.right := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [writeAtOffsetProgram, hi]

/-- Phase `Δ` (write phase): emit bit `b`, stay, advance to phase `Δ+1`. -/
theorem transition_write (Δ : Nat) (b : Bool)
    {i : Fin ((writeAtOffsetProgram Δ b).numPhases)} (hi : i.val = Δ)
    (q : (writeAtOffsetProgram Δ b).phaseState i) (scan : Bool) :
    ((writeAtOffsetProgram Δ b).transition i q scan).fst.fst.val = Δ + 1 ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.fst = b ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.snd = Move.stay := by
  have hni : ¬ i.val < Δ := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp [writeAtOffsetProgram, hni, hi]

/-- Phases `Δ+1..2Δ` (seeking left): write scan back, advance phase,
move left. -/
theorem transition_seeking_left (Δ : Nat) (b : Bool)
    {i : Fin ((writeAtOffsetProgram Δ b).numPhases)}
    (hi_lo : Δ < i.val) (hi_hi : i.val < 2 * Δ + 1)
    (q : (writeAtOffsetProgram Δ b).phaseState i) (scan : Bool) :
    ((writeAtOffsetProgram Δ b).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.fst = scan ∧
    ((writeAtOffsetProgram Δ b).transition i q scan).snd.snd = Move.left := by
  have hn1 : ¬ i.val < Δ := by omega
  have hn2 : ¬ i.val = Δ := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp [writeAtOffsetProgram, hn1, hn2, hi_hi]

/-! ### stepConfig per-block -/

/-- One stepConfig while seeking right: advance phase, head += 1,
tape unchanged. -/
theorem stepConfig_seeking_right (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (hi : c.state.fst.val < Δ)
    (h_head_bound : (c.head : ℕ) + 1 <
        (writeAtOffsetProgram Δ b).toTM.tapeLength n) :
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    ((TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).tape = c.tape := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    transition_seeking_right Δ b (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.right := hmove
  have hbit_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-! ### j-fold invariant for the seek-right block

After `j ≤ Δ` steps starting from phase 0, we are in phase `j` with
the head advanced by `j` and the tape unchanged. -/
theorem run_after_j_right_steps (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + Δ <
        (writeAtOffsetProgram Δ b).toTM.tapeLength n) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c j
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
    set cj' := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c j'
      with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ := by rw [ih_phase]; exact hj'_lt_Δ
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (writeAtOffsetProgram Δ b).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨rip_phase, rip_head, rip_tape⟩ :=
      stepConfig_seeking_right Δ b cj' h_phase_cj' h_head_advance_bound
    have hrw :
        TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (j' + 1) =
          TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_head, ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- One stepConfig in the write phase (phase `Δ`): phase advances
to `Δ+1`, head stays, tape has `b` written at current head. -/
theorem stepConfig_write (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (hi : c.state.fst.val = Δ) :
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).state.fst.val =
        Δ + 1 ∧
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).tape =
        c.write c.head b := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    transition_write Δ b (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := hmove
  have hbit_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = b := hbit
  have hphase_step :
      ((((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = Δ + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]

/-- After `Δ + 1` steps starting from phase 0: the seek-right block
has advanced the head by `Δ`, the write phase has just committed
bit `b` at the new head position, and we are now in phase `Δ + 1`
with the head still at `c.head + Δ`. -/
theorem run_after_write_phase (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + Δ <
        (writeAtOffsetProgram Δ b).toTM.tapeLength n) :
    let cmid := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (Δ + 1)
    cmid.state.fst.val = Δ + 1 ∧
    ((cmid.head : ℕ) = (c.head : ℕ) + Δ) ∧
    (∀ (h_off_bound :
          (c.head : ℕ) + Δ < (writeAtOffsetProgram Δ b).toTM.tapeLength n),
        cmid.tape = c.write ⟨(c.head : ℕ) + Δ, h_off_bound⟩ b) := by
  -- After Δ steps: right block invariant.
  obtain ⟨right_phase, right_head, right_tape⟩ :=
    run_after_j_right_steps Δ b c h_phase h_bound Δ le_rfl
  set cΔ := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c Δ with hcΔ
  -- Write step: one more step at phase Δ produces tape = cΔ.write cΔ.head b.
  have h_phase_cΔ : cΔ.state.fst.val = Δ := right_phase
  obtain ⟨wr_phase, wr_head, wr_tape⟩ :=
    stepConfig_write Δ b cΔ h_phase_cΔ
  -- runConfig c (Δ+1) = stepConfig cΔ.
  have hrw :
      TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (Δ + 1) =
        TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) cΔ := by
    rw [runConfig_succ]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]; exact wr_phase
  · rw [hrw, wr_head, right_head]
  · intro h_off_bound
    rw [hrw, wr_tape]
    -- Goal: cΔ.write cΔ.head b = c.write ⟨c.head + Δ, _⟩ b
    have h_head_eq : cΔ.head = (⟨(c.head : ℕ) + Δ, h_off_bound⟩ :
        Fin ((writeAtOffsetProgram Δ b).toTM.tapeLength n)) := by
      apply Fin.ext; exact right_head
    rw [h_head_eq]
    -- Goal: cΔ.write ⟨c.head + Δ, _⟩ b = c.write ⟨c.head + Δ, _⟩ b
    funext j
    unfold Configuration.write
    split_ifs with hj
    · rfl
    · rw [right_tape]

/-- One stepConfig in the seek-left block (phase Δ+1..2Δ) with head
> 0: phase advances by 1, head decrements by 1, tape unchanged. -/
theorem stepConfig_seeking_left (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (hi_lo : Δ < c.state.fst.val) (hi_hi : c.state.fst.val < 2 * Δ + 1)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    ((TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) c).tape = c.tape := by
  obtain ⟨hphase, hbit, hmove⟩ :=
    transition_seeking_left Δ b (i := c.state.fst) hi_lo hi_hi
      c.state.snd (c.tape c.head)
  have hmove_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.left := hmove
  have hbit_step :
      (((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((writeAtOffsetProgram Δ b).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state]; exact hphase_step
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-- j-fold invariant for the seek-left block, starting from any
configuration at phase Δ+1 with head ≥ Δ. -/
theorem run_j_seeking_left (Δ : Nat) (b : Bool) {n : Nat}
    (c_start : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (h_phase : c_start.state.fst.val = Δ + 1)
    (h_head_ge : Δ ≤ (c_start.head : ℕ)) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c_start j
    cj.state.fst.val = Δ + 1 + j ∧
    ((cj.head : ℕ) = (c_start.head : ℕ) - j) ∧
    cj.tape = c_start.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show c_start.state.fst.val = Δ + 1 + 0; rw [h_phase]
    · show (c_start.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c_start j'
      with hcj'
    have h_phase_lo : Δ < cj'.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cj'.state.fst.val < 2 * Δ + 1 := by rw [ih_phase]; omega
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_head, rip_tape⟩ :=
      stepConfig_seeking_left Δ b cj' h_phase_lo h_phase_hi h_head_pos
    have hrw :
        TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c_start (j' + 1) =
          TM.stepConfig (M := (writeAtOffsetProgram Δ b).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]; omega
    · rw [hrw, rip_head, ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- **Full correctness of `writeAtOffsetProgram`**: starting from
any configuration at phase 0, after the full `2Δ+1`-step budget:

* state is `2Δ+1` (accepting),
* head is back at `c.head`,
* the tape has bit `b` written at position `c.head + Δ`, everything
  else unchanged.
-/
theorem writeAtOffsetProgram_run_full (Δ : Nat) (b : Bool) {n : Nat}
    (c : Configuration (M := (writeAtOffsetProgram Δ b).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + Δ <
        (writeAtOffsetProgram Δ b).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (2 * Δ + 1)
    cfinal.state.fst.val = 2 * Δ + 1 ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δ, h_bound⟩ b := by
  -- Compose: runConfig c (2Δ+1) = runConfig (runConfig c (Δ+1)) Δ.
  have hsplit : 2 * Δ + 1 = (Δ + 1) + Δ := by omega
  have hcomp :
      TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (2 * Δ + 1) =
        TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM)
          (TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (Δ + 1)) Δ := by
    rw [hsplit, runConfig_add]
  obtain ⟨mid_phase, mid_head, mid_tape⟩ :=
    run_after_write_phase Δ b c h_phase h_bound
  set cmid := TM.runConfig (M := (writeAtOffsetProgram Δ b).toTM) c (Δ + 1)
    with hcmid
  -- After write: phase = Δ+1, head = c.head + Δ, tape = c.write ⟨c.head+Δ, _⟩ b.
  have h_phase_mid : cmid.state.fst.val = Δ + 1 := mid_phase
  have h_head_mid : (cmid.head : ℕ) = (c.head : ℕ) + Δ := mid_head
  have h_head_ge : Δ ≤ (cmid.head : ℕ) := by rw [h_head_mid]; omega
  have h_tape_mid : cmid.tape = c.write ⟨(c.head : ℕ) + Δ, h_bound⟩ b :=
    mid_tape h_bound
  -- Apply seek-left j-fold at j = Δ.
  obtain ⟨left_phase, left_head, left_tape⟩ :=
    run_j_seeking_left Δ b cmid h_phase_mid h_head_ge Δ le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomp, left_phase]; omega
  · rw [hcomp]
    apply Fin.ext
    show (_ : ℕ) = (c.head : ℕ)
    rw [left_head, h_head_mid]; omega
  · rw [hcomp, left_tape, h_tape_mid]

end WriteAtOffset

/-!
## Session 9e-d (step 7): `readAtOffsetProgram` compound

`readAtOffsetProgram Δ`: seek head right by `Δ`, read the bit there
into state, seek head back left by `Δ`.  Returns head to original
position.  The compiled TM accepts iff the read bit is `true`.

Uses `Bool` state throughout to carry the read value from the
read phase through the return trip.

Phases (analogous to writeAtOffsetProgram):
* 0..Δ-1: seek right, propagate state.
* Δ: read phase — new state = scanned bit.
* Δ+1..2Δ: seek left, propagate state.
* 2Δ+1: accepting idle (state unchanged).
-/

namespace ReadAtOffset

/-- Read-at-offset compound with `Bool` state. -/
def readAtOffsetProgram (Δ : Nat) : PhasedProgram.{0} where
  numPhases := 2 * Δ + 2
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := false
  acceptPhase := ⟨2 * Δ + 1, by omega⟩
  acceptState := true
  transition := fun i q scan =>
    if hi1 : i.val < Δ then
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi2 : i.val = Δ then
      (⟨⟨Δ + 1, by omega⟩, scan⟩, scan, Move.stay)
    else if hi3 : i.val < 2 * Δ + 1 then
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.left)
    else
      (⟨⟨2 * Δ + 1, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 2 * Δ + 1

@[simp] theorem readAtOffsetProgram_numPhases (Δ : Nat) :
    (readAtOffsetProgram Δ).numPhases = 2 * Δ + 2 := rfl

@[simp] theorem readAtOffsetProgram_timeBound (Δ n : Nat) :
    (readAtOffsetProgram Δ).timeBound n = 2 * Δ + 1 := rfl

/-! ### Transition helpers -/

theorem transition_seeking_right (Δ : Nat)
    {i : Fin ((readAtOffsetProgram Δ).numPhases)} (hi : i.val < Δ)
    (q : (readAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((readAtOffsetProgram Δ).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((readAtOffsetProgram Δ).transition i q scan).fst.snd = q ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.snd = Move.right := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [readAtOffsetProgram, hi]

theorem transition_read (Δ : Nat)
    {i : Fin ((readAtOffsetProgram Δ).numPhases)} (hi : i.val = Δ)
    (q : (readAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((readAtOffsetProgram Δ).transition i q scan).fst.fst.val = Δ + 1 ∧
    ((readAtOffsetProgram Δ).transition i q scan).fst.snd = scan ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.snd = Move.stay := by
  have hni : ¬ i.val < Δ := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [readAtOffsetProgram, hni, hi]

theorem transition_seeking_left (Δ : Nat)
    {i : Fin ((readAtOffsetProgram Δ).numPhases)}
    (hi_lo : Δ < i.val) (hi_hi : i.val < 2 * Δ + 1)
    (q : (readAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((readAtOffsetProgram Δ).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((readAtOffsetProgram Δ).transition i q scan).fst.snd = q ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((readAtOffsetProgram Δ).transition i q scan).snd.snd = Move.left := by
  have hn1 : ¬ i.val < Δ := by omega
  have hn2 : ¬ i.val = Δ := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [readAtOffsetProgram, hn1, hn2, hi_hi]

/-! ### Seek-right block invariant -/

theorem run_after_j_right_steps (Δ : Nat) {n : Nat}
    (c : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (readAtOffsetProgram Δ).toTM.tapeLength n) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c j
    cj.state.fst.val = j ∧
    cj.state.snd = false ∧
    ((cj.head : ℕ) = (c.head : ℕ) + j) ∧
    cj.tape = c.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show c.state.snd = false; exact h_state_snd
    · show (c.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c j' with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ := by rw [ih_phase]; exact hj'_lt_Δ
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (readAtOffsetProgram Δ).toTM.tapeLength n := by
      rw [ih_head]; omega
    -- Get transition behaviour
    obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
      transition_seeking_right Δ h_phase_cj' cj'.state.snd (cj'.tape cj'.head)
    have hmove_step :
        (((readAtOffsetProgram Δ).toTM.step cj'.state (cj'.tape cj'.head)).snd.snd :
          Move) = Move.right := t_move
    have hbit_step :
        (((readAtOffsetProgram Δ).toTM.step cj'.state (cj'.tape cj'.head)).snd.fst :
          Bool) = cj'.tape cj'.head := t_bit
    -- Compute step results
    have hrw :
        TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (j' + 1) =
          TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, stepConfig_state]
      show (((readAtOffsetProgram Δ).transition cj'.state.fst cj'.state.snd
              (cj'.tape cj'.head)).fst).fst.val = j' + 1
      rw [t_phase, ih_phase]
    · rw [hrw, stepConfig_state]
      show (((readAtOffsetProgram Δ).transition cj'.state.fst cj'.state.snd
              (cj'.tape cj'.head)).fst).snd = false
      rw [t_state, ih_state]
    · rw [hrw, stepConfig_head, hmove_step]
      rw [Configuration.moveHead_right_lt (c := cj') h_head_advance_bound]
      show cj'.head.val + 1 = c.head.val + (j' + 1)
      omega
    · rw [hrw, stepConfig_tape, hbit_step]
      rw [BinaryCounter.write_self_eq cj' cj'.head]
      exact ih_tape

/-! ### Read-phase step + combined after-read-phase invariant -/

/-- One stepConfig at phase Δ: new state.snd = scanned bit, head
stays, tape unchanged, phase → Δ+1. -/
theorem stepConfig_read (Δ : Nat) {n : Nat}
    (c : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (hi : c.state.fst.val = Δ) :
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).state.fst.val = Δ + 1 ∧
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).state.snd =
        c.tape c.head ∧
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_read Δ (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((readAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := t_move
  have hbit_step :
      (((readAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((readAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = Δ + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((readAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = c.tape c.head
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-- After `Δ + 1` total steps: seek-right block done, read phase
committed.  Now at phase `Δ+1`, head at `c.head + Δ`, state carries
the bit at offset Δ, tape unchanged. -/
theorem run_after_read_phase (Δ : Nat) {n : Nat}
    (c : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (readAtOffsetProgram Δ).toTM.tapeLength n) :
    let cmid := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (Δ + 1)
    cmid.state.fst.val = Δ + 1 ∧
    cmid.state.snd = c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩ ∧
    ((cmid.head : ℕ) = (c.head : ℕ) + Δ) ∧
    cmid.tape = c.tape := by
  obtain ⟨right_phase, right_state, right_head, right_tape⟩ :=
    run_after_j_right_steps Δ c h_phase h_state_snd h_bound Δ le_rfl
  set cΔ := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c Δ with hcΔ
  have h_phase_cΔ : cΔ.state.fst.val = Δ := right_phase
  obtain ⟨rd_phase, rd_state, rd_head, rd_tape⟩ := stepConfig_read Δ cΔ h_phase_cΔ
  have hrw :
      TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (Δ + 1) =
        TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) cΔ := by
    rw [runConfig_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrw]; exact rd_phase
  · -- cmid.state.snd = cΔ.tape cΔ.head = c.tape (at position c.head + Δ).
    rw [hrw, rd_state, right_tape]
    have h_head_eq : cΔ.head = (⟨(c.head : ℕ) + Δ, h_bound⟩ :
        Fin ((readAtOffsetProgram Δ).toTM.tapeLength n)) := by
      apply Fin.ext; exact right_head
    rw [h_head_eq]
  · rw [hrw, rd_head, right_head]
  · rw [hrw, rd_tape, right_tape]

/-! ### Seek-left block + full correctness -/

/-- One stepConfig in seek-left block of readAtOffsetProgram
(phase Δ+1..2Δ) with head > 0: phase advances, head decrements,
state/tape unchanged. -/
theorem stepConfig_seeking_left (Δ : Nat) {n : Nat}
    (c : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (hi_lo : Δ < c.state.fst.val) (hi_hi : c.state.fst.val < 2 * Δ + 1)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seeking_left Δ hi_lo hi_hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((readAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.left := t_move
  have hbit_step :
      (((readAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((readAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((readAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-- j-fold seek-left invariant, starting from any config at phase
Δ+1 with head ≥ Δ. -/
theorem run_j_seeking_left (Δ : Nat) {n : Nat}
    (c_start : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (h_phase : c_start.state.fst.val = Δ + 1)
    (h_head_ge : Δ ≤ (c_start.head : ℕ)) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c_start j
    cj.state.fst.val = Δ + 1 + j ∧
    cj.state.snd = c_start.state.snd ∧
    ((cj.head : ℕ) = (c_start.head : ℕ) - j) ∧
    cj.tape = c_start.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c_start.state.fst.val = Δ + 1 + 0; rw [h_phase]
    · rfl
    · show (c_start.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c_start j'
      with hcj'
    have h_phase_lo : Δ < cj'.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cj'.state.fst.val < 2 * Δ + 1 := by rw [ih_phase]; omega
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seeking_left Δ cj' h_phase_lo h_phase_hi h_head_pos
    have hrw :
        TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c_start (j' + 1) =
          TM.stepConfig (M := (readAtOffsetProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]; omega
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val - 1 = c_start.head.val - (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- **Full correctness of `readAtOffsetProgram`**: after the full
`2Δ+1`-step execution from phase 0 with startState = false:

* accepting phase (state.fst.val = 2Δ+1),
* state.snd carries the bit at offset Δ from the original head,
* head is back at c.head,
* tape unchanged.

The compiled TM's `accepts` returns the bit at offset Δ. -/
theorem readAtOffsetProgram_run_full (Δ : Nat) {n : Nat}
    (c : Configuration (M := (readAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (readAtOffsetProgram Δ).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (2 * Δ + 1)
    cfinal.state.fst.val = 2 * Δ + 1 ∧
    cfinal.state.snd = c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩ ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.tape := by
  have hsplit : 2 * Δ + 1 = (Δ + 1) + Δ := by omega
  have hcomp :
      TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (2 * Δ + 1) =
        TM.runConfig (M := (readAtOffsetProgram Δ).toTM)
          (TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (Δ + 1)) Δ := by
    rw [hsplit, runConfig_add]
  obtain ⟨mid_phase, mid_state, mid_head, mid_tape⟩ :=
    run_after_read_phase Δ c h_phase h_state_snd h_bound
  set cmid := TM.runConfig (M := (readAtOffsetProgram Δ).toTM) c (Δ + 1)
    with hcmid
  have h_phase_mid : cmid.state.fst.val = Δ + 1 := mid_phase
  have h_head_mid : (cmid.head : ℕ) = (c.head : ℕ) + Δ := mid_head
  have h_head_ge : Δ ≤ (cmid.head : ℕ) := by rw [h_head_mid]; omega
  obtain ⟨left_phase, left_state, left_head, left_tape⟩ :=
    run_j_seeking_left Δ cmid h_phase_mid h_head_ge Δ le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcomp, left_phase]; omega
  · rw [hcomp, left_state, mid_state]
  · rw [hcomp]
    apply Fin.ext
    show (_ : ℕ) = (c.head : ℕ)
    rw [left_head, h_head_mid]; omega
  · rw [hcomp, left_tape, mid_tape]

end ReadAtOffset

/-!
## Session 9e-d (step 8): `notAtOffsetProgram` compound

`notAtOffsetProgram Δ`: read bit at offset Δ, negate it in state,
write the negated bit back at the same position, return head.

This is the first "read + modify + write" compound — the core
pattern for single-input gate evaluators (`.not` in SLGate).

Phases:
* 0..Δ-1: seek right (Δ phases).
* Δ: read-negate — state.snd := !scan; stay.
* Δ+1: write state.snd at current cell; stay.
* Δ+2..2Δ+1: seek left (Δ phases).
* 2Δ+2: accepting idle.

Total phases: 2Δ+3.  runTime: 2Δ+2.
-/

namespace NotAtOffset

def notAtOffsetProgram (Δ : Nat) : PhasedProgram.{0} where
  numPhases := 2 * Δ + 3
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := false
  acceptPhase := ⟨2 * Δ + 2, by omega⟩
  acceptState := false
  transition := fun i q scan =>
    if hi1 : i.val < Δ then
      -- seek right
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi2 : i.val = Δ then
      -- read-negate phase: state := !scan
      (⟨⟨Δ + 1, by omega⟩, !scan⟩, scan, Move.stay)
    else if hi3 : i.val = Δ + 1 then
      -- write state.snd at current cell
      (⟨⟨Δ + 2, by omega⟩, q⟩, q, Move.stay)
    else if hi4 : i.val < 2 * Δ + 2 then
      -- seek left
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.left)
    else
      -- accepting idle
      (⟨⟨2 * Δ + 2, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 2 * Δ + 2

@[simp] theorem notAtOffsetProgram_numPhases (Δ : Nat) :
    (notAtOffsetProgram Δ).numPhases = 2 * Δ + 3 := rfl

@[simp] theorem notAtOffsetProgram_timeBound (Δ n : Nat) :
    (notAtOffsetProgram Δ).timeBound n = 2 * Δ + 2 := rfl

/-! ### Transition helpers -/

theorem transition_seeking_right (Δ : Nat)
    {i : Fin ((notAtOffsetProgram Δ).numPhases)} (hi : i.val < Δ)
    (q : (notAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((notAtOffsetProgram Δ).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((notAtOffsetProgram Δ).transition i q scan).fst.snd = q ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.snd = Move.right := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [notAtOffsetProgram, hi]

theorem transition_read_negate (Δ : Nat)
    {i : Fin ((notAtOffsetProgram Δ).numPhases)} (hi : i.val = Δ)
    (q : (notAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((notAtOffsetProgram Δ).transition i q scan).fst.fst.val = Δ + 1 ∧
    ((notAtOffsetProgram Δ).transition i q scan).fst.snd = !scan ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.snd = Move.stay := by
  have hni : ¬ i.val < Δ := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [notAtOffsetProgram, hni, hi]

theorem transition_write_state (Δ : Nat)
    {i : Fin ((notAtOffsetProgram Δ).numPhases)} (hi : i.val = Δ + 1)
    (q : (notAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((notAtOffsetProgram Δ).transition i q scan).fst.fst.val = Δ + 2 ∧
    ((notAtOffsetProgram Δ).transition i q scan).fst.snd = q ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.fst = q ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.snd = Move.stay := by
  have hn1 : ¬ i.val < Δ := by omega
  have hn2 : ¬ i.val = Δ := by omega
  have hn3 : ¬ (Δ + 1 < Δ) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [notAtOffsetProgram, hn1, hn2, hi, hn3]

theorem transition_seeking_left (Δ : Nat)
    {i : Fin ((notAtOffsetProgram Δ).numPhases)}
    (hi_lo : Δ + 1 < i.val) (hi_hi : i.val < 2 * Δ + 2)
    (q : (notAtOffsetProgram Δ).phaseState i) (scan : Bool) :
    ((notAtOffsetProgram Δ).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((notAtOffsetProgram Δ).transition i q scan).fst.snd = q ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.fst = scan ∧
    ((notAtOffsetProgram Δ).transition i q scan).snd.snd = Move.left := by
  have hn1 : ¬ i.val < Δ := by omega
  have hn2 : ¬ i.val = Δ := by omega
  have hn3 : ¬ i.val = Δ + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [notAtOffsetProgram, hn1, hn2, hn3, hi_hi]

/-! ### Step lemmas -/

theorem stepConfig_seeking_right (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (hi : c.state.fst.val < Δ)
    (h_head_bound : (c.head : ℕ) + 1 <
        (notAtOffsetProgram Δ).toTM.tapeLength n) :
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seeking_right Δ (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.right := t_move
  have hbit_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_read_negate (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (hi : c.state.fst.val = Δ) :
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.fst.val = Δ + 1 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.snd =
        !(c.tape c.head) ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_read_negate Δ (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := t_move
  have hbit_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = Δ + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = !(c.tape c.head)
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_write_state (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (hi : c.state.fst.val = Δ + 1) :
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.fst.val = Δ + 2 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.snd =
        c.state.snd ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).tape =
        c.write c.head c.state.snd := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_write_state Δ (i := c.state.fst) hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := t_move
  have hbit_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.state.snd := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = Δ + 2
    exact t_phase
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]

theorem stepConfig_seeking_left (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (hi_lo : Δ + 1 < c.state.fst.val) (hi_hi : c.state.fst.val < 2 * Δ + 2)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seeking_left Δ hi_lo hi_hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.left := t_move
  have hbit_step :
      (((notAtOffsetProgram Δ).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((notAtOffsetProgram Δ).transition c.state.fst c.state.snd
            (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-! ### j-fold right-block invariant -/

theorem run_after_j_right_steps (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (notAtOffsetProgram Δ).toTM.tapeLength n) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c j
    cj.state.fst.val = j ∧
    cj.state.snd = false ∧
    ((cj.head : ℕ) = (c.head : ℕ) + j) ∧
    cj.tape = c.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show c.state.snd = false; exact h_state_snd
    · show (c.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c j' with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ := by rw [ih_phase]; exact hj'_lt_Δ
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (notAtOffsetProgram Δ).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seeking_right Δ cj' h_phase_cj' h_head_advance_bound
    have hrw :
        TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (j' + 1) =
          TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val + 1 = c.head.val + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-! ### Combined: after Δ+2 total steps (right block + read + write) -/

theorem run_after_modify_phases (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (notAtOffsetProgram Δ).toTM.tapeLength n) :
    let cmid := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (Δ + 2)
    cmid.state.fst.val = Δ + 2 ∧
    cmid.state.snd = !(c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩) ∧
    ((cmid.head : ℕ) = (c.head : ℕ) + Δ) ∧
    cmid.tape = c.write ⟨(c.head : ℕ) + Δ, h_bound⟩
                  (!(c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩)) := by
  -- After Δ steps: right block invariant.
  obtain ⟨right_phase, right_state, right_head, right_tape⟩ :=
    run_after_j_right_steps Δ c h_phase h_state_snd h_bound Δ le_rfl
  set cΔ := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c Δ with hcΔ
  -- After 1 more step (read-negate): state.snd = !cΔ.tape cΔ.head.
  have h_phase_cΔ : cΔ.state.fst.val = Δ := right_phase
  obtain ⟨rd_phase, rd_state, rd_head, rd_tape⟩ :=
    stepConfig_read_negate Δ cΔ h_phase_cΔ
  set cΔ1 := TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) cΔ with hcΔ1
  have h_rewrite1 :
      TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (Δ + 1) = cΔ1 := by
    rw [show Δ + 1 = Δ + 1 from rfl, runConfig_succ]
  -- After 1 more step (write-state): tape := cΔ1.write cΔ1.head cΔ1.state.snd.
  have h_phase_cΔ1 : cΔ1.state.fst.val = Δ + 1 := rd_phase
  obtain ⟨wr_phase, wr_state, wr_head, wr_tape⟩ :=
    stepConfig_write_state Δ cΔ1 h_phase_cΔ1
  have h_rewrite2 :
      TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (Δ + 2) =
        TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) cΔ1 := by
    rw [show Δ + 2 = Δ + 1 + 1 from rfl, runConfig_succ, h_rewrite1]
  -- Position-level identification: cΔ.head = ⟨c.head + Δ, h_bound⟩.
  have h_head_fin :
      cΔ.head = (⟨(c.head : ℕ) + Δ, h_bound⟩ :
        Fin ((notAtOffsetProgram Δ).toTM.tapeLength n)) := by
    apply Fin.ext; exact right_head
  -- And cΔ1.head = cΔ.head (read-negate didn't move).
  have h_head_cΔ1 : cΔ1.head = cΔ.head := rd_head
  -- cΔ1.tape = cΔ.tape = c.tape (read-negate didn't change tape, right block didn't).
  have h_tape_cΔ1 : cΔ1.tape = c.tape := by rw [hcΔ1, rd_tape, right_tape]
  -- cΔ1.state.snd = !(cΔ.tape cΔ.head) = !(c.tape at position c.head+Δ).
  have h_state_cΔ1 : cΔ1.state.snd = !(c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩) := by
    rw [hcΔ1, rd_state, right_tape, h_head_fin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_rewrite2]; exact wr_phase
  · rw [h_rewrite2, wr_state]; exact h_state_cΔ1
  · rw [h_rewrite2, wr_head]
    show (cΔ1.head : ℕ) = (c.head : ℕ) + Δ
    rw [h_head_cΔ1]; exact right_head
  · rw [h_rewrite2, wr_tape]
    -- Goal: cΔ1.write cΔ1.head cΔ1.state.snd = c.write ⟨c.head+Δ, _⟩ (!(c.tape at..))
    rw [h_head_cΔ1, h_head_fin, h_state_cΔ1]
    funext j
    unfold Configuration.write
    split_ifs with hj
    · rfl
    · rw [h_tape_cΔ1]

/-! ### j-fold seek-left invariant -/

theorem run_j_seeking_left (Δ : Nat) {n : Nat}
    (c_start : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (h_phase : c_start.state.fst.val = Δ + 2)
    (h_head_ge : Δ ≤ (c_start.head : ℕ)) :
    ∀ j, j ≤ Δ →
    let cj := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c_start j
    cj.state.fst.val = Δ + 2 + j ∧
    cj.state.snd = c_start.state.snd ∧
    ((cj.head : ℕ) = (c_start.head : ℕ) - j) ∧
    cj.tape = c_start.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c_start.state.fst.val = Δ + 2 + 0; rw [h_phase]
    · rfl
    · show (c_start.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le_Δ : j' ≤ Δ := by omega
    have hj'_lt_Δ : j' < Δ := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le_Δ
    set cj' := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c_start j'
      with hcj'
    have h_phase_lo : Δ + 1 < cj'.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cj'.state.fst.val < 2 * Δ + 2 := by rw [ih_phase]; omega
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seeking_left Δ cj' h_phase_lo h_phase_hi h_head_pos
    have hrw :
        TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c_start (j' + 1) =
          TM.stepConfig (M := (notAtOffsetProgram Δ).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]; omega
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val - 1 = c_start.head.val - (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- **Full correctness of `notAtOffsetProgram`**: starting from phase 0
with startState = false and head + Δ in bounds, after the full
2Δ+2-step budget:
* phase = 2Δ+2 (accepting),
* state.snd = !(c.tape at c.head+Δ),
* head returned to c.head,
* tape has bit at offset Δ flipped to its negation.
-/
theorem notAtOffsetProgram_run_full (Δ : Nat) {n : Nat}
    (c : Configuration (M := (notAtOffsetProgram Δ).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δ <
        (notAtOffsetProgram Δ).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (2 * Δ + 2)
    cfinal.state.fst.val = 2 * Δ + 2 ∧
    cfinal.state.snd = !(c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩) ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δ, h_bound⟩
                    (!(c.tape ⟨(c.head : ℕ) + Δ, h_bound⟩)) := by
  have hsplit : 2 * Δ + 2 = (Δ + 2) + Δ := by omega
  have hcomp :
      TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (2 * Δ + 2) =
        TM.runConfig (M := (notAtOffsetProgram Δ).toTM)
          (TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (Δ + 2)) Δ := by
    rw [hsplit, runConfig_add]
  obtain ⟨mid_phase, mid_state, mid_head, mid_tape⟩ :=
    run_after_modify_phases Δ c h_phase h_state_snd h_bound
  set cmid := TM.runConfig (M := (notAtOffsetProgram Δ).toTM) c (Δ + 2)
    with hcmid
  have h_phase_mid : cmid.state.fst.val = Δ + 2 := mid_phase
  have h_head_mid : (cmid.head : ℕ) = (c.head : ℕ) + Δ := mid_head
  have h_head_ge : Δ ≤ (cmid.head : ℕ) := by rw [h_head_mid]; omega
  obtain ⟨left_phase, left_state, left_head, left_tape⟩ :=
    run_j_seeking_left Δ cmid h_phase_mid h_head_ge Δ le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcomp, left_phase]; omega
  · rw [hcomp, left_state]; exact mid_state
  · rw [hcomp]
    apply Fin.ext
    show (_ : ℕ) = (c.head : ℕ)
    rw [left_head, h_head_mid]; omega
  · rw [hcomp, left_tape]; exact mid_tape

end NotAtOffset

/-!
## Session 9e-d (step 9): `copyAtOffsetProgram` compound

`copyAtOffsetProgram Δsrc Δdst` (with `Δsrc ≤ Δdst`): read the bit
at offset `Δsrc` from the initial head, then write that bit at
offset `Δdst`, then return the head.

This is the cross-position analogue of `notAtOffsetProgram` and
the first compound with SEPARATE read/write positions.  It is the
core primitive for SL-gate evaluation where the result of reading
one scratch cell must be written to a different scratch cell.

5-block structure (assuming `Δsrc ≤ Δdst`):
* 0..Δsrc-1: seek right to source.
* Δsrc: read source bit into state.
* Δsrc+1..Δdst: seek right from source to destination.
* Δdst+1: write state bit at destination.
* Δdst+2..2Δdst+1: seek left back to origin.
* 2Δdst+2: accepting.

Total phases: `2Δdst+3`.  runTime: `2Δdst+2`.
-/

end TM

end PsubsetPpoly
end Internal
end Pnp3
