import Complexity.PsubsetPpolyInternal.TuringToolkit.UnaryAtOffset

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM


namespace CopyAtOffset

def copyAtOffsetProgram (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) :
    PhasedProgram.{0} where
  numPhases := 2 * Δdst + 3
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := false
  acceptPhase := ⟨2 * Δdst + 2, by omega⟩
  acceptState := true
  transition := fun i q scan =>
    if hi1 : i.val < Δsrc then
      -- seek right to source
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi2 : i.val = Δsrc then
      -- read source bit into state
      (⟨⟨Δsrc + 1, by omega⟩, scan⟩, scan, Move.stay)
    else if hi3 : i.val < Δdst + 1 then
      -- seek right to destination (phase Δsrc+1..Δdst)
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi4 : i.val = Δdst + 1 then
      -- write state bit at destination
      (⟨⟨Δdst + 2, by omega⟩, q⟩, q, Move.stay)
    else if hi5 : i.val < 2 * Δdst + 2 then
      -- seek left back to origin (phase Δdst+2..2Δdst+1)
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.left)
    else
      -- accepting idle (phase 2Δdst+2)
      (⟨⟨2 * Δdst + 2, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 2 * Δdst + 2

@[simp] theorem copyAtOffsetProgram_numPhases (Δsrc Δdst : Nat)
    (hleq : Δsrc ≤ Δdst) :
    (copyAtOffsetProgram Δsrc Δdst hleq).numPhases = 2 * Δdst + 3 := rfl

@[simp] theorem copyAtOffsetProgram_timeBound (Δsrc Δdst : Nat)
    (hleq : Δsrc ≤ Δdst) (n : Nat) :
    (copyAtOffsetProgram Δsrc Δdst hleq).timeBound n = 2 * Δdst + 2 := rfl

/-! ### Transition helpers for the 5 phase classes -/

theorem transition_seek_to_src (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst)
    {i : Fin ((copyAtOffsetProgram Δsrc Δdst hleq).numPhases)} (hi : i.val < Δsrc)
    (q : (copyAtOffsetProgram Δsrc Δdst hleq).phaseState i) (scan : Bool) :
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.snd = q ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.fst = scan ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.snd = Move.right := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [copyAtOffsetProgram, hi]

theorem transition_read (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst)
    {i : Fin ((copyAtOffsetProgram Δsrc Δdst hleq).numPhases)} (hi : i.val = Δsrc)
    (q : (copyAtOffsetProgram Δsrc Δdst hleq).phaseState i) (scan : Bool) :
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.fst.val = Δsrc + 1 ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.snd = scan ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.fst = scan ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.snd = Move.stay := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [copyAtOffsetProgram, hi]

theorem transition_seek_to_dst (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst)
    {i : Fin ((copyAtOffsetProgram Δsrc Δdst hleq).numPhases)}
    (hi_lo : Δsrc < i.val) (hi_hi : i.val < Δdst + 1)
    (q : (copyAtOffsetProgram Δsrc Δdst hleq).phaseState i) (scan : Bool) :
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.snd = q ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.fst = scan ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.snd = Move.right := by
  have hn1 : ¬ i.val < Δsrc := by omega
  have hn2 : ¬ i.val = Δsrc := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [copyAtOffsetProgram, hn1, hn2, hi_hi]

theorem transition_write (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst)
    {i : Fin ((copyAtOffsetProgram Δsrc Δdst hleq).numPhases)} (hi : i.val = Δdst + 1)
    (q : (copyAtOffsetProgram Δsrc Δdst hleq).phaseState i) (scan : Bool) :
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.fst.val = Δdst + 2 ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.snd = q ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.fst = q ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.snd = Move.stay := by
  have hn4 : ¬ (Δdst + 1 < Δsrc) := by omega
  have hn5 : ¬ (Δdst + 1 = Δsrc) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [copyAtOffsetProgram, hi, hn4, hn5]

theorem transition_seek_back (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst)
    {i : Fin ((copyAtOffsetProgram Δsrc Δdst hleq).numPhases)}
    (hi_lo : Δdst + 1 < i.val) (hi_hi : i.val < 2 * Δdst + 2)
    (q : (copyAtOffsetProgram Δsrc Δdst hleq).phaseState i) (scan : Bool) :
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.fst.val = i.val + 1 ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).fst.snd = q ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.fst = scan ∧
    ((copyAtOffsetProgram Δsrc Δdst hleq).transition i q scan).snd.snd = Move.left := by
  have hn1 : ¬ i.val < Δsrc := by omega
  have hn2 : ¬ i.val = Δsrc := by omega
  have hn3 : ¬ i.val < Δdst + 1 := by omega
  have hn4 : ¬ i.val = Δdst + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [copyAtOffsetProgram, hn1, hn2, hn3, hn4, hi_hi]

/-! ### Step lemmas -/

theorem stepConfig_seek_to_src (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (hi : c.state.fst.val < Δsrc)
    (h_head_bound : (c.head : ℕ) + 1 <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_to_src Δsrc Δdst hleq (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.right := t_move
  have hbit_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_read (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (hi : c.state.fst.val = Δsrc) :
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.fst.val =
        Δsrc + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.snd =
        c.tape c.head ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_read Δsrc Δdst hleq (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.stay := t_move
  have hbit_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = Δsrc + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.tape c.head
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_seek_to_dst (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (hi_lo : Δsrc < c.state.fst.val) (hi_hi : c.state.fst.val < Δdst + 1)
    (h_head_bound : (c.head : ℕ) + 1 <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_to_dst Δsrc Δdst hleq hi_lo hi_hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.right := t_move
  have hbit_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_write (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (hi : c.state.fst.val = Δdst + 1) :
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.fst.val =
        Δdst + 2 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.snd =
        c.state.snd ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).tape =
        c.write c.head c.state.snd := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_write Δsrc Δdst hleq (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.stay := t_move
  have hbit_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.state.snd := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = Δdst + 2
    exact t_phase
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]

theorem stepConfig_seek_back (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (hi_lo : Δdst + 1 < c.state.fst.val) (hi_hi : c.state.fst.val < 2 * Δdst + 2)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_back Δsrc Δdst hleq hi_lo hi_hi c.state.snd (c.tape c.head)
  have hmove_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.left := t_move
  have hbit_step :
      (((copyAtOffsetProgram Δsrc Δdst hleq).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((copyAtOffsetProgram Δsrc Δdst hleq).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-! ### Block A: j-fold invariant for seek-to-src -/

theorem run_after_j_seek_to_src_steps (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δdst <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    ∀ j, j ≤ Δsrc →
    let cj := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c j
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
    have hj'_le_src : j' ≤ Δsrc := by omega
    have hj'_lt_src : j' < Δsrc := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le_src
    set cj' := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c j'
      with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δsrc := by rw [ih_phase]; exact hj'_lt_src
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 <
          (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seek_to_src Δsrc Δdst hleq cj' h_phase_cj' h_head_advance_bound
    have hrw :
        TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (j' + 1) =
          TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val + 1 = c.head.val + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-! ### Read + Block B: j-fold after read phase -/

theorem run_after_j_seek_to_dst_steps (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c_start : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (_h_phase : c_start.state.fst.val = Δsrc + 1)
    (_h_head_start : (c_start.head : ℕ) = 0 + Δsrc) -- dummy for now, generalized below
    : True := trivial  -- placeholder: we handle B via direct composition instead.

/-- Combined: `run_after_j_steps_and_read_then_seek_to_dst`.  After
`Δsrc + 1 + j` total steps (0 ≤ j ≤ Δdst - Δsrc), we are at phase
`Δsrc + 1 + j`, state.snd = bit read at src, head at c.head + Δsrc + j,
tape unchanged. -/
theorem run_after_j_extra_right_steps (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δdst <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n)
    (h_src_bound : (c.head : ℕ) + Δsrc <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    ∀ j, j ≤ Δdst - Δsrc →
    let ctotal := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
        (Δsrc + 1 + j)
    ctotal.state.fst.val = Δsrc + 1 + j ∧
    ctotal.state.snd = c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ ∧
    ((ctotal.head : ℕ) = (c.head : ℕ) + Δsrc + j) ∧
    ctotal.tape = c.tape := by
  intro j hj
  -- Base structure: first Δsrc + 1 steps = Block A + read.  Then j more = Block B prefix.
  -- After Block A (Δsrc steps): phase Δsrc, head c.head+Δsrc, state false, tape c.tape.
  obtain ⟨A_phase, A_state, A_head, A_tape⟩ :=
    run_after_j_seek_to_src_steps Δsrc Δdst hleq c h_phase h_state_snd h_bound
      Δsrc le_rfl
  set cA := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c Δsrc
    with hcA
  -- One more step (read phase): phase Δsrc+1, state = c.tape at c.head+Δsrc, head unchanged, tape unchanged.
  have h_phase_cA : cA.state.fst.val = Δsrc := A_phase
  obtain ⟨rd_phase, rd_state, rd_head, rd_tape⟩ :=
    stepConfig_read Δsrc Δdst hleq cA h_phase_cA
  have h_rewrite_src_plus_one :
      TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δsrc + 1) =
        TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) cA := by
    rw [runConfig_succ]
  -- Now compose j more steps of Block B.
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δsrc + 1 + 0)).state.fst.val = Δsrc + 1 + 0
      rw [show Δsrc + 1 + 0 = Δsrc + 1 from by omega, h_rewrite_src_plus_one]
      exact rd_phase
    · show (TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δsrc + 1 + 0)).state.snd =
           c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩
      rw [show Δsrc + 1 + 0 = Δsrc + 1 from by omega, h_rewrite_src_plus_one, rd_state, A_tape]
      have h_head_fin : cA.head = (⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ :
          Fin ((copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n)) := by
        apply Fin.ext; exact A_head
      rw [h_head_fin]
    · show ((TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δsrc + 1 + 0)).head : ℕ)
           = (c.head : ℕ) + Δsrc + 0
      rw [show Δsrc + 1 + 0 = Δsrc + 1 from by omega, h_rewrite_src_plus_one, rd_head]
      show (cA.head : ℕ) = _
      rw [A_head]; omega
    · show (TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δsrc + 1 + 0)).tape = c.tape
      rw [show Δsrc + 1 + 0 = Δsrc + 1 from by omega, h_rewrite_src_plus_one, rd_tape, A_tape]
  | succ j' ih =>
    have hj'_le : j' ≤ Δdst - Δsrc := by omega
    have hj'_lt : j' < Δdst - Δsrc := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cprev := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
        (Δsrc + 1 + j')
      with hcprev
    have h_phase_lo : Δsrc < cprev.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cprev.state.fst.val < Δdst + 1 := by rw [ih_phase]; omega
    have h_head_advance_bound :
        (cprev.head : ℕ) + 1 <
          (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨B_phase, B_state, B_head, B_tape⟩ :=
      stepConfig_seek_to_dst Δsrc Δdst hleq cprev h_phase_lo h_phase_hi
        h_head_advance_bound
    have hrw :
        TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
            (Δsrc + 1 + (j' + 1)) =
          TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) cprev := by
      rw [show Δsrc + 1 + (j' + 1) = (Δsrc + 1 + j') + 1 from by omega,
          runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, B_phase, ih_phase]; omega
    · rw [hrw, B_state, ih_state]
    · rw [hrw, B_head]
      show cprev.head.val + 1 = c.head.val + Δsrc + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, B_tape, ih_tape]

/-! ### After write phase: commits bit at dst -/

theorem run_after_write_phase (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δdst <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    let cmid := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
        (Δdst + 2)
    ∃ (h_src_bound : (c.head : ℕ) + Δsrc <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n),
    cmid.state.fst.val = Δdst + 2 ∧
    cmid.state.snd = c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ ∧
    ((cmid.head : ℕ) = (c.head : ℕ) + Δdst) ∧
    cmid.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                  (c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩) := by
  have h_src_bound : (c.head : ℕ) + Δsrc <
      (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n := by omega
  refine ⟨h_src_bound, ?_⟩
  -- After Δsrc + 1 + (Δdst - Δsrc) = Δdst + 1 total steps: at phase Δdst + 1,
  -- state = read bit at src, head = c.head + Δdst, tape unchanged.
  have hj_bound : Δdst - Δsrc ≤ Δdst - Δsrc := le_refl _
  obtain ⟨ext_phase, ext_state, ext_head, ext_tape⟩ :=
    run_after_j_extra_right_steps Δsrc Δdst hleq c h_phase h_state_snd h_bound
      h_src_bound (Δdst - Δsrc) hj_bound
  have h_total : Δsrc + 1 + (Δdst - Δsrc) = Δdst + 1 := by omega
  set cpre := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δdst + 1)
    with hcpre
  have h_rewrite_dst_plus_one :
      TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
          (Δsrc + 1 + (Δdst - Δsrc)) = cpre := by
    rw [h_total]
  have h_phase_cpre : cpre.state.fst.val = Δdst + 1 := by
    rw [← h_rewrite_dst_plus_one]; show _ = Δdst + 1
    rw [ext_phase]; omega
  have h_state_cpre : cpre.state.snd =
      c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ := by
    rw [← h_rewrite_dst_plus_one]; exact ext_state
  have h_head_cpre : (cpre.head : ℕ) = (c.head : ℕ) + Δdst := by
    rw [← h_rewrite_dst_plus_one]; show _ = _
    rw [ext_head]; omega
  have h_tape_cpre : cpre.tape = c.tape := by
    rw [← h_rewrite_dst_plus_one]; exact ext_tape
  -- One more step: write phase.
  obtain ⟨wr_phase, wr_state, wr_head, wr_tape⟩ :=
    stepConfig_write Δsrc Δdst hleq cpre h_phase_cpre
  have hrw_final :
      TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δdst + 2) =
        TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) cpre := by
    rw [show Δdst + 2 = (Δdst + 1) + 1 from by omega, runConfig_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrw_final]; exact wr_phase
  · rw [hrw_final, wr_state, h_state_cpre]
  · rw [hrw_final, wr_head]
    show (cpre.head : ℕ) = _; exact h_head_cpre
  · rw [hrw_final, wr_tape]
    have h_head_fin : cpre.head = (⟨(c.head : ℕ) + Δdst, h_bound⟩ :
        Fin ((copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n)) := by
      apply Fin.ext; exact h_head_cpre
    rw [h_head_fin, h_state_cpre]
    funext j
    unfold Configuration.write
    split_ifs with hj
    · rfl
    · rw [h_tape_cpre]

/-! ### Block C: j-fold seek-back invariant -/

theorem run_j_seek_back (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c_start : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (h_phase : c_start.state.fst.val = Δdst + 2)
    (h_head_ge : Δdst ≤ (c_start.head : ℕ)) :
    ∀ j, j ≤ Δdst →
    let cj := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c_start j
    cj.state.fst.val = Δdst + 2 + j ∧
    cj.state.snd = c_start.state.snd ∧
    ((cj.head : ℕ) = (c_start.head : ℕ) - j) ∧
    cj.tape = c_start.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c_start.state.fst.val = Δdst + 2 + 0; rw [h_phase]
    · rfl
    · show (c_start.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le : j' ≤ Δdst := by omega
    have hj'_lt : j' < Δdst := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cj' := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c_start j'
      with hcj'
    have h_phase_lo : Δdst + 1 < cj'.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cj'.state.fst.val < 2 * Δdst + 2 := by rw [ih_phase]; omega
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seek_back Δsrc Δdst hleq cj' h_phase_lo h_phase_hi h_head_pos
    have hrw :
        TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c_start (j' + 1) =
          TM.stepConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]; omega
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val - 1 = c_start.head.val - (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- **Full correctness of `copyAtOffsetProgram`**: after `2Δdst+2`
steps, the bit at `c.head + Δsrc` is copied to `c.head + Δdst`, head
returned to origin, all other tape cells preserved. -/
theorem copyAtOffsetProgram_run_full (Δsrc Δdst : Nat) (hleq : Δsrc ≤ Δdst) {n : Nat}
    (c : Configuration (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = false)
    (h_bound : (c.head : ℕ) + Δdst <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
        (2 * Δdst + 2)
    ∃ (h_src_bound : (c.head : ℕ) + Δsrc <
        (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n),
    cfinal.state.fst.val = 2 * Δdst + 2 ∧
    cfinal.state.snd = c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                    (c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩) := by
  have h_src_bound : (c.head : ℕ) + Δsrc <
      (copyAtOffsetProgram Δsrc Δdst hleq).toTM.tapeLength n := by omega
  refine ⟨h_src_bound, ?_⟩
  have hsplit : 2 * Δdst + 2 = (Δdst + 2) + Δdst := by omega
  have hcomp :
      TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (2 * Δdst + 2) =
        TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM)
          (TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c (Δdst + 2))
          Δdst := by
    rw [hsplit, runConfig_add]
  obtain ⟨h_src_bound', mid_phase, mid_state, mid_head, mid_tape⟩ :=
    run_after_write_phase Δsrc Δdst hleq c h_phase h_state_snd h_bound
  set cmid := TM.runConfig (M := (copyAtOffsetProgram Δsrc Δdst hleq).toTM) c
      (Δdst + 2)
    with hcmid
  have h_phase_mid : cmid.state.fst.val = Δdst + 2 := mid_phase
  have h_head_mid : (cmid.head : ℕ) = (c.head : ℕ) + Δdst := mid_head
  have h_head_ge : Δdst ≤ (cmid.head : ℕ) := by rw [h_head_mid]; omega
  -- Unify h_src_bound with h_src_bound'.
  have h_state_mid_rewritten :
      cmid.state.snd = c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩ := mid_state
  obtain ⟨left_phase, left_state, left_head, left_tape⟩ :=
    run_j_seek_back Δsrc Δdst hleq cmid h_phase_mid h_head_ge Δdst le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcomp, left_phase]; omega
  · rw [hcomp, left_state]; exact h_state_mid_rewritten
  · rw [hcomp]
    apply Fin.ext
    show (_ : ℕ) = (c.head : ℕ)
    rw [left_head, h_head_mid]; omega
  · rw [hcomp, left_tape, mid_tape]

end CopyAtOffset

end TM

end PsubsetPpoly
end Internal
end Pnp3
