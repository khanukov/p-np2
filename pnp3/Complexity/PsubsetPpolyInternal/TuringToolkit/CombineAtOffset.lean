import Complexity.PsubsetPpolyInternal.TuringToolkit.CopyAtOffset
import Complexity.PsubsetPpolyInternal.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM


/-! ## CombineAtOffset: 2-input gate compound

A parameterized compound that reads bits at offsets `Δ1` and `Δ2` from
the current head, combines them with a user-supplied boolean operation
`op : Bool → Bool → Bool`, and writes the result at offset `Δdst`
(head returns to origin).  Specialized to AND and OR below.

Preconditions: `Δ1 ≤ Δ2 ≤ Δdst`.

Phase layout (total `2*Δdst + 4` phases):
- `0..Δ1-1`: seek right from `c.head` to `c.head + Δ1`.
- `Δ1`: read bit at src1, store in `state.fst`.
- `Δ1+1..Δ2`: seek right to `c.head + Δ2`.
- `Δ2+1`: read bit at src2, store in `state.snd`.
- `Δ2+2..Δdst+1`: seek right to `c.head + Δdst`.
- `Δdst+2`: write `op state.fst state.snd` at destination.
- `Δdst+3..2Δdst+2`: seek left back to `c.head`.
- `2Δdst+3`: accept.

Time bound: `2*Δdst + 3`. -/

namespace CombineAtOffset

open Pnp3.Internal.PsubsetPpoly.TM

def combineAtOffsetProgram (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst)
    (op : Bool → Bool → Bool) :
    PhasedProgram.{0} where
  numPhases := 2 * Δdst + 4
  phaseState := fun _ => Bool × Bool
  instFin := fun _ => inferInstanceAs (Fintype (Bool × Bool))
  instDec := fun _ => inferInstanceAs (DecidableEq (Bool × Bool))
  startPhase := ⟨0, by omega⟩
  startState := (false, false)
  acceptPhase := ⟨2 * Δdst + 3, by omega⟩
  acceptState := (false, false)
  transition := fun i q scan =>
    if hi1 : i.val < Δ1 then
      -- seek right to src1
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi2 : i.val = Δ1 then
      -- read src1 into state.fst
      (⟨⟨Δ1 + 1, by omega⟩, (scan, q.snd)⟩, scan, Move.stay)
    else if hi3 : i.val < Δ2 + 1 then
      -- seek right to src2
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi4 : i.val = Δ2 + 1 then
      -- read src2 into state.snd
      (⟨⟨Δ2 + 2, by omega⟩, (q.fst, scan)⟩, scan, Move.stay)
    else if hi5 : i.val < Δdst + 2 then
      -- seek right to dst
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.right)
    else if hi6 : i.val = Δdst + 2 then
      -- write op q.fst q.snd at dst
      (⟨⟨Δdst + 3, by omega⟩, q⟩, op q.fst q.snd, Move.stay)
    else if hi7 : i.val < 2 * Δdst + 3 then
      -- seek left back
      (⟨⟨i.val + 1, by omega⟩, q⟩, scan, Move.left)
    else
      -- accept
      (⟨⟨2 * Δdst + 3, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 2 * Δdst + 3

@[simp] theorem combineAtOffsetProgram_numPhases (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) :
    (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases = 2 * Δdst + 4 := rfl

@[simp] theorem combineAtOffsetProgram_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) (n : Nat) :
    (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).timeBound n = 2 * Δdst + 3 := rfl

/-! ### Transition helpers for the 7 phase classes -/

theorem transition_seek_to_src1 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi : i.val < Δ1)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        i.val + 1 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd = q ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.right := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [combineAtOffsetProgram, hi]

theorem transition_read1 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi : i.val = Δ1)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        Δ1 + 1 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd =
        (scan, q.snd) ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.stay := by
  have hni : ¬ i.val < Δ1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [combineAtOffsetProgram, hni, hi]

theorem transition_seek_to_src2 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi_lo : Δ1 < i.val) (hi_hi : i.val < Δ2 + 1)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        i.val + 1 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd = q ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.right := by
  have hn1 : ¬ i.val < Δ1 := by omega
  have hn2 : ¬ i.val = Δ1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [combineAtOffsetProgram, hn1, hn2, hi_hi]

theorem transition_read2 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi : i.val = Δ2 + 1)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        Δ2 + 2 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd =
        (q.fst, scan) ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.stay := by
  have hn1 : ¬ i.val < Δ1 := by omega
  have hn2 : ¬ i.val = Δ1 := by omega
  have hn3 : ¬ i.val < Δ2 + 1 := by omega
  have hn1' : ¬ (Δ2 + 1 : Nat) < Δ1 := by omega
  have hn2' : ¬ (Δ2 + 1 : Nat) = Δ1 := by omega
  have hn3' : ¬ (Δ2 + 1 : Nat) < Δ2 + 1 := Nat.lt_irrefl _
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [combineAtOffsetProgram, hn1, hn2, hn3, hn1', hn2', hn3', hi]

theorem transition_seek_to_dst (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi_lo : Δ2 + 1 < i.val) (hi_hi : i.val < Δdst + 2)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        i.val + 1 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd = q ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.right := by
  have hn1 : ¬ i.val < Δ1 := by omega
  have hn2 : ¬ i.val = Δ1 := by omega
  have hn3 : ¬ i.val < Δ2 + 1 := by omega
  have hn4 : ¬ i.val = Δ2 + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [combineAtOffsetProgram, hn1, hn2, hn3, hn4, hi_hi]

theorem transition_write (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi : i.val = Δdst + 2)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        Δdst + 3 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd = q ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst =
        op q.fst q.snd ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.stay := by
  have hn1 : ¬ i.val < Δ1 := by omega
  have hn2 : ¬ i.val = Δ1 := by omega
  have hn3 : ¬ i.val < Δ2 + 1 := by omega
  have hn4 : ¬ i.val = Δ2 + 1 := by omega
  have hn5 : ¬ i.val < Δdst + 2 := by omega
  have hn1' : ¬ (Δdst + 2 : Nat) < Δ1 := by omega
  have hn2' : ¬ (Δdst + 2 : Nat) = Δ1 := by omega
  have hn3' : ¬ (Δdst + 2 : Nat) < Δ2 + 1 := by omega
  have hn4' : ¬ (Δdst + 2 : Nat) = Δ2 + 1 := by omega
  have hn5' : ¬ (Δdst + 2 : Nat) < Δdst + 2 := Nat.lt_irrefl _
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [combineAtOffsetProgram, hn1, hn2, hn3, hn4, hn5,
      hn1', hn2', hn3', hn4', hn5', hi]

theorem transition_seek_back (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool)
    {i : Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).numPhases)}
    (hi_lo : Δdst + 2 < i.val) (hi_hi : i.val < 2 * Δdst + 3)
    (q : (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).phaseState i)
    (scan : Bool) :
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.fst.val =
        i.val + 1 ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).fst.snd = q ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.fst = scan ∧
    ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition i q scan).snd.snd =
        Move.left := by
  have hn1 : ¬ i.val < Δ1 := by omega
  have hn2 : ¬ i.val = Δ1 := by omega
  have hn3 : ¬ i.val < Δ2 + 1 := by omega
  have hn4 : ¬ i.val = Δ2 + 1 := by omega
  have hn5 : ¬ i.val < Δdst + 2 := by omega
  have hn6 : ¬ i.val = Δdst + 2 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [combineAtOffsetProgram, hn1, hn2, hn3, hn4, hn5, hn6, hi_hi]

/-! ### Step lemmas -/

theorem stepConfig_seek_to_src1 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi : c.state.fst.val < Δ1)
    (h_head_bound : (c.head : ℕ) + 1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_to_src1 Δ1 Δ2 Δdst hle12 hle2d op (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.right := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_read1 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi : c.state.fst.val = Δ1) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        Δ1 + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        (c.tape c.head, c.state.snd.snd) ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_read1 Δ1 Δ2 Δdst hle12 hle2d op (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.stay := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = Δ1 + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = (c.tape c.head, c.state.snd.snd)
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_seek_to_src2 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi_lo : Δ1 < c.state.fst.val) (hi_hi : c.state.fst.val < Δ2 + 1)
    (h_head_bound : (c.head : ℕ) + 1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_to_src2 Δ1 Δ2 Δdst hle12 hle2d op hi_lo hi_hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.right := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_read2 (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi : c.state.fst.val = Δ2 + 1) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        Δ2 + 2 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        (c.state.snd.fst, c.tape c.head) ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_read2 Δ1 Δ2 Δdst hle12 hle2d op (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.stay := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = Δ2 + 2
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = (c.state.snd.fst, c.tape c.head)
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_seek_to_dst (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi_lo : Δ2 + 1 < c.state.fst.val) (hi_hi : c.state.fst.val < Δdst + 2)
    (h_head_bound : (c.head : ℕ) + 1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_to_dst Δ1 Δ2 Δdst hle12 hle2d op hi_lo hi_hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.right := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) h_head_bound]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

theorem stepConfig_write (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi : c.state.fst.val = Δdst + 2) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        Δdst + 3 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        c.state.snd ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape =
        c.write c.head (op c.state.snd.fst c.state.snd.snd) := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_write Δ1 Δ2 Δdst hle12 hle2d op (i := c.state.fst) hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.stay := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = op c.state.snd.fst c.state.snd.snd := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = Δdst + 3
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_tape, hbit_step]

theorem stepConfig_seek_back (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (hi_lo : Δdst + 2 < c.state.fst.val) (hi_hi : c.state.fst.val < 2 * Δdst + 3)
    (h_head_pos : 0 < (c.head : ℕ)) :
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.fst.val =
        c.state.fst.val + 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).state.snd =
        c.state.snd ∧
    ((TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).head : ℕ) =
        (c.head : ℕ) - 1 ∧
    (TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c).tape = c.tape := by
  obtain ⟨t_phase, t_state, t_bit, t_move⟩ :=
    transition_seek_back Δ1 Δ2 Δdst hle12 hle2d op hi_lo hi_hi c.state.snd
      (c.tape c.head)
  have hmove_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.snd : Move) = Move.left := t_move
  have hbit_step :
      (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.step c.state
          (c.tape c.head)).snd.fst : Bool) = c.tape c.head := t_bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).fst.val = c.state.fst.val + 1
    exact t_phase
  · rw [stepConfig_state]
    show (((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).transition c.state.fst
            c.state.snd (c.tape c.head)).fst).snd = c.state.snd
    exact t_state
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_left_val_of_pos c h_head_pos]
  · rw [stepConfig_tape, hbit_step]
    exact BinaryCounter.write_self_eq c c.head

/-! ### Block A: j-fold seek from 0 to src1 -/

theorem run_after_j_seek_to_src1_steps (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    ∀ j, j ≤ Δ1 →
    let cj := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c j
    cj.state.fst.val = j ∧
    cj.state.snd = (false, false) ∧
    ((cj.head : ℕ) = (c.head : ℕ) + j) ∧
    cj.tape = c.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · exact h_state_snd
    · show (c.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le : j' ≤ Δ1 := by omega
    have hj'_lt : j' < Δ1 := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cj' := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c j'
      with hcj'
    have h_phase_cj' : cj'.state.fst.val < Δ1 := by rw [ih_phase]; exact hj'_lt
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 <
          (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seek_to_src1 Δ1 Δ2 Δdst hle12 hle2d op cj' h_phase_cj' h_head_advance_bound
    have hrw :
        TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c (j' + 1) =
          TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val + 1 = c.head.val + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-! ### Block B: j-fold seek from src1 to src2, after read1 already fired -/

theorem run_after_j_seek_to_src2_steps (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)
    (h_src1_bound : (c.head : ℕ) + Δ1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    ∀ j, j ≤ Δ2 - Δ1 →
    let ctotal := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (Δ1 + 1 + j)
    ctotal.state.fst.val = Δ1 + 1 + j ∧
    ctotal.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩, false) ∧
    ((ctotal.head : ℕ) = (c.head : ℕ) + Δ1 + j) ∧
    ctotal.tape = c.tape := by
  intro j hj
  -- Base structure: first Δ1 + 1 steps = Block A + read1.
  obtain ⟨A_phase, A_state, A_head, A_tape⟩ :=
    run_after_j_seek_to_src1_steps Δ1 Δ2 Δdst hle12 hle2d op c h_phase h_state_snd h_bound
      Δ1 le_rfl
  set cA := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c Δ1
    with hcA
  -- One more step (read1 phase).
  have h_phase_cA : cA.state.fst.val = Δ1 := A_phase
  obtain ⟨rd_phase, rd_state, rd_head, rd_tape⟩ :=
    stepConfig_read1 Δ1 Δ2 Δdst hle12 hle2d op cA h_phase_cA
  have h_rewrite_Δ1_plus_one :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c (Δ1 + 1) =
        TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cA := by
    rw [runConfig_succ]
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ1 + 1 + 0)).state.fst.val = Δ1 + 1 + 0
      rw [show Δ1 + 1 + 0 = Δ1 + 1 from by omega, h_rewrite_Δ1_plus_one]
      exact rd_phase
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ1 + 1 + 0)).state.snd =
           (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩, false)
      rw [show Δ1 + 1 + 0 = Δ1 + 1 from by omega, h_rewrite_Δ1_plus_one, rd_state, A_tape]
      have h_head_fin : cA.head = (⟨(c.head : ℕ) + Δ1, h_src1_bound⟩ :
          Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)) := by
        apply Fin.ext; exact A_head
      rw [h_head_fin]
      congr 1
      rw [A_state]
    · show ((TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ1 + 1 + 0)).head : ℕ) = (c.head : ℕ) + Δ1 + 0
      rw [show Δ1 + 1 + 0 = Δ1 + 1 from by omega, h_rewrite_Δ1_plus_one, rd_head]
      show (cA.head : ℕ) = _
      rw [A_head]; omega
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ1 + 1 + 0)).tape = c.tape
      rw [show Δ1 + 1 + 0 = Δ1 + 1 from by omega, h_rewrite_Δ1_plus_one, rd_tape, A_tape]
  | succ j' ih =>
    have hj'_le : j' ≤ Δ2 - Δ1 := by omega
    have hj'_lt : j' < Δ2 - Δ1 := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cprev := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (Δ1 + 1 + j')
      with hcprev
    have h_phase_lo : Δ1 < cprev.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cprev.state.fst.val < Δ2 + 1 := by rw [ih_phase]; omega
    have h_head_advance_bound :
        (cprev.head : ℕ) + 1 <
          (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨B_phase, B_state, B_head, B_tape⟩ :=
      stepConfig_seek_to_src2 Δ1 Δ2 Δdst hle12 hle2d op cprev h_phase_lo h_phase_hi
        h_head_advance_bound
    have hrw :
        TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
            (Δ1 + 1 + (j' + 1)) =
          TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cprev := by
      rw [show Δ1 + 1 + (j' + 1) = (Δ1 + 1 + j') + 1 from by omega,
          runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, B_phase, ih_phase]; omega
    · rw [hrw, B_state, ih_state]
    · rw [hrw, B_head]
      show cprev.head.val + 1 = c.head.val + Δ1 + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, B_tape, ih_tape]

/-! ### Block C: j-fold seek from src2 to dst, after read2 already fired -/

theorem run_after_j_seek_to_dst_steps (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)
    (h_src1_bound : (c.head : ℕ) + Δ1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)
    (h_src2_bound : (c.head : ℕ) + Δ2 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    ∀ j, j ≤ Δdst - Δ2 →
    let ctotal := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (Δ2 + 2 + j)
    ctotal.state.fst.val = Δ2 + 2 + j ∧
    ctotal.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                        c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) ∧
    ((ctotal.head : ℕ) = (c.head : ℕ) + Δ2 + j) ∧
    ctotal.tape = c.tape := by
  intro j hj
  -- First Δ1 + 1 + (Δ2 - Δ1) = Δ2 + 1 total steps bring us to post-read1 Block B end.
  obtain ⟨B_phase, B_state, B_head, B_tape⟩ :=
    run_after_j_seek_to_src2_steps Δ1 Δ2 Δdst hle12 hle2d op c h_phase h_state_snd h_bound
      h_src1_bound (Δ2 - Δ1) le_rfl
  have h_total_B : Δ1 + 1 + (Δ2 - Δ1) = Δ2 + 1 := by omega
  set cB := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c (Δ2 + 1)
    with hcB
  have h_rewrite_B :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
          (Δ1 + 1 + (Δ2 - Δ1)) = cB := by
    rw [h_total_B]
  have h_phase_cB : cB.state.fst.val = Δ2 + 1 := by
    rw [← h_rewrite_B]; show _ = Δ2 + 1
    rw [B_phase]; omega
  have h_state_cB : cB.state.snd =
      (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩, false) := by
    rw [← h_rewrite_B]; exact B_state
  have h_head_cB : (cB.head : ℕ) = (c.head : ℕ) + Δ2 := by
    rw [← h_rewrite_B]; show _ = _
    rw [B_head]; omega
  have h_tape_cB : cB.tape = c.tape := by
    rw [← h_rewrite_B]; exact B_tape
  -- One more step: read2 phase.
  obtain ⟨rd_phase, rd_state, rd_head, rd_tape⟩ :=
    stepConfig_read2 Δ1 Δ2 Δdst hle12 hle2d op cB h_phase_cB
  have h_rewrite_Δ2_plus_two :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c (Δ2 + 2) =
        TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cB := by
    rw [show Δ2 + 2 = (Δ2 + 1) + 1 from by omega, runConfig_succ]
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ2 + 2 + 0)).state.fst.val = Δ2 + 2 + 0
      rw [show Δ2 + 2 + 0 = Δ2 + 2 from by omega, h_rewrite_Δ2_plus_two]
      exact rd_phase
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ2 + 2 + 0)).state.snd =
           (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
            c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩)
      rw [show Δ2 + 2 + 0 = Δ2 + 2 from by omega, h_rewrite_Δ2_plus_two, rd_state, h_tape_cB]
      have h_head_fin : cB.head = (⟨(c.head : ℕ) + Δ2, h_src2_bound⟩ :
          Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)) := by
        apply Fin.ext; exact h_head_cB
      rw [h_head_fin, h_state_cB]
    · show ((TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ2 + 2 + 0)).head : ℕ) = (c.head : ℕ) + Δ2 + 0
      rw [show Δ2 + 2 + 0 = Δ2 + 2 from by omega, h_rewrite_Δ2_plus_two, rd_head]
      show (cB.head : ℕ) = _
      rw [h_head_cB]; omega
    · show (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
             (Δ2 + 2 + 0)).tape = c.tape
      rw [show Δ2 + 2 + 0 = Δ2 + 2 from by omega, h_rewrite_Δ2_plus_two, rd_tape, h_tape_cB]
  | succ j' ih =>
    have hj'_le : j' ≤ Δdst - Δ2 := by omega
    have hj'_lt : j' < Δdst - Δ2 := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cprev := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (Δ2 + 2 + j')
      with hcprev
    have h_phase_lo : Δ2 + 1 < cprev.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cprev.state.fst.val < Δdst + 2 := by rw [ih_phase]; omega
    have h_head_advance_bound :
        (cprev.head : ℕ) + 1 <
          (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by
      rw [ih_head]; omega
    obtain ⟨C_phase, C_state, C_head, C_tape⟩ :=
      stepConfig_seek_to_dst Δ1 Δ2 Δdst hle12 hle2d op cprev h_phase_lo h_phase_hi
        h_head_advance_bound
    have hrw :
        TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
            (Δ2 + 2 + (j' + 1)) =
          TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cprev := by
      rw [show Δ2 + 2 + (j' + 1) = (Δ2 + 2 + j') + 1 from by omega,
          runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, C_phase, ih_phase]; omega
    · rw [hrw, C_state, ih_state]
    · rw [hrw, C_head]
      show cprev.head.val + 1 = c.head.val + Δ2 + (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, C_tape, ih_tape]

/-! ### After write phase: commits op(bit1, bit2) at dst -/

theorem run_after_write_phase (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    let cmid := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (Δdst + 3)
    ∃ (h_src1_bound : (c.head : ℕ) + Δ1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)
      (h_src2_bound : (c.head : ℕ) + Δ2 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n),
    cmid.state.fst.val = Δdst + 3 ∧
    cmid.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                      c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) ∧
    ((cmid.head : ℕ) = (c.head : ℕ) + Δdst) ∧
    cmid.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                  (op (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩)
                      (c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩)) := by
  have h_src1_bound : (c.head : ℕ) + Δ1 <
      (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by omega
  have h_src2_bound : (c.head : ℕ) + Δ2 <
      (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by omega
  refine ⟨h_src1_bound, h_src2_bound, ?_⟩
  -- After Δ2 + 2 + (Δdst - Δ2) = Δdst + 2 total steps: at phase Δdst + 2,
  -- state = (bit1, bit2), head = c.head + Δdst, tape unchanged.
  obtain ⟨C_phase, C_state, C_head, C_tape⟩ :=
    run_after_j_seek_to_dst_steps Δ1 Δ2 Δdst hle12 hle2d op c h_phase h_state_snd h_bound
      h_src1_bound h_src2_bound (Δdst - Δ2) le_rfl
  have h_total : Δ2 + 2 + (Δdst - Δ2) = Δdst + 2 := by omega
  set cpre := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
      (Δdst + 2) with hcpre
  have h_rewrite_dst_plus_two :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
          (Δ2 + 2 + (Δdst - Δ2)) = cpre := by
    rw [h_total]
  have h_phase_cpre : cpre.state.fst.val = Δdst + 2 := by
    rw [← h_rewrite_dst_plus_two]; show _ = Δdst + 2
    rw [C_phase]; omega
  have h_state_cpre : cpre.state.snd =
      (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
       c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) := by
    rw [← h_rewrite_dst_plus_two]; exact C_state
  have h_head_cpre : (cpre.head : ℕ) = (c.head : ℕ) + Δdst := by
    rw [← h_rewrite_dst_plus_two]; show _ = _
    rw [C_head]; omega
  have h_tape_cpre : cpre.tape = c.tape := by
    rw [← h_rewrite_dst_plus_two]; exact C_tape
  -- One more step: write phase.
  obtain ⟨wr_phase, wr_state, wr_head, wr_tape⟩ :=
    stepConfig_write Δ1 Δ2 Δdst hle12 hle2d op cpre h_phase_cpre
  have hrw_final :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c (Δdst + 3) =
        TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cpre := by
    rw [show Δdst + 3 = (Δdst + 2) + 1 from by omega, runConfig_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrw_final]; exact wr_phase
  · rw [hrw_final, wr_state, h_state_cpre]
  · rw [hrw_final, wr_head]
    show (cpre.head : ℕ) = _; exact h_head_cpre
  · rw [hrw_final, wr_tape]
    have h_head_fin : cpre.head = (⟨(c.head : ℕ) + Δdst, h_bound⟩ :
        Fin ((combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)) := by
      apply Fin.ext; exact h_head_cpre
    rw [h_head_fin, h_state_cpre]
    funext j
    unfold Configuration.write
    split_ifs with hj
    · rfl
    · rw [h_tape_cpre]

/-! ### Block D: j-fold seek-back invariant -/

theorem run_j_seek_back (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c_start : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c_start.state.fst.val = Δdst + 3)
    (h_head_ge : Δdst ≤ (c_start.head : ℕ)) :
    ∀ j, j ≤ Δdst →
    let cj := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c_start j
    cj.state.fst.val = Δdst + 3 + j ∧
    cj.state.snd = c_start.state.snd ∧
    ((cj.head : ℕ) = (c_start.head : ℕ) - j) ∧
    cj.tape = c_start.tape := by
  intro j hjΔ
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c_start.state.fst.val = Δdst + 3 + 0; rw [h_phase]
    · rfl
    · show (c_start.head : ℕ) = _; omega
    · rfl
  | succ j' ih =>
    have hj'_le : j' ≤ Δdst := by omega
    have hj'_lt : j' < Δdst := by omega
    obtain ⟨ih_phase, ih_state, ih_head, ih_tape⟩ := ih hj'_le
    set cj' := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c_start j'
      with hcj'
    have h_phase_lo : Δdst + 2 < cj'.state.fst.val := by rw [ih_phase]; omega
    have h_phase_hi : cj'.state.fst.val < 2 * Δdst + 3 := by rw [ih_phase]; omega
    have h_head_pos : 0 < (cj'.head : ℕ) := by rw [ih_head]; omega
    obtain ⟨rip_phase, rip_state, rip_head, rip_tape⟩ :=
      stepConfig_seek_back Δ1 Δ2 Δdst hle12 hle2d op cj' h_phase_lo h_phase_hi h_head_pos
    have hrw :
        TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c_start
            (j' + 1) =
          TM.stepConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw, rip_phase, ih_phase]; omega
    · rw [hrw, rip_state, ih_state]
    · rw [hrw, rip_head]
      show cj'.head.val - 1 = c_start.head.val - (j' + 1)
      rw [ih_head]; omega
    · rw [hrw, rip_tape, ih_tape]

/-- **Full correctness of `combineAtOffsetProgram`**: after `2*Δdst + 3` steps,
the TM reaches its accept phase with head back at origin, state carrying
both source bits, and the tape updated at the destination with `op` applied. -/
theorem combineAtOffsetProgram_run_full (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) {n : Nat}
    (c : Configuration (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
        (2 * Δdst + 3)
    ∃ (h_src1_bound : (c.head : ℕ) + Δ1 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n)
      (h_src2_bound : (c.head : ℕ) + Δ2 <
        (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n),
    cfinal.state.fst.val = 2 * Δdst + 3 ∧
    cfinal.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                        c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                    (op (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩)
                        (c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩)) := by
  have h_src1_bound : (c.head : ℕ) + Δ1 <
      (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by omega
  have h_src2_bound : (c.head : ℕ) + Δ2 <
      (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM.tapeLength n := by omega
  refine ⟨h_src1_bound, h_src2_bound, ?_⟩
  have hsplit : 2 * Δdst + 3 = (Δdst + 3) + Δdst := by omega
  have hcomp :
      TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
          (2 * Δdst + 3) =
        TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM)
          (TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
              (Δdst + 3))
          Δdst := by
    rw [hsplit, runConfig_add]
  obtain ⟨h_src1_bound', h_src2_bound', mid_phase, mid_state, mid_head, mid_tape⟩ :=
    run_after_write_phase Δ1 Δ2 Δdst hle12 hle2d op c h_phase h_state_snd h_bound
  set cmid := TM.runConfig (M := (combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d op).toTM) c
      (Δdst + 3) with hcmid
  have h_phase_mid : cmid.state.fst.val = Δdst + 3 := mid_phase
  have h_head_mid : (cmid.head : ℕ) = (c.head : ℕ) + Δdst := mid_head
  have h_head_ge : Δdst ≤ (cmid.head : ℕ) := by rw [h_head_mid]; omega
  have h_state_mid_rewritten :
      cmid.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                        c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) := mid_state
  obtain ⟨left_phase, left_state, left_head, left_tape⟩ :=
    run_j_seek_back Δ1 Δ2 Δdst hle12 hle2d op cmid h_phase_mid h_head_ge Δdst le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcomp, left_phase]; omega
  · rw [hcomp, left_state]; exact h_state_mid_rewritten
  · rw [hcomp]
    apply Fin.ext
    show (_ : ℕ) = (c.head : ℕ)
    rw [left_head, h_head_mid]; omega
  · rw [hcomp, left_tape, mid_tape]

/-! ### `ConstStatePhasedProgram` re-packaging

A parallel definition of `combineAtOffsetProgram` as a
`ConstStatePhasedProgram (Bool × Bool)`, suitable for composition via
`ConstStatePhasedProgram.seq`.  It has an identical transition
structure; `combineAtOffsetCS_toPhased_eq` proves that
`combineAtOffsetCS.toPhased = combineAtOffsetProgram`, so all existing
correctness theorems (including `combineAtOffsetProgram_run_full`)
transport automatically. -/

def combineAtOffsetCS (Δ1 Δ2 Δdst : Nat) (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst)
    (op : Bool → Bool → Bool) :
    ConstStatePhasedProgram (Bool × Bool) where
  numPhases := 2 * Δdst + 4
  startPhase := ⟨0, by omega⟩
  startState := (false, false)
  acceptPhase := ⟨2 * Δdst + 3, by omega⟩
  acceptState := (false, false)
  transition := fun i q scan =>
    if hi1 : i.val < Δ1 then
      (⟨i.val + 1, by omega⟩, q, scan, Move.right)
    else if hi2 : i.val = Δ1 then
      (⟨Δ1 + 1, by omega⟩, (scan, q.snd), scan, Move.stay)
    else if hi3 : i.val < Δ2 + 1 then
      (⟨i.val + 1, by omega⟩, q, scan, Move.right)
    else if hi4 : i.val = Δ2 + 1 then
      (⟨Δ2 + 2, by omega⟩, (q.fst, scan), scan, Move.stay)
    else if hi5 : i.val < Δdst + 2 then
      (⟨i.val + 1, by omega⟩, q, scan, Move.right)
    else if hi6 : i.val = Δdst + 2 then
      (⟨Δdst + 3, by omega⟩, q, op q.fst q.snd, Move.stay)
    else if hi7 : i.val < 2 * Δdst + 3 then
      (⟨i.val + 1, by omega⟩, q, scan, Move.left)
    else
      (⟨2 * Δdst + 3, by omega⟩, q, scan, Move.stay)
  timeBound := fun _ => 2 * Δdst + 3

@[simp] theorem combineAtOffsetCS_numPhases (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) :
    (combineAtOffsetCS Δ1 Δ2 Δdst hle12 hle2d op).numPhases = 2 * Δdst + 4 := rfl

@[simp] theorem combineAtOffsetCS_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) (n : Nat) :
    (combineAtOffsetCS Δ1 Δ2 Δdst hle12 hle2d op).timeBound n = 2 * Δdst + 3 := rfl

end CombineAtOffset

end TM

end PsubsetPpoly
end Internal
end Pnp3
