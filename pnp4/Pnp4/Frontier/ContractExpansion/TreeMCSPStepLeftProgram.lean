import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Single-step leftward move (NP-verifier track — D2 transcoder, D2t-3c building block)

`stepLeftOnce` is the trivial one-cell **leftward** move: a fixed 2-phase program that, in phase `0`,
writes the scanned bit back, moves the head **left** by one — clamping at the tape's left end, i.e. at
head `0` the head stays at `0` (`Move.left` semantics), so its run lemma `stepLeftOnce_runConfig_one`
guards with `0 < c.head`; the boundary case is the explicit `stepLeftOnce_stepConfig_head_clamp` — and
halts (phase `1`).  The binary→unary
loop's home-seek (D2t-3c-β) uses it to step **off** the decrement's cleared `0`-cell onto the flipped
`1`-block before `selfLoopScanLeftOne` scans that block back to the sentinel — a single deterministic
left step that a `scan`-style self-loop (which is bit-conditional) cannot provide.

This ships the program and its one-step run-behaviour.  Builds no verifier and proves no separation; all
surfaces carry only the standard `[propext, Classical.choice, Quot.sound]` triple.
-/

/-- Single leftward step: phase `0` writes the scanned bit back, moves left (clamping at the tape's
left end — at head `0` it stays `0`), and halts (phase `1`). -/
def stepLeftOnce : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem stepLeftOnce_timeBound (n : Nat) : stepLeftOnce.timeBound n = 1 := rfl
@[simp] theorem stepLeftOnce_numPhases : stepLeftOnce.numPhases = 2 := rfl
@[simp] theorem stepLeftOnce_startPhase_val : (stepLeftOnce.startPhase : Nat) = 0 := rfl
@[simp] theorem stepLeftOnce_acceptPhase_val : (stepLeftOnce.acceptPhase : Nat) = 1 := rfl

/-- The single left step never moves the head right (it moves left, then stays in the done phase). -/
theorem stepLeftOnce_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (stepLeftOnce.transition i s b).2.2.2 ≠ Move.right := by
  unfold stepLeftOnce
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas (phase `0`) -/

/-- Phase-`0` step: advance to the done phase `1`. -/
theorem stepLeftOnce_stepConfig_phase {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]

/-- Phase-`0` step: the head moves left by one (when not at the left end). -/
theorem stepLeftOnce_stepConfig_head {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1 := by
  have hmove : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Boundary clamp: a phase-`0` step at head `0` leaves the head at `0` (`Move.left` clamps at the left
end) — the explicit witness that the "moves left by one" contract holds only for `head > 0`. -/
theorem stepLeftOnce_stepConfig_head_clamp {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead0 : (c.head : Nat) = 0) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head : Nat) = 0 := by
  have hmove : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  rw [hmove]
  simp [Configuration.moveHead, hhead0]

/-- Phase-`0` step: the tape is unchanged (the scanned bit is written back). -/
theorem stepLeftOnce_stepConfig_tape {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour: from phase `0` with the head not at the left end, after one step the program
is in the done phase `1`, the head has moved one cell left, and the tape is unchanged. -/
theorem stepLeftOnce_runConfig_one {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0) (hhead : 0 < (c.head : Nat)) :
    (((TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).tape = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepLeftOnce_stepConfig_phase c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepLeftOnce_stepConfig_head c (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepLeftOnce_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) hphase rfl

/-- Done-phase (`1`) idle: a step from phase `1` preserves phase, head, and tape. -/
theorem stepLeftOnce_stepConfig_done {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Composition lift: the single left step as a non-first phase (`seqP2`)

So `stepLeftOnce` composes as a phase of `seq P1 stepLeftOnce` (phase offset `P1.numPhases`) — used in
the binary→unary loop body to step between the operations. -/

/-- The single left step as a non-first phase: advance to the shifted done phase `P1.numPhases + 1`. -/
theorem stepLeftOnce_seqP2_stepConfig_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepLeftOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepLeftOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 stepLeftOnce c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [stepLeftOnce, hsub]

/-- The single left step as a non-first phase: the head moves left by one (when not at the left end). -/
theorem stepLeftOnce_seqP2_stepConfig_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepLeftOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepLeftOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hmove : (TM.stepConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P2_head P1 stepLeftOnce c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [stepLeftOnce, hsub]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- The single left step as a non-first phase: the tape is unchanged (scanned bit written back). -/
theorem stepLeftOnce_seqP2_stepConfig_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepLeftOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepLeftOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 stepLeftOnce c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [stepLeftOnce, hsub]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour as a non-first phase: from phase `P1.numPhases` with `0 < c.head`, after one
step the phase is `P1.numPhases + 1`, the head has moved one cell left, and the tape is unchanged. -/
theorem stepLeftOnce_seqP2_runConfig_one (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepLeftOnce).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = P1.numPhases) (hhead : 0 < (c.head : Nat)) :
    (((TM.runConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c 1).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c 1).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq P1 stepLeftOnce).toPhased.toTM) c 1).tape = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepLeftOnce_seqP2_stepConfig_phase P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepLeftOnce_seqP2_stepConfig_head P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepLeftOnce_seqP2_stepConfig_tape P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl

/-! ### Depth-3 composition lift: the single left step as the inner-inner P1 (`seqNested2`)

In the flattened binary→unary loop body `seqList [stepRightOnce, selfLoopDecrement, stepLeftOnce, …]`
the *third* element `stepLeftOnce` sits at chain-depth 3: it is the first component of the innermost
`seq stepLeftOnce R`, which is the second component of `seq Q (seq stepLeftOnce R)`, itself the second
component of `seq P1 (seq Q (seq stepLeftOnce R))`.  A step there is the outer P2-region step feeding
the middle P2-region transition feeding `stepLeftOnce`'s P1-normal transition — chained via
`seq_stepConfig_P2_*` then `seq_transition_P2_*` then `seq_transition_P1_normal_*`.  These lemmas are
the depth-3 analogue of `stepLeftOnce_seqP2_*`, generic in the two outer prefixes `P1`, `Q` and the
suffix `R`. -/

/-- Depth-3 left step: advance to the shifted done phase `P1.numPhases + Q.numPhases + 1`. -/
theorem stepLeftOnce_seqNested2_stepConfig_phase (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + Q.numPhases + 1 := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq stepLeftOnce R)) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub]
  omega

/-- Depth-3 left step: the head moves left by one (when not at the left end). -/
theorem stepLeftOnce_seqNested2_stepConfig_head (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) - 1 := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases := by omega
  have hmove : (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P2_head P1 (seq Q (seq stepLeftOnce R)) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Depth-3 left step: the tape is unchanged (the scanned bit is written back). -/
theorem stepLeftOnce_seqNested2_stepConfig_tape (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).tape = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq stepLeftOnce R)) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Depth-3 one-step run behaviour: from outer phase `P1.numPhases + Q.numPhases` with `0 < c.head`,
after one step the phase is `P1.numPhases + Q.numPhases + 1`, the head has moved one cell left, and the
tape is unchanged.  The depth-3 analogue of `stepLeftOnce_seqP2_runConfig_one`. -/
theorem stepLeftOnce_seqNested2_runConfig_one (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = P1.numPhases + Q.numPhases) (hhead : 0 < (c.head : Nat)) :
    (((TM.runConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c 1).state).fst : Nat)
        = P1.numPhases + Q.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c 1).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c 1).tape = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepLeftOnce_seqNested2_stepConfig_phase P1 Q R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepLeftOnce_seqNested2_stepConfig_head P1 Q R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepLeftOnce_seqNested2_stepConfig_tape P1 Q R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl

/-! ### Depth-5 composition lift: the single left step as element 5 (`seqNested4`)

The *fifth* element of the flattened binary→unary loop body is again `stepLeftOnce`, at chain-depth 5
(`seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))`).  The navigation peels four `seq` levels;
beyond depth 3 the successive middle subtractions `(a + b + …) − a` are supplied to `simp` as explicit
`hsubᵢ` facts (`Nat.add_sub_cancel_left` only matches the immediate `a + m − a` shape) together with the
non-self `¬(… < …)` comparison negations. -/

/-- Depth-5 left step: advance to `P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1`. -/
theorem stepLeftOnce_seqNested4_stepConfig_phase (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1 := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases < Q.numPhases) := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases < Q2.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases - Q.numPhases = Q2.numPhases + Q3.numPhases := by
    omega
  have hsub2 : Q2.numPhases + Q3.numPhases - Q2.numPhases = Q3.numPhases := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub, hc1, hc2, hsub1, hsub2]
  omega

/-- Depth-5 left step: the head moves left by one (when not at the left end). -/
theorem stepLeftOnce_seqNested4_stepConfig_head (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) - 1 := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases < Q.numPhases) := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases < Q2.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases - Q.numPhases = Q2.numPhases + Q3.numPhases := by
    omega
  have hsub2 : Q2.numPhases + Q3.numPhases - Q2.numPhases = Q3.numPhases := by omega
  have hmove : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub, hc1, hc2, hsub1, hsub2]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Depth-5 left step: the tape is unchanged (the scanned bit is written back). -/
theorem stepLeftOnce_seqNested4_stepConfig_tape (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).tape
      = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases < Q.numPhases) := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases < Q2.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases - Q.numPhases = Q2.numPhases + Q3.numPhases := by
    omega
  have hsub2 : Q2.numPhases + Q3.numPhases - Q2.numPhases = Q3.numPhases := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub, hc1, hc2, hsub1, hsub2]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Depth-5 one-step run behaviour (element 5): phase advances by one, head moves one cell left, tape
unchanged.  Depth-5 analogue of `stepLeftOnce_seqNested2_runConfig_one`. -/
theorem stepLeftOnce_seqNested4_runConfig_one (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases)
    (hhead : 0 < (c.head : Nat)) :
    (((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c 1).state).fst : Nat)
        = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c 1).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c 1).tape
          = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepLeftOnce_seqNested4_stepConfig_phase P1 Q Q2 Q3 R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepLeftOnce_seqNested4_stepConfig_head P1 Q Q2 Q3 R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepLeftOnce_seqNested4_stepConfig_tape P1 Q Q2 Q3 R c
      (i := c.state.fst) (s := c.state.snd) hphase rfl

/-! ### Depth-3 accept handoff: stepLeftOnce → successor (element-3→element-4 boundary)

After `stepLeftOnce` (element 3) takes its move step it rests at its shifted accept phase
`P1.numPhases + Q.numPhases + 1`; the next step is the inner `seq`'s handoff from `stepLeftOnce` to its
successor `R` (in the binary→unary body, the `selfLoopScanLeftOne` of the home-seek).  These lemmas
characterize that handoff on `seq P1 (seq Q (seq stepLeftOnce R))`. -/

/-- Depth-3 handoff (phase `P1.numPhases + Q.numPhases + 1`): advance to the successor's shifted start. -/
theorem stepLeftOnce_seqNested2_stepConfig_handoff_phase
    (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + (Q.numPhases + (stepLeftOnce.numPhases + R.startPhase.val)) := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + 1 - Q.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq stepLeftOnce R)) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub, hc1, hsub2]

/-- Depth-3 handoff: the head is unchanged (handoff stays put). -/
theorem stepLeftOnce_seqNested2_stepConfig_handoff_head
    (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).head = c.head := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + 1 - Q.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq stepLeftOnce R)) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub, hc1, hsub2, Configuration.moveHead]

/-- Depth-3 handoff: the tape is unchanged (scanned bit written back). -/
theorem stepLeftOnce_seqNested2_stepConfig_handoff_tape
    (P1 Q R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq stepLeftOnce R))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).tape = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + 1 - Q.numPhases = 1 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq stepLeftOnce R))).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq stepLeftOnce R)) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub, hc1, hsub2]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Depth-5 accept→successor handoff

The *fifth* element of the binary→unary loop body is again `stepLeftOnce` (at chain-depth 5); after its
move (accept phase `P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1`) the composed machine
hands off to the successor `R` (the `selfLoopAppendLeftOne` of the U-append).  These lemmas characterize
that handoff on `seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))`, the depth-5 analogue of
`stepLeftOnce_seqNested2_stepConfig_handoff_*`. -/

/-- Depth-5 handoff (phase `P1 + Q + Q2 + Q3 + 1`): advance to the successor's shifted start. -/
theorem stepLeftOnce_seqNested4_stepConfig_handoff_phase
    (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).state).fst.val
      = P1.numPhases
        + (Q.numPhases + (Q2.numPhases + (Q3.numPhases + (stepLeftOnce.numPhases + R.startPhase.val)))) := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + 1 < Q.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + 1 - Q.numPhases
      = Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + 1 < Q2.numPhases) := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + 1 - Q2.numPhases = Q3.numPhases + 1 := by omega
  have hc3 : ¬ (Q3.numPhases + 1 < Q3.numPhases) := by omega
  have hsub3 : Q3.numPhases + 1 - Q3.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub, hc1, hsub1, hc2, hsub2, hc3, hsub3]

/-- Depth-5 handoff: the head is unchanged. -/
theorem stepLeftOnce_seqNested4_stepConfig_handoff_head
    (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).head
      = c.head := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + 1 < Q.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + 1 - Q.numPhases
      = Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + 1 < Q2.numPhases) := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + 1 - Q2.numPhases = Q3.numPhases + 1 := by omega
  have hc3 : ¬ (Q3.numPhases + 1 < Q3.numPhases) := by omega
  have hsub3 : Q3.numPhases + 1 - Q3.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
  simp [seq, stepLeftOnce, hsub, hc1, hsub1, hc2, hsub2, hc3, hsub3, Configuration.moveHead]

/-- Depth-5 handoff: the tape is unchanged. -/
theorem stepLeftOnce_seqNested4_stepConfig_handoff_tape
    (P1 Q Q2 Q3 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + 1)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).tape
      = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + 1 < Q.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + 1 - Q.numPhases
      = Q2.numPhases + Q3.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + 1 < Q2.numPhases) := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + 1 - Q2.numPhases = Q3.numPhases + 1 := by omega
  have hc3 : ¬ (Q3.numPhases + 1 < Q3.numPhases) := by omega
  have hsub3 : Q3.numPhases + 1 - Q3.numPhases = 1 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R))))).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq Q3 (seq stepLeftOnce R)))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, stepLeftOnce_numPhases]; omega) hstate]
    simp [seq, stepLeftOnce, hsub, hc1, hsub1, hc2, hsub2, hc3, hsub3]
  rw [hwrite]
  funext jj
  by_cases hj : jj = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
