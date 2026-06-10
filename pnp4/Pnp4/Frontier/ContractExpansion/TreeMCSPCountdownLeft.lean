import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Unary countdown self-loop (NP-verifier track — marker-free counter, brick toward the row loop)

`TM_VERIFIER_STRATEGY.md` §6c identifies the **bounded unary-counter loop** as the shared bottleneck
for both remaining data-dependent items (the counted gamma-payload read and the `2^n`-row loop): a
*binary* counter cannot be delimited on a marker-free binary alphabet by a fixed machine, but a
**unary** counter can (zero-test = one read; decrement = flip the boundary `1`).  This module builds
the countdown core: `selfLoopCountdownLeft` **consumes** a unary counter — a contiguous block of `1`s —
by walking *leftward*, flipping each `1` to `0`, and stopping at the first `0` (the counter is now
empty).  Consuming a `K`-block of `1`s takes exactly `K` steps, so this is the marker-free
"decrement-to-zero in `K` ticks" primitive the loop combinator will drive.

Structurally it is the consuming dual of `selfLoopScanLeft` (which scans `0`s leftward without writing,
stopping on a `1`); here the bit roles are swapped *and* the scanned `1` is overwritten with `0`, so the
tape evolves (as in the increment carry-ripple).  Built like the other self-loops: program, structural
facts, single-step lemmas, and the `consume`-`K`-ticks run invariant.  Builds no verifier and proves no
separation; all surfaces carry only the standard `[propext, Classical.choice, Quot.sound]` triple. -/

/-- Self-loop unary countdown: phase `0` consumes a `1` (writes `0`, moves left, re-enters — the
back-edge) and stops (phase `1`) on reading a `0`.  Walking leftward over a block of `1`s clears them
to `0`; the number of steps equals the block length (the unary count). -/
def selfLoopCountdownLeft : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), false, Move.left)
      else (⟨1, by omega⟩, (), b, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopCountdownLeft_timeBound (n : Nat) :
    selfLoopCountdownLeft.timeBound n = n := rfl

@[simp] theorem selfLoopCountdownLeft_numPhases : selfLoopCountdownLeft.numPhases = 2 := rfl

@[simp] theorem selfLoopCountdownLeft_startPhase_val :
    (selfLoopCountdownLeft.startPhase : Nat) = 0 := rfl

@[simp] theorem selfLoopCountdownLeft_acceptPhase_val :
    (selfLoopCountdownLeft.acceptPhase : Nat) = 1 := rfl

/-- The countdown never moves the head right: it moves left while consuming a `1`, otherwise stays. -/
theorem selfLoopCountdownLeft_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopCountdownLeft.transition i s b).2.2.2 ≠ Move.right := by
  unfold selfLoopCountdownLeft
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas (the consuming leftward back-edge step) -/

/-- Consume step (phase `0`, bit `1`): the phase stays `0` (the leftward self-loop / back-edge). -/
theorem selfLoopCountdownLeft_stepConfig_consume_phase {L : Nat}
    (c : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopCountdownLeft.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopCountdownLeft, hi, hbit]

/-- Consume step (phase `0`, bit `1`): the head moves left (the countdown progresses). -/
theorem selfLoopCountdownLeft_stepConfig_consume_head {L : Nat}
    (c : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopCountdownLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopCountdownLeft, hi, hbit]

/-- Consume step (phase `0`, bit `1`): the consumed `1` is overwritten with `0`. -/
theorem selfLoopCountdownLeft_stepConfig_consume_tape {L : Nat}
    (c : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopCountdownLeft.toPhased.toTM) c).tape = c.write c.head false := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopCountdownLeft, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the counter is empty — jump to the done phase `1`. -/
theorem selfLoopCountdownLeft_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopCountdownLeft.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopCountdownLeft, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopCountdownLeft_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopCountdownLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopCountdownLeft, hi, hbit, Configuration.moveHead]

/-! ### The countdown run invariant -/

/-- Countdown invariant from an arbitrary start `c0` (phase `0`): if the `j` cells just to the left of
and including the head (positions `(c0.head − j, c0.head]`) are all `1` (a unary count of `j`), then
after `j ≤ c0.head` steps the machine is still in phase `0`, the head has retreated to `c0.head − j`,
and exactly those `j` cells have been cleared to `0` (the rest of the tape unchanged).  Consuming a
`j`-block of `1`s takes exactly `j` steps — the marker-free unary countdown.  (`j ≤ c0.head` keeps
each `Move.left` genuinely decrementing rather than clamping at `0`.) -/
theorem selfLoopCountdownLeft_runConfig_consume {L : Nat}
    (c0 : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (selfLoopCountdownLeft.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) - j
      ∧ ∀ p : Fin (selfLoopCountdownLeft.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 j).tape p
            = (if (c0.head : Nat) - j < (p : Nat) ∧ (p : Nat) ≤ (c0.head : Nat)
                then false else c0.tape p) := by
  intro j
  induction j with
  | zero =>
      intro _ _
      refine ⟨hphase, by simp, ?_⟩
      intro p
      have h0 : (TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 0) = c0 := rfl
      rw [h0, if_neg (show ¬ ((c0.head : Nat) - 0 < (p : Nat) ∧ (p : Nat) ≤ (c0.head : Nat)) by omega)]
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
        (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 j with hc
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      -- The cell now under the head (position `c0.head − j`) is one of the `1`s of the block.
      have hbit : c.tape c.head = true := by
        rw [htp c.head]
        have hlt : ¬ ((c0.head : Nat) - j < (c.head : Nat) ∧ (c.head : Nat) ≤ (c0.head : Nat)) := by
          rw [hhd]; omega
        rw [if_neg hlt]
        exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopCountdownLeft_stepConfig_consume_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopCountdownLeft_stepConfig_consume_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopCountdownLeft_stepConfig_consume_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (by rw [hhd]; constructor <;> omega)]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ (c.head : Nat) := fun h => hp (Fin.ext h)
          rw [hhd] at hpc
          split_ifs <;> first | rfl | (exfalso; omega)

/-- Countdown to empty: if a unary count of `j` sits at and left of the head (positions
`(c0.head − j, c0.head]` all `1`) and the cell just below the block (`c0.head − j`) is `0`, then after
`j + 1` steps the countdown has stopped — phase `1`, head on the `0` boundary (`c0.head − j`), and the
`j` counted cells cleared to `0`.  The complete "decrement a unary counter to zero in `j + 1` steps"
unit. -/
theorem selfLoopCountdownLeft_runConfig_empty {L : Nat}
    (c0 : Configuration (M := selfLoopCountdownLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat) (hj : j ≤ (c0.head : Nat))
    (hones : ∀ p : Fin (selfLoopCountdownLeft.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hzero : ∀ p : Fin (selfLoopCountdownLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - j → c0.tape p = false) :
    (((TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 (j + 1)).head : Nat)
          = (c0.head : Nat) - j := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopCountdownLeft_runConfig_consume c0 hphase j hj hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopCountdownLeft.toPhased.toTM) c0 j with hc
  have hbit : c.tape c.head = false := by
    rw [htp c.head]
    have hlt : ¬ ((c0.head : Nat) - j < (c.head : Nat) ∧ (c.head : Nat) ≤ (c0.head : Nat)) := by
      rw [hhd]; omega
    rw [if_neg hlt]
    exact hzero c.head hhd
  refine ⟨?_, ?_⟩
  · exact selfLoopCountdownLeft_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopCountdownLeft_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd

/-! ### Composition lift: the countdown as a non-first (P2-region) phase

For the loop combinator the countdown runs as a `seq` component, so — per the cross-instance caveat —
we re-derive its consume behaviour on the composed machine `seq P1 selfLoopCountdownLeft` (the countdown
occupies P2, governed by `seq_stepConfig_P2_*`).  Mirrors `selfLoopScanLeft`'s seqP2 lift, but the tape
*evolves* (each consumed `1` becomes `0`), so the run invariant carries the conditional-tape clause. -/

/-- Consume step as a non-first phase (bit `1`): the phase stays at `P1.numPhases`. -/
theorem selfLoopCountdownLeft_seqP2_stepConfig_consume_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopCountdownLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopCountdownLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopCountdownLeft, hsub, hbit]

/-- Consume step as a non-first phase (bit `1`): the head moves left. -/
theorem selfLoopCountdownLeft_seqP2_stepConfig_consume_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopCountdownLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopCountdownLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopCountdownLeft, hsub, hbit]

/-- Consume step as a non-first phase (bit `1`): the consumed `1` becomes `0`. -/
theorem selfLoopCountdownLeft_seqP2_stepConfig_consume_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopCountdownLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c).tape
      = c.write c.head false := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopCountdownLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopCountdownLeft, hsub, hbit]

/-- Countdown consume invariant as a non-first phase, from an arbitrary start `c0` at phase
`P1.numPhases`: a `j`-block of `1`s at/left of the head clears to `0` in exactly `j` steps, the phase
stays at `P1.numPhases`, and the head retreats to `c0.head − j`.  Offset/non-first analogue of
`selfLoopCountdownLeft_runConfig_consume` — the countdown's composition-API parity for the loop. -/
theorem selfLoopCountdownLeft_seqP2_runConfig_consume (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin ((seq P1 selfLoopCountdownLeft).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 j).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) - j
      ∧ ∀ p : Fin ((seq P1 selfLoopCountdownLeft).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 j).tape p
            = (if (c0.head : Nat) - j < (p : Nat) ∧ (p : Nat) ≤ (c0.head : Nat)
                then false else c0.tape p) := by
  intro j
  induction j with
  | zero =>
      intro _ _
      refine ⟨hphase, by simp, ?_⟩
      intro p
      have h0 : (TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 0) = c0 := rfl
      rw [h0, if_neg (show ¬ ((c0.head : Nat) - 0 < (p : Nat) ∧ (p : Nat) ≤ (c0.head : Nat)) by omega)]
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 j with hc
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      have hbit : c.tape c.head = true := by
        rw [htp c.head]
        have hlt : ¬ ((c0.head : Nat) - j < (c.head : Nat) ∧ (c.head : Nat) ≤ (c0.head : Nat)) := by
          rw [hhd]; omega
        rw [if_neg hlt]
        exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopCountdownLeft_seqP2_stepConfig_consume_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopCountdownLeft_seqP2_stepConfig_consume_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopCountdownLeft_seqP2_stepConfig_consume_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (by rw [hhd]; constructor <;> omega)]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ (c.head : Nat) := fun h => hp (Fin.ext h)
          rw [hhd] at hpc
          split_ifs <;> first | rfl | (exfalso; omega)

/-- Stop step as a non-first phase (bit `0`): the counter is empty — jump to the shifted done phase
`P1.numPhases + 1`. -/
theorem selfLoopCountdownLeft_seqP2_stepConfig_stop_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopCountdownLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopCountdownLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopCountdownLeft, hsub, hbit]

/-- Stop step as a non-first phase (bit `0`): the head stays put. -/
theorem selfLoopCountdownLeft_seqP2_stepConfig_stop_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopCountdownLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopCountdownLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopCountdownLeft, hsub, hbit, Configuration.moveHead]

/-- Countdown-to-empty as a non-first phase, from an arbitrary start `c0` at phase `P1.numPhases`: a
`j`-block of `1`s above a `0` at `c0.head − j` is consumed and the loop exits to the shifted done phase
`P1.numPhases + 1` (head on the `0` boundary) after `j + 1` steps.  Completes the countdown's
composition-API parity (seqP2 `consume` *and* `empty`), giving the loop combinator both the body-running
and the exit-detecting halves on the composed machine. -/
theorem selfLoopCountdownLeft_seqP2_runConfig_empty (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (j : Nat) (hj : j ≤ (c0.head : Nat))
    (hones : ∀ p : Fin ((seq P1 selfLoopCountdownLeft).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hzero : ∀ p : Fin ((seq P1 selfLoopCountdownLeft).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - j → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 (j + 1)).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 (j + 1)).head : Nat)
          = (c0.head : Nat) - j := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopCountdownLeft_seqP2_runConfig_consume P1 c0 hphase j hj hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopCountdownLeft).toPhased.toTM) c0 j with hc
  have hbit : c.tape c.head = false := by
    rw [htp c.head]
    have hlt : ¬ ((c0.head : Nat) - j < (c.head : Nat) ∧ (c.head : Nat) ≤ (c0.head : Nat)) := by
      rw [hhd]; omega
    rw [if_neg hlt]
    exact hzero c.head hhd
  refine ⟨?_, ?_⟩
  · exact selfLoopCountdownLeft_seqP2_stepConfig_stop_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopCountdownLeft_seqP2_stepConfig_stop_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd

end ContractExpansion
end Frontier
end Pnp4
