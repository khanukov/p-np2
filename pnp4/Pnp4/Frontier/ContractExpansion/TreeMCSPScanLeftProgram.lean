import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Leftward scan-to-marker primitive (NP-verifier track — first bidirectional brick)

The right-only composition layer is structurally complete, but `M`'s genuinely data-dependent phases
(recover `n` from the gamma payload, compare the certificate's witness prefix against the instance's
prefix) need the head to travel **leftward** — to return from a region just scanned back to a reference
marker.  This module builds the fundamental *leftward motion* primitive: the exact dual of
`gammaSelfLoopScan`, scanning **left** over `0`s and stopping on the first `1`.

`Move.left` decrements the head (clamped at `0`); the scan re-enters phase `0` moving left while it
reads a `0`, and jumps to the done phase `1` (staying put) on the first `1`.  This is a low-level
*motion* primitive (not a premature high-level decode program — cf. `TM_VERIFIER_STRATEGY.md` §6b),
analogous to the proven rightward `gammaSelfLoopScan`, and is the first verified building block of the
bidirectional layer.

Like the rightward scan it is fully proven through its run behaviour (`selfLoopScanLeft_runConfig_*`).
It does **not** satisfy `TMNeverMovesLeft` (it is leftward by design); instead it never moves *right*
(`selfLoopScanLeft_transition_move`).  All surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` execution triple. -/

/-- Leftward self-loop scan: phase `0` re-enters itself (moving **left**) while reading `0`, and jumps
to the done phase `1` (staying put) on the first `1`.  Fixed 2-phase structure (dual of
`gammaSelfLoopScan`). -/
def selfLoopScanLeft : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨1, by omega⟩, (), b, Move.stay)
      else (⟨0, by omega⟩, (), b, Move.left)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopScanLeft_timeBound (n : Nat) :
    selfLoopScanLeft.timeBound n = n := rfl

@[simp] theorem selfLoopScanLeft_numPhases : selfLoopScanLeft.numPhases = 2 := rfl

@[simp] theorem selfLoopScanLeft_startPhase_val : (selfLoopScanLeft.startPhase : Nat) = 0 := rfl

@[simp] theorem selfLoopScanLeft_acceptPhase_val : (selfLoopScanLeft.acceptPhase : Nat) = 1 := rfl

/-- The leftward scan never moves the head right: it moves left while scanning a `0`, otherwise stays
(on the terminator, or in the done phase).  The dual confinement fact to `gammaSelfLoopScan`'s
never-moves-left. -/
theorem selfLoopScanLeft_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopScanLeft.transition i s b).2.2.2 ≠ Move.right := by
  unfold selfLoopScanLeft
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas (the leftward back-edge step) -/

/-- Scan-phase step on a `0`: the phase stays `0` (the leftward self-loop / back-edge). -/
theorem selfLoopScanLeft_stepConfig_scan_zero_phase {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit]

/-- Scan-phase step on a `0`: the head moves left (the head-carried leftward scan progresses). -/
theorem selfLoopScanLeft_stepConfig_scan_zero_head {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit]

/-- Scan-phase step on a `0`: the tape is unchanged (the `0` is written back). -/
theorem selfLoopScanLeft_stepConfig_scan_zero_tape {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Terminator step on a `1`: jump to the done phase `1`. -/
theorem selfLoopScanLeft_stepConfig_scan_one_phase {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit]

/-- Terminator step on a `1`: the head stays put. -/
theorem selfLoopScanLeft_stepConfig_scan_one_head {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit, Configuration.moveHead]

/-- Terminator step on a `1`: the tape is unchanged. -/
theorem selfLoopScanLeft_stepConfig_scan_one_tape {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeft, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Boundary characterization (the `Move.left` clamp): at head `0`, a scan step on a `0` leaves the
head at `0` — the scan cannot retreat past the left end of the tape, it clamps.  This makes the
`j ≤ c0.head` / `k < c0.head` preconditions of the run lemmas below necessary: from `head = 0` the
primitive makes no leftward progress (it would spin in place).  Explicit clamping lemma for
completeness (per the head-boundary semantics of `Configuration.moveHead Move.left`). -/
theorem selfLoopScanLeft_stepConfig_scan_zero_head_clamp {L : Nat}
    (c : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) (hhead0 : (c.head : Nat) = 0) :
    ((TM.stepConfig (M := selfLoopScanLeft.toPhased.toTM) c).head : Nat) = 0 := by
  rw [selfLoopScanLeft_stepConfig_scan_zero_head c hi hstate hbit]
  simp [Configuration.moveHead, hhead0]

/-! ### Leftward scanning run invariant and terminator -/

/-- Leftward scanning invariant: from a start `c0` in scan phase `0`, if the `j` cells just to the left
of and including the head (positions `(c0.head − j, c0.head]`) are all `0`, then after `j ≤ c0.head`
steps the machine is still in scan phase `0`, the head has retreated to `c0.head − j`, and the tape is
unchanged.  The leftward dual of `gammaSelfLoopScan`'s scanning invariant (head *decreases*, requiring
`j ≤ c0.head` so each `Move.left` genuinely decrements rather than clamping at `0`). -/
theorem selfLoopScanLeft_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (selfLoopScanLeft.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanLeft_stepConfig_scan_zero_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanLeft_stepConfig_scan_zero_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopScanLeft_stepConfig_scan_zero_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Leftward terminator: from a start `c0` in scan phase `0`, if the cells `(k, c0.head]` are all `0`
and cell `k` is `1` (`k < c0.head`), then after `(c0.head − k) + 1` steps (`c0.head − k` to retreat to
the marker, one to read it) the machine has stopped at phase `1` with the head resting on the marker
(`head = k`) and the tape unchanged.  The leftward dual of `gammaSelfLoopScan`'s terminator-locating
result — a verified "return left to the nearest `1`". -/
theorem selfLoopScanLeft_runConfig_terminator {L : Nat}
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : k < (c0.head : Nat))
    (hzeros : ∀ p : Fin (selfLoopScanLeft.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false)
    (hterm : ∀ p : Fin (selfLoopScanLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = true) :
    (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).state).fst
        : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).head
          : Nat) = k
      ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).tape
          = c0.tape := by
  -- Retreat the `(c0.head − k)`-cell zero window down onto the marker, then take the terminator step.
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeft_runConfig_scanning c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hzeros p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeft_stepConfig_scan_one_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanLeft_stepConfig_scan_one_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanLeft_stepConfig_scan_one_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### Composition: the leftward scan as a non-first (P2-region) phase

The right-only `seq`/`seqList` single-step lemmas (`seq_stepConfig_P2_*`) are *transition-generic* — they
do not assume `TMNeverMovesLeft` — so the leftward scan composes as a `seq` phase exactly as the
rightward scan does, with the head now *decreasing*.  This is the first composition fact of the
bidirectional layer (no new composition toolkit needed for straight-line composition; only the
direction of motion differs). -/

/-- Leftward scan step as a non-first phase (composition phase `P1.numPhases`, bit `0`): the phase
stays. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_zero_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).state).fst.val = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeft, hsub, hbit]

/-- Leftward scan step as a non-first phase (bit `0`): the head moves left. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_zero_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeft, hsub, hbit]

/-- Leftward scan step as a non-first phase (bit `0`): the tape is unchanged. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_zero_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanLeft c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanLeft, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Leftward scanning invariant as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `(c0.head − k, c0.head]` is all `0`, then after `k ≤ c0.head` steps the
phase still rests at `P1.numPhases`, the head has retreated to `c0.head − k`, and the tape is
unchanged.  Offset/non-first analogue of `selfLoopScanLeft_runConfig_scanning`. -/
theorem selfLoopScanLeft_seqP2_runConfig_scanning (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin ((seq P1 selfLoopScanLeft).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanLeft_seqP2_stepConfig_scan_zero_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanLeft_seqP2_stepConfig_scan_zero_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopScanLeft_seqP2_stepConfig_scan_zero_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Leftward terminator step as a non-first phase (bit `1`): jump to the shifted done phase
`P1.numPhases + 1`. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_one_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeft, hsub, hbit]

/-- Leftward terminator step as a non-first phase (bit `1`): the head stays put. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_one_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanLeft c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeft, hsub, hbit, Configuration.moveHead]

/-- Leftward terminator step as a non-first phase (bit `1`): the tape is unchanged. -/
theorem selfLoopScanLeft_seqP2_stepConfig_scan_one_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeft).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanLeft c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanLeft, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Leftward terminator-locating run as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `(k, c0.head]` is all `0` and cell `k` is `1` (`k < c0.head`), then after
`(c0.head − k) + 1` steps the scan has stopped at the shifted done phase `P1.numPhases + 1`, the head
rests on the marker (`k`), and the tape is unchanged.  Gives the leftward scan full composition-API
parity with `gammaSelfLoopScan` (seqP2 scanning *and* terminator). -/
theorem selfLoopScanLeft_seqP2_runConfig_terminator (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanLeft).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (k : Nat) (hk : k < (c0.head : Nat))
    (hzeros : ∀ p : Fin ((seq P1 selfLoopScanLeft).toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false)
    (hterm : ∀ p : Fin ((seq P1 selfLoopScanLeft).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = true) :
    (((TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0
        (((c0.head : Nat) - k) + 1)).state).fst : Nat) = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeft_seqP2_runConfig_scanning P1 c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hzeros p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopScanLeft).toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeft_seqP2_stepConfig_scan_one_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanLeft_seqP2_stepConfig_scan_one_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanLeft_seqP2_stepConfig_scan_one_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
