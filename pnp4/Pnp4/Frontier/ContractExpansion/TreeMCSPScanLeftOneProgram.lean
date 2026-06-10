import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Leftward scan-over-`1`s primitive (NP-verifier track — bidirectional motion vocabulary)

The bidirectional **motion** layer already covers leftward/rightward travel over `0`-blocks
(`selfLoopScanLeft` scans left over `0`s; `gammaSelfLoopScan` scans right over `0`s).  The shuttle that
recovers `n` from the gamma payload must also traverse **`1`-blocks**: once the gamma loop-counter is
materialized as a contiguous block of `1`s (`gammaSelfLoopFill`, or a run of consumed-counter cells),
re-anchoring at the block's left boundary means travelling **left over `1`s** until the first `0`.  This
module supplies that missing primitive — the exact dual of `selfLoopScanLeft` with the scan/stop bit
roles swapped: phase `0` re-enters itself (moving **left**) while reading a `1`, and jumps to the done
phase `1` (staying put) on the first `0`.

This completes the leftward scan family (`0`s via `selfLoopScanLeft`, `1`s here) and gives the
bidirectional layer the full four-way scan vocabulary (`0`/`1` × left/right) the data-dependent shuttle
needs — *without* committing to a particular counter-representation scheme (`TM_VERIFIER_STRATEGY.md`
§6d (a)/(b)/(c)), which remains the next design step.  This is a low-level *motion* primitive (not a
premature high-level decode program — cf. §6b), proven through its run behaviour exactly as
`selfLoopScanLeft`.

`Move.left` decrements the head (clamped at `0`).  It does **not** satisfy `TMNeverMovesLeft` (it is
leftward by design); instead it never moves *right* (`selfLoopScanLeftOne_transition_move`).  All
surfaces carry only the standard `[propext, Classical.choice, Quot.sound]` execution triple. -/

/-- Leftward self-loop scan over `1`s: phase `0` re-enters itself (moving **left**) while reading `1`,
and jumps to the done phase `1` (staying put) on the first `0`.  Fixed 2-phase structure (the bit-dual
of `selfLoopScanLeft`). -/
def selfLoopScanLeftOne : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), b, Move.left)
      else (⟨1, by omega⟩, (), b, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopScanLeftOne_timeBound (n : Nat) :
    selfLoopScanLeftOne.timeBound n = n := rfl

@[simp] theorem selfLoopScanLeftOne_numPhases : selfLoopScanLeftOne.numPhases = 2 := rfl

@[simp] theorem selfLoopScanLeftOne_startPhase_val : (selfLoopScanLeftOne.startPhase : Nat) = 0 := rfl

@[simp] theorem selfLoopScanLeftOne_acceptPhase_val : (selfLoopScanLeftOne.acceptPhase : Nat) = 1 := rfl

/-- The leftward scan-over-`1`s never moves the head right: it moves left while scanning a `1`,
otherwise stays (on the terminating `0`, or in the done phase).  Dual confinement fact. -/
theorem selfLoopScanLeftOne_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopScanLeftOne.transition i s b).2.2.2 ≠ Move.right := by
  unfold selfLoopScanLeftOne
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas (the leftward back-edge step) -/

/-- Scan-phase step on a `1`: the phase stays `0` (the leftward self-loop / back-edge). -/
theorem selfLoopScanLeftOne_stepConfig_scan_one_phase {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit]

/-- Scan-phase step on a `1`: the head moves left (the head-carried leftward scan progresses). -/
theorem selfLoopScanLeftOne_stepConfig_scan_one_head {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit]

/-- Scan-phase step on a `1`: the tape is unchanged (the `1` is written back). -/
theorem selfLoopScanLeftOne_stepConfig_scan_one_tape {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Terminator step on a `0`: jump to the done phase `1`. -/
theorem selfLoopScanLeftOne_stepConfig_stop_zero_phase {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit]

/-- Terminator step on a `0`: the head stays put. -/
theorem selfLoopScanLeftOne_stepConfig_stop_zero_head {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit, Configuration.moveHead]

/-- Terminator step on a `0`: the tape is unchanged. -/
theorem selfLoopScanLeftOne_stepConfig_stop_zero_tape {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanLeftOne, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Boundary characterization (the `Move.left` clamp): at head `0`, a scan step on a `1` leaves the
head at `0` — the scan cannot retreat past the left end of the tape, it clamps.  This makes the
`j ≤ c0.head` / `k < c0.head` preconditions of the run lemmas below necessary.  Explicit clamping lemma
for completeness (dual of `selfLoopScanLeft_stepConfig_scan_zero_head_clamp`). -/
theorem selfLoopScanLeftOne_stepConfig_scan_one_head_clamp {L : Nat}
    (c : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) (hhead0 : (c.head : Nat) = 0) :
    ((TM.stepConfig (M := selfLoopScanLeftOne.toPhased.toTM) c).head : Nat) = 0 := by
  rw [selfLoopScanLeftOne_stepConfig_scan_one_head c hi hstate hbit]
  simp [Configuration.moveHead, hhead0]

/-! ### Leftward scanning run invariant and terminator -/

/-- Leftward scanning invariant: from a start `c0` in scan phase `0`, if the `j` cells just to the left
of and including the head (positions `(c0.head − j, c0.head]`) are all `1`, then after `j ≤ c0.head`
steps the machine is still in scan phase `0`, the head has retreated to `c0.head − j`, and the tape is
unchanged.  The `1`-block dual of `selfLoopScanLeft_runConfig_scanning` (head *decreases*, requiring
`j ≤ c0.head` so each `Move.left` genuinely decrements rather than clamping at `0`). -/
theorem selfLoopScanLeftOne_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (selfLoopScanLeftOne.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanLeftOne_stepConfig_scan_one_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanLeftOne_stepConfig_scan_one_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopScanLeftOne_stepConfig_scan_one_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Leftward terminator: from a start `c0` in scan phase `0`, if the cells `(k, c0.head]` are all `1`
and cell `k` is `0` (`k < c0.head`), then after `(c0.head − k) + 1` steps (`c0.head − k` to retreat to
the marker, one to read it) the machine has stopped at phase `1` with the head resting on the marker
(`head = k`) and the tape unchanged.  The `1`-block dual of `selfLoopScanLeft_runConfig_terminator` — a
verified "return left over a `1`-block to its first `0`" (e.g. the left boundary of a filled
loop-counter). -/
theorem selfLoopScanLeftOne_runConfig_terminator {L : Nat}
    (c0 : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin (selfLoopScanLeftOne.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hterm : ∀ p : Fin (selfLoopScanLeftOne.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).state).fst
        : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).head
          : Nat) = k
      ∧ (TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).tape
          = c0.tape := by
  -- Retreat the `(c0.head − k)`-cell `1`-window down onto the marker, then take the terminator step.
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeftOne_runConfig_scanning c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeftOne_stepConfig_stop_zero_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanLeftOne_stepConfig_stop_zero_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanLeftOne_stepConfig_stop_zero_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### Composition: the leftward scan-over-`1`s as a non-first (P2-region) phase

The right-only `seq`/`seqList` single-step lemmas (`seq_stepConfig_P2_*`) are *transition-generic* — they
do not assume `TMNeverMovesLeft` — so this leftward scan composes as a `seq` phase exactly as
`selfLoopScanLeft` does, with the head *decreasing*.  Gives full composition-API parity with the rest of
the scan family. -/

/-- Scan-over-`1`s step as a non-first phase (composition phase `P1.numPhases`, bit `1`): the phase
stays. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_scan_one_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanLeftOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeftOne, hsub, hbit]

/-- Scan-over-`1`s step as a non-first phase (bit `1`): the head moves left. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_scan_one_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanLeftOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeftOne, hsub, hbit]

/-- Scan-over-`1`s step as a non-first phase (bit `1`): the tape is unchanged. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_scan_one_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanLeftOne c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanLeftOne, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Leftward scanning invariant as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `(c0.head − k, c0.head]` is all `1`, then after `k ≤ c0.head` steps the
phase still rests at `P1.numPhases`, the head has retreated to `c0.head − k`, and the tape is unchanged.
Offset/non-first analogue of `selfLoopScanLeftOne_runConfig_scanning`. -/
theorem selfLoopScanLeftOne_seqP2_runConfig_scanning (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin ((seq P1 selfLoopScanLeftOne).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanLeftOne_seqP2_stepConfig_scan_one_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanLeftOne_seqP2_stepConfig_scan_one_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopScanLeftOne_seqP2_stepConfig_scan_one_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Terminator step as a non-first phase (bit `0`): jump to the shifted done phase `P1.numPhases + 1`. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanLeftOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeftOne, hsub, hbit]

/-- Terminator step as a non-first phase (bit `0`): the head stays put. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanLeftOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanLeftOne, hsub, hbit, Configuration.moveHead]

/-- Terminator step as a non-first phase (bit `0`): the tape is unchanged. -/
theorem selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanLeftOne c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanLeftOne, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Leftward terminator-locating run as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `(k, c0.head]` is all `1` and cell `k` is `0` (`k < c0.head`), then after
`(c0.head − k) + 1` steps the scan has stopped at the shifted done phase `P1.numPhases + 1`, the head
rests on the marker (`k`), and the tape is unchanged.  Gives the leftward scan-over-`1`s full
composition-API parity with the rest of the scan family (seqP2 scanning *and* terminator). -/
theorem selfLoopScanLeftOne_seqP2_runConfig_terminator (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin ((seq P1 selfLoopScanLeftOne).toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hterm : ∀ p : Fin ((seq P1 selfLoopScanLeftOne).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0
        (((c0.head : Nat) - k) + 1)).state).fst : Nat) = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeftOne_seqP2_runConfig_scanning P1 c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopScanLeftOne).toPhased.toTM) c0 ((c0.head : Nat) - k)
    with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### Depth-4 composition lift: leftward scan-over-`1`s as element 4 of a seqList (`seqNested3`)

In the flattened binary→unary loop body the *fourth* element `selfLoopScanLeftOne` sits at chain-depth 4
(`seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))`).  A step there peels three outer `seq` levels:
the outer `seq_stepConfig_P2_*` produces the middle transition, and a single
`simp [seq, selfLoopScanLeftOne, hsub, hc1, …]` then navigates the two further `seq` levels — the first
middle comparison `Q.numPhases + Q2.numPhases < Q.numPhases` is *not* of the `a < a` shape, so its
negation `hc1` is supplied explicitly (the depth-3 case closed via `lt_self_iff_false` alone). -/

/-- Depth-4 scan-over-`1`s step (bit `1`): the phase stays at `P1.numPhases + Q.numPhases + Q2.numPhases`. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_phase
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + Q.numPhases + Q2.numPhases := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit]
  omega

/-- Depth-4 scan-over-`1`s step (bit `1`): the head moves left. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_head
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit]

/-- Depth-4 scan-over-`1`s step (bit `1`): the tape is unchanged. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_tape
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
    simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Depth-4 leftward scanning invariant from an arbitrary start `c0` (phase
`P1.numPhases + Q.numPhases + Q2.numPhases`): if the window `(c0.head − k, c0.head]` is all `1`, then
after `k ≤ c0.head` steps the phase still rests, the head has retreated to `c0.head − k`, and the tape is
unchanged.  Depth-4 analogue of `selfLoopScanLeftOne_seqP2_runConfig_scanning`. -/
theorem selfLoopScanLeftOne_seqNested3_runConfig_scanning
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases + Q.numPhases + Q2.numPhases) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin ((seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases + Q.numPhases + Q2.numPhases
      ∧ ((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0 k).tape
          = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0 k
        with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_phase P1 Q Q2 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_head P1 Q Q2 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopScanLeftOne_seqNested3_stepConfig_scan_one_tape P1 Q Q2 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Depth-4 terminator step (bit `0`): jump to the shifted done phase
`P1.numPhases + Q.numPhases + Q2.numPhases + 1`. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_phase
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + Q.numPhases + Q2.numPhases + 1 := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit]
  omega

/-- Depth-4 terminator step (bit `0`): the head stays put. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_head
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).head
      = c.head := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit, Configuration.moveHead]

/-- Depth-4 terminator step (bit `0`): the tape is unchanged. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_tape
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases < Q.numPhases) := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
    simp [seq, selfLoopScanLeftOne, hsub, hc1, Nat.add_sub_cancel_left, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Depth-4 leftward terminator-locating run from an arbitrary start `c0` (phase
`P1.numPhases + Q.numPhases + Q2.numPhases`): if the window `(k, c0.head]` is all `1` and cell `k` is
`0` (`k < c0.head`), then after `(c0.head − k) + 1` steps the scan has stopped at the shifted done phase,
the head rests on the marker (`k`), and the tape is unchanged.  Depth-4 analogue of
`selfLoopScanLeftOne_seqP2_runConfig_terminator`. -/
theorem selfLoopScanLeftOne_seqNested3_runConfig_terminator
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases + Q.numPhases + Q2.numPhases)
    (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin ((seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hterm : ∀ p : Fin ((seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0
        (((c0.head : Nat) - k) + 1)).state).fst : Nat)
        = P1.numPhases + Q.numPhases + Q2.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeftOne_seqNested3_runConfig_scanning P1 Q Q2 R c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c0
    ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_phase P1 Q Q2 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_head P1 Q Q2 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_tape P1 Q Q2 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### Depth-4 accept→successor handoff

After the leftward scan stops (phase `P1.numPhases + Q.numPhases + Q2.numPhases + 1`, the scan's accept),
the composed machine hands off to the successor `R` (in the binary→unary body, the second `stepLeftOnce`
of the home-seek).  These lemmas characterize that handoff on `seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))`,
the depth-4 analogue of `stepLeftOnce_seqNested2_stepConfig_handoff_*`. -/

/-- Depth-4 handoff (phase `P1.numPhases + Q.numPhases + Q2.numPhases + 1`): advance to the successor's
shifted start. -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_handoff_phase
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).state).fst.val
      = P1.numPhases + (Q.numPhases + (Q2.numPhases + (selfLoopScanLeftOne.numPhases + R.startPhase.val))) := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + Q2.numPhases + 1 - Q.numPhases = Q2.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + 1 < Q2.numPhases) := by omega
  have hsub3 : Q2.numPhases + 1 - Q2.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, hsub2, hc2, hsub3]

/-- Depth-4 handoff: the head is unchanged (handoff stays put). -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_handoff_head
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).head
      = c.head := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + Q2.numPhases + 1 - Q.numPhases = Q2.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + 1 < Q2.numPhases) := by omega
  have hsub3 : Q2.numPhases + 1 - Q2.numPhases = 1 := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanLeftOne, hsub, hc1, hsub2, hc2, hsub3, Configuration.moveHead]

/-- Depth-4 handoff: the tape is unchanged (scanned bit written back). -/
theorem selfLoopScanLeftOne_seqNested3_stepConfig_handoff_tape
    (P1 Q Q2 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases = Q.numPhases + Q2.numPhases + 1 := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + 1 < Q.numPhases) := by omega
  have hsub2 : Q.numPhases + Q2.numPhases + 1 - Q.numPhases = Q2.numPhases + 1 := by omega
  have hc2 : ¬ (Q2.numPhases + 1 < Q2.numPhases) := by omega
  have hsub3 : Q2.numPhases + 1 - Q2.numPhases = 1 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, selfLoopScanLeftOne_numPhases]; omega) hstate]
    simp [seq, selfLoopScanLeftOne, hsub, hc1, hsub2, hc2, hsub3]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
