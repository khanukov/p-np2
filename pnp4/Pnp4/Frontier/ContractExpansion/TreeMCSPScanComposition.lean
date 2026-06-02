import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Lifting the self-loop gamma scan into a composition (NP-verifier track, assembly milestone)

Companion to `TreeMCSPCounterComposition.lean`, which lifted the *counter* (`selfLoopIncrement`) into a
composition.  Here we do the same for the **gamma scan** (`gammaSelfLoopScan`) — a structurally
*different* self-loop: it scans right over a unary `0`-prefix **without writing**, then stops on the
first `1` (the gamma terminator), pinning the unary-prefix length as a head offset.  The gamma scan is
`M`'s phase right after the tag check, so its composition-survival is directly on the assembly path.

Per the cross-type caveat (`TM_VERIFIER_STRATEGY.md` §6a), the standalone `gammaSelfLoopScan_*` lemmas
do not transfer to `seq gammaSelfLoopScan P2` for free; we re-derive, on the composed machine, the
single-step scan/terminator/handoff lemmas (phase `0` is P1-*normal*, accept phase is `1`), the
scanning run invariant, the terminator-locating result, and the P1→P2 handoff.  This is the same
per-instance template as the counter lift, validating it across a *different* self-loop shape (no-write
scan + locate vs write + count).

Builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` execution triple. -/

@[simp] theorem gammaSelfLoopScan_numPhases : gammaSelfLoopScan.numPhases = 2 := rfl

@[simp] theorem gammaSelfLoopScan_acceptPhase_val : gammaSelfLoopScan.acceptPhase.val = 1 := rfl

@[simp] theorem gammaSelfLoopScan_startPhase_val : gammaSelfLoopScan.startPhase.val = 0 := rfl

/-! ### Single-step scan lemmas on `seq gammaSelfLoopScan P2` (phase `0`, the back-edge) -/

/-- Scan step inside the composition (phase `0`, bit `0`): the phase stays `0` (back-edge survives). -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_zero_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).state).fst.val = 0 := by
  rw [seq_stepConfig_P1_normal_phase gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [gammaSelfLoopScan, hi, hbit]

/-- Scan step inside the composition (phase `0`, bit `0`): the head advances right. -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_zero_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  rw [seq_stepConfig_P1_normal_head gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [gammaSelfLoopScan, hi, hbit]

/-- Scan step inside the composition (phase `0`, bit `0`): the tape is unchanged (the `0` is written
back). -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_zero_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P1_normal_tape gammaSelfLoopScan P2 c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [gammaSelfLoopScan, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-! ### Single-step terminator lemmas on `seq gammaSelfLoopScan P2` (phase `0`, reading the first `1`) -/

/-- Terminator step inside the composition (phase `0`, bit `1`): the phase jumps to `1`. -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_one_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [gammaSelfLoopScan, hi, hbit]

/-- Terminator step inside the composition (phase `0`, bit `1`): the head stays put. -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_one_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_normal_head gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [gammaSelfLoopScan, hi, hbit, Configuration.moveHead]

/-- Terminator step inside the composition (phase `0`, bit `1`): the tape is unchanged. -/
theorem gammaSelfLoopScan_seq_stepConfig_scan_one_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P1_normal_tape gammaSelfLoopScan P2 c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [gammaSelfLoopScan, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-! ### The scanning run invariant and terminator on the composed machine -/

/-- Scanning invariant on the composed machine: if the first `k` cells are `0`, then after `k ≤ L`
steps of `seq gammaSelfLoopScan P2` the machine is still in scan phase `0`, head advanced to `k`, tape
unchanged.  Mirrors `gammaSelfLoopScan_runConfig_scanning` with the composition single-steps. -/
theorem gammaSelfLoopScan_seq_runConfig_scanning (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin ((seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape p = false) →
      (((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) k).tape
          = ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp => h0 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
        ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < (seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + (L + P2.timeBound L + 1) + 1; omega
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopScan_seq_stepConfig_scan_zero_phase P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopScan_seq_stepConfig_scan_zero_head P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaSelfLoopScan_seq_stepConfig_scan_zero_tape P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Terminator on the composed machine: if the first `z` cells are `0` and cell `z` is `1` (`z ≤ L`),
then after `z + 1` steps of `seq gammaSelfLoopScan P2` the machine has reached phase `1` with the head
resting on the terminator (`head = z`) and the tape unchanged.  Mirrors
`gammaSelfLoopScan_runConfig_terminator`. -/
theorem gammaSelfLoopScan_seq_runConfig_terminator (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (z : Nat) (hz : z ≤ L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L),
      (p : Nat) < z → ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L),
      (p : Nat) = z → ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
        ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 1)).head : Nat) = z
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 1)).tape
          = ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph, hhd, htp⟩ := gammaSelfLoopScan_seq_runConfig_scanning P2 x z hz hzeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
    ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) z with hc
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhd
  refine ⟨?_, ?_, ?_⟩
  · exact gammaSelfLoopScan_seq_stepConfig_scan_one_phase P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [gammaSelfLoopScan_seq_stepConfig_scan_one_head P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [gammaSelfLoopScan_seq_stepConfig_scan_one_tape P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### The P1→P2 handoff after the scan locates the terminator -/

/-- Handoff step (phase `1`): the phase jumps to `P2`'s shifted start. -/
theorem gammaSelfLoopScan_seq_stepConfig_handoff_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).state).fst.val
      = 2 + P2.startPhase.val := by
  rw [seq_stepConfig_P1_accept_phase gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate,
    gammaSelfLoopScan_numPhases]

/-- Handoff step (phase `1`): the head is unchanged. -/
theorem gammaSelfLoopScan_seq_stepConfig_handoff_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_accept_head gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]

/-- Handoff step (phase `1`): the tape is unchanged. -/
theorem gammaSelfLoopScan_seq_stepConfig_handoff_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq gammaSelfLoopScan P2).toPhased.toTM) L)
    {i : Fin (seq gammaSelfLoopScan P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM) c).tape = c.tape := by
  rw [seq_stepConfig_P1_accept_tape gammaSelfLoopScan P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]

/-- Scan-then-handoff on the composed machine: after `z + 2` steps of `seq gammaSelfLoopScan P2`
(`z + 1` for the scan to locate the terminator, one for the handoff), control sits at `P2`'s shifted
start phase, the head rests on the terminator (`head = z`, the unary-prefix length), and the tape is
unchanged.  This is the complete "scan done, next phase begins at the located terminator" composition
unit — `M`'s gamma phase handing control to whatever decodes the payload. -/
theorem gammaSelfLoopScan_seq_runConfig_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (z : Nat) (hz : z ≤ L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L),
      (p : Nat) < z → ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan P2).toPhased.toTM.tapeLength L),
      (p : Nat) = z → ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
        ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 2)).state).fst : Nat)
        = 2 + P2.startPhase.val
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 2)).head : Nat) = z
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
          ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 2)).tape
          = ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph1, hhd1, htp1⟩ := gammaSelfLoopScan_seq_runConfig_terminator P2 x z hz hzeros hterm
  have hsucc : z + 2 = (z + 1) + 1 := by omega
  rw [hsucc, TM.runConfig_succ]
  set c1 := TM.runConfig (M := (seq gammaSelfLoopScan P2).toPhased.toTM)
    ((seq gammaSelfLoopScan P2).toPhased.toTM.initialConfig x) (z + 1) with hc1
  refine ⟨?_, ?_, ?_⟩
  · exact gammaSelfLoopScan_seq_stepConfig_handoff_phase P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl
  · rw [gammaSelfLoopScan_seq_stepConfig_handoff_head P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact hhd1
  · rw [gammaSelfLoopScan_seq_stepConfig_handoff_tape P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact htp1

end ContractExpansion
end Frontier
end Pnp4
