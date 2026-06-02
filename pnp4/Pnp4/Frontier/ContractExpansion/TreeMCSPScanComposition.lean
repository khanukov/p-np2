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

/-! ## Lifting the gamma scan into the P2 region (a non-first phase)

Mirrors the counter P2-region lifts for the scan: when `gammaSelfLoopScan` is the *second* component
`seq P1 gammaSelfLoopScan`, phase `P1.numPhases` is its scan phase, governed by `seq_stepConfig_P2_*`.
Completes the self-loop family's composition coverage — every self-loop now composes in *either* `seq`
position. -/

/-- Scan step as a non-first phase (composition phase `P1.numPhases`, bit `0`): the phase stays. -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_zero_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 gammaSelfLoopScan c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopScan, hsub, hbit]

/-- Scan step as a non-first phase (bit `0`): the head advances right. -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_zero_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 gammaSelfLoopScan c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopScan, hsub, hbit]

/-- Scan step as a non-first phase (bit `0`): the tape is unchanged (the `0` is written back). -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_zero_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 gammaSelfLoopScan c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [gammaSelfLoopScan, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Terminator step as a non-first phase (bit `1`): jump to the shifted accept phase. -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_one_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 gammaSelfLoopScan c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopScan, hsub, hbit]

/-- Terminator step as a non-first phase (bit `1`): the head stays put. -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_one_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 gammaSelfLoopScan c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopScan, hsub, hbit, Configuration.moveHead]

/-- Terminator step as a non-first phase (bit `1`): the tape is unchanged. -/
theorem gammaSelfLoopScan_seqP2_stepConfig_scan_one_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopScan).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 gammaSelfLoopScan c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [gammaSelfLoopScan, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Scanning invariant as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`): if
the window `[c0.head, c0.head + k)` is all `0`, then after `k` steps the phase still rests at
`P1.numPhases`, the head has advanced to `c0.head + k`, and the tape is unchanged.  Offset/non-first
analogue of `gammaSelfLoopScan_seq_runConfig_scanning`. -/
theorem gammaSelfLoopScan_seqP2_runConfig_scanning (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k ≤ L →
      (∀ p : Fin ((seq P1 gammaSelfLoopScan).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 k with hc
      have hbnd : (c.head : Nat) + 1 < (seq P1 gammaSelfLoopScan).toPhased.toTM.tapeLength L := by
        rw [hhd]; show (c0.head : Nat) + k + 1 < L + (P1.timeBound L + L + 1) + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopScan_seqP2_stepConfig_scan_zero_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopScan_seqP2_stepConfig_scan_zero_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaSelfLoopScan_seqP2_stepConfig_scan_zero_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Terminator-locating run as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`):
if the window `[c0.head, c0.head + z)` is all `0` and the cell at `c0.head + z` is `1`, then after
`z + 1` steps the scan has stopped at phase `P1.numPhases + 1` (the gamma scan's shifted accept phase),
the head rests on the terminator (`c0.head + z`), and the tape is unchanged.  Offset/non-first analogue
of `gammaSelfLoopScan_seq_runConfig_terminator`. -/
theorem gammaSelfLoopScan_seqP2_runConfig_terminator (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (z : Nat) (hz : (c0.head : Nat) + z ≤ L)
    (hzeros : ∀ p : Fin ((seq P1 gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin ((seq P1 gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true) :
    (((TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 (z + 1)).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 (z + 1)).head : Nat)
          = (c0.head : Nat) + z
      ∧ (TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 (z + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := gammaSelfLoopScan_seqP2_runConfig_scanning P1 c0 hphase z hz hzeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 gammaSelfLoopScan).toPhased.toTM) c0 z with hc
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhd
  refine ⟨?_, ?_, ?_⟩
  · exact gammaSelfLoopScan_seqP2_stepConfig_scan_one_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [gammaSelfLoopScan_seqP2_stepConfig_scan_one_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [gammaSelfLoopScan_seqP2_stepConfig_scan_one_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ## Transitively-nested composition: the gamma scan in the P2∘P1 position

For `seqList` of length ≥ 3 the gamma scan sits in a *doubly-nested* position: it is the first
component (P1) of an inner `seq gammaSelfLoopScan R`, which is itself the non-first component (P2) of
an outer `seq P1 (seq gammaSelfLoopScan R)`.  (E.g. `mSkeletonU = seq tagCheckProgramU (seqList
[gammaSelfLoopScan, selfLoopIncrement])` and `seqList [gammaSelfLoopScan, selfLoopIncrement] = seq
gammaSelfLoopScan (seqList [selfLoopIncrement])`.)  A step there is the outer P2-region step
(`seq_stepConfig_P2_*`) feeding the inner P1-normal transition (`seq_transition_P1_normal_*`).  These
lemmas re-derive the scan in that position, proving the composition layer chains to *any* depth. -/

/-- Nested scan step (outer phase `P1.numPhases`, inner gamma-scan phase `0`, bit `0`): the phase
stays `P1.numPhases`. -/
theorem gammaSelfLoopScan_seqNested_stepConfig_scan_zero_phase
    (P1 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq gammaSelfLoopScan R)).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq gammaSelfLoopScan R) c
      (h2 := hi.ge) (hlt := by rw [hsub, seq_numPhases, gammaSelfLoopScan_numPhases]; omega) hstate]
  simp [seq, gammaSelfLoopScan, hsub, hbit]

/-- Nested scan step (bit `0`): the head advances right. -/
theorem gammaSelfLoopScan_seqNested_stepConfig_scan_zero_head
    (P1 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq gammaSelfLoopScan R)).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 (seq gammaSelfLoopScan R) c
      (h2 := hi.ge) (hlt := by rw [hsub, seq_numPhases, gammaSelfLoopScan_numPhases]; omega) hstate]
  simp [seq, gammaSelfLoopScan, hsub, hbit]

/-- Nested scan step (bit `0`): the tape is unchanged (the `0` is written back). -/
theorem gammaSelfLoopScan_seqNested_stepConfig_scan_zero_tape
    (P1 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq gammaSelfLoopScan R)).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 (seq gammaSelfLoopScan R) c
        (h2 := hi.ge) (hlt := by rw [hsub, seq_numPhases, gammaSelfLoopScan_numPhases]; omega) hstate]
    simp [seq, gammaSelfLoopScan, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Nested terminator step (bit `1`): jump to the inner gamma scan's shifted accept phase
`P1.numPhases + 1`. -/
theorem gammaSelfLoopScan_seqNested_stepConfig_scan_one_phase
    (P1 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq gammaSelfLoopScan R)).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq gammaSelfLoopScan R) c
      (h2 := hi.ge) (hlt := by rw [hsub, seq_numPhases, gammaSelfLoopScan_numPhases]; omega) hstate]
  simp [seq, gammaSelfLoopScan, hsub, hbit]

/-- Nested scanning invariant from an arbitrary start `c0` (outer phase `P1.numPhases`): if the window
`[c0.head, c0.head + k)` is all `0`, then after `k` steps the phase still rests at `P1.numPhases`, the
head has advanced to `c0.head + k`, and the tape is unchanged.  The doubly-nested (P2∘P1) analogue of
`gammaSelfLoopScan_seqP2_runConfig_scanning` — confirming the scan composes at depth ≥ 2. -/
theorem gammaSelfLoopScan_seqNested_runConfig_scanning (P1 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k ≤ L →
      (∀ p : Fin ((seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM) c0 k with hc
      have hbnd : (c.head : Nat) + 1
          < (seq P1 (seq gammaSelfLoopScan R)).toPhased.toTM.tapeLength L := by
        rw [hhd]
        show (c0.head : Nat) + k + 1 < L + (P1.timeBound L + (L + R.timeBound L + 1) + 1) + 1
        omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopScan_seqNested_stepConfig_scan_zero_phase P1 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopScan_seqNested_stepConfig_scan_zero_head P1 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaSelfLoopScan_seqNested_stepConfig_scan_zero_tape P1 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
