import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftProgram

/-!
# The leftward scan as the **first** `seq` phase — D2t-5b (Block A5m-1a)

The corridor navigation legs (`corridor_scan_M_to_ctrlTop`, …) are stated on `selfLoopScanLeft`'s
own machine.  The driver arms run it as the **first** component of a `seq` composition, so its run
behaviour must transfer into the composite's P1 region: phases `0`/`1` lie below
`selfLoopScanLeft.numPhases = 2`, the scan loops in phase `0` (≠ accept `1`), the terminator step
enters the accept phase, and one further **handoff** step jumps to `P2`'s shifted start with the
local state re-initialised — head and tape untouched.

`selfLoopScanLeft_seq_runConfig_terminator_handoff` packages the whole leg: from a phase-`0` start
at head `h₀`, a `1`-marker at `k < h₀` with all-`0` cells in between, after `(h₀ − k) + 2` steps the
composite rests at `P2`'s start phase (`2 + P2.startPhase`), state `P2.startState`, head on the
marker, tape unchanged — exactly the configuration `P2`'s `seqP2`/`runConfigFrom` lemmas consume.

**Progress classification (AGENTS.md): Infrastructure** — composition transfer for a verifier
machine component; builds no verifier and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Single steps in the composite's P1 region -/

/-- Scan step on a `0` (P1 region): the phase stays `0`. -/
theorem scanLeftSeq_stepConfig_zero_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = false) :
    (((TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).state).fst : Nat) = 0 := by
  have h := seq_stepConfig_P1_normal_phase selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  simp [selfLoopScanLeft, hph, hbit]

/-- Scan step on a `0` (P1 region): the head moves left. -/
theorem scanLeftSeq_stepConfig_zero_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).head
      = c.moveHead Move.left := by
  have h := seq_stepConfig_P1_normal_head selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  congr 1
  simp [selfLoopScanLeft, hph, hbit]

/-- Scan step on a `0` (P1 region): the tape is unchanged (writes back the scanned bit). -/
theorem scanLeftSeq_stepConfig_zero_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).tape = c.tape := by
  have h := seq_stepConfig_P1_normal_tape selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  have hb : (selfLoopScanLeft.transition ⟨(c.state.fst : Nat), by simp [hph]⟩ c.state.snd
      (c.tape c.head)).snd.snd.fst = c.tape c.head := by
    simp [selfLoopScanLeft, hph, hbit]
  rw [hb]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Terminator step on a `1` (P1 region): the phase advances to the accept phase `1`. -/
theorem scanLeftSeq_stepConfig_one_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = true) :
    (((TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).state).fst : Nat) = 1 := by
  have h := seq_stepConfig_P1_normal_phase selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  simp [selfLoopScanLeft, hph, hbit]

/-- Terminator step on a `1` (P1 region): the head stays. -/
theorem scanLeftSeq_stepConfig_one_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).head = c.head := by
  have h := seq_stepConfig_P1_normal_head selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  have hm : (selfLoopScanLeft.transition ⟨(c.state.fst : Nat), by simp [hph]⟩ c.state.snd
      (c.tape c.head)).snd.snd.snd = Move.stay := by
    simp [selfLoopScanLeft, hph, hbit]
  rw [hm]
  simp [Configuration.moveHead]

/-- Terminator step on a `1` (P1 region): the tape is unchanged. -/
theorem scanLeftSeq_stepConfig_one_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hph : (c.state.fst : Nat) = 0) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c).tape = c.tape := by
  have h := seq_stepConfig_P1_normal_tape selfLoopScanLeft P2 c
    (i := c.state.fst) (q := c.state.snd) (by simp [hph]) (by simp [hph]) rfl
  rw [h]
  have hb : (selfLoopScanLeft.transition ⟨(c.state.fst : Nat), by simp [hph]⟩ c.state.snd
      (c.tape c.head)).snd.snd.fst = c.tape c.head := by
    simp [selfLoopScanLeft, hph, hbit]
  rw [hb]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### The composed runs -/

/-- **P1-region scanning**: from a phase-`0` start, `j` all-`0` cells retreat the head `j` cells
left, phase and tape unchanged — `selfLoopScanLeft_runConfig_scanning` inside the composite. -/
theorem selfLoopScanLeft_seq_runConfig_scanning (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin ((seq selfLoopScanLeft P2).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact scanLeftSeq_stepConfig_zero_phase P2 c hph hbit
      · rw [scanLeftSeq_stepConfig_zero_head P2 c hph hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [scanLeftSeq_stepConfig_zero_tape P2 c hph hbit, htp]

/-- **The full P1 leg with handoff**: from a phase-`0` start at head `h₀`, with a `1`-marker at
`k < h₀` and all-`0` cells in between, after `(h₀ − k) + 2` steps (retreat, read the marker, hand
off) the composite rests at `P2`'s shifted start phase with state `P2.startState`, head on the
marker, tape unchanged. -/
theorem selfLoopScanLeft_seq_runConfig_terminator_handoff (P2 : ConstStatePhasedProgram Unit)
    {L : Nat}
    (c0 : Configuration (M := (seq selfLoopScanLeft P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : k < (c0.head : Nat))
    (hzeros : ∀ p : Fin ((seq selfLoopScanLeft P2).toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false)
    (hterm : ∀ p : Fin ((seq selfLoopScanLeft P2).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = true) :
    (((TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0
        (((c0.head : Nat) - k) + 2)).state).fst : Nat) = 2 + (P2.startPhase : Nat)
      ∧ ((TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 2)).state).snd = P2.startState
      ∧ ((TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 2)).head : Nat) = k
      ∧ (TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0
          (((c0.head : Nat) - k) + 2)).tape = c0.tape := by
  -- Retreat onto the marker.
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanLeft_seq_runConfig_scanning P2 c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hzeros p (by omega) hp2)
  have hsteps : ((c0.head : Nat) - k) + 2 = (((c0.head : Nat) - k) + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c0
    ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhdk
  -- The terminator step: phase 0 → 1, head/tape kept.
  set c1 := TM.stepConfig (M := (seq selfLoopScanLeft P2).toPhased.toTM) c with hc1
  have hph1 : (c1.state.fst : Nat) = 1 := scanLeftSeq_stepConfig_one_phase P2 c hph hbit
  have hhd1 : c1.head = c.head := scanLeftSeq_stepConfig_one_head P2 c hph hbit
  have htp1 : c1.tape = c.tape := scanLeftSeq_stepConfig_one_tape P2 c hph hbit
  -- The handoff step: phase 1 (= accept) → 2 + P2.startPhase, state reset, head/tape kept.
  have hacc : (c1.state.fst : Nat) = (selfLoopScanLeft.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := seq_stepConfig_P1_accept_phase selfLoopScanLeft P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
    rw [h]
    rfl
  · exact seq_stepConfig_P1_accept_state selfLoopScanLeft P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
  · rw [seq_stepConfig_P1_accept_head selfLoopScanLeft P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl, hhd1]
    exact hhdk
  · rw [seq_stepConfig_P1_accept_tape selfLoopScanLeft P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl, htp1]
    exact htp

end ContractExpansion
end Frontier
end Pnp4
