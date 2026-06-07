import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroFullScan

/-!
# `bZeroFullScanRouteBody` as a depth-2 (`P2∘P1`) `seq` phase (NP-verifier track — D2t-3 `ε`)

In the sound conversion loop body `seq stepRightOnce (seq (bZeroFullScanRouteBody w) R)`
(`TreeMCSPBinToUnaryLoopFullScan.lean`) the scan sits as **P1 of the inner `seq`, P2 of the outer** —
i.e. at composition depth 2.  This module lifts the scan's run-through to that position, the
doubly-nested analogue of `bZeroFullScan_seqP2_runConfig_*` (`TreeMCSPBZeroFullScanComposition.lean`),
mirroring `gammaSelfLoopScan_seqNested_runConfig_scanning` (`TreeMCSPScanComposition.lean`).

The scan **advances its phase** each step, so the single-step lemmas are parameterised by the local
phase `p` and the scanning invariant tracks the composition phase `P1.numPhases + j`.  Because the inner
`seq` is `seq (bZeroFullScanRouteBody w) R`, the seq handoff check is `current phase = w + 1`
(`bZeroFullScanRouteBody`'s accept); for `p < w` this is `False`, so the inner `seq` runs
`bZeroFullScan`'s transition (and on `B > 0` lands at `P1.numPhases + w + 1`, whence the next step hands
off into `R`).

**Progress classification (AGENTS.md): Infrastructure** — composition lift toward the NP-membership leg;
standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Single-step lemmas at depth 2 (parameterised by the local scan phase `p`) -/

/-- **Scan step (read `0`) at depth 2.**  At composition phase `P1.numPhases + p` (`p < w`), advance to
`P1.numPhases + p + 1`. -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_scan_phase
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).state).fst.val
      = P1.numPhases + p + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq (bZeroFullScanRouteBody w) R) c
      (h2 := by omega)
      (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
  simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2, Nat.add_assoc]

/-- **Scan step (read `0`) at depth 2.**  Advance the head by one. -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_scan_head
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1
      < (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  rw [seq_stepConfig_P2_head P1 (seq (bZeroFullScanRouteBody w) R) c
      (h2 := by omega)
      (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
  have hmove : ((seq (bZeroFullScanRouteBody w) R).transition
      ⟨i.val - P1.numPhases, by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega⟩
      s (c.tape c.head)).2.2.2 = Move.right := by
    simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- **Scan step (read `0`) at depth 2.**  The tape is unchanged. -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_scan_tape
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = p := by omega
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 (seq (bZeroFullScanRouteBody w) R) c
        (h2 := by omega)
        (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
    simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- **Divert step (read `1`) at depth 2.**  At composition phase `P1.numPhases + p` (`p < w`), jump to
`P1.numPhases + w + 1` (`bZeroFullScanRouteBody`'s accept = `B > 0`). -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_divert_phase
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).state).fst.val
      = P1.numPhases + w + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  rw [seq_stepConfig_P2_phase P1 (seq (bZeroFullScanRouteBody w) R) c
      (h2 := by omega)
      (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
  simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2, Nat.add_assoc]

/-- **Divert step (read `1`) at depth 2.**  The head stays put. -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_divert_head
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = p := by omega
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  rw [seq_stepConfig_P2_head P1 (seq (bZeroFullScanRouteBody w) R) c
      (h2 := by omega)
      (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
  have hmove : ((seq (bZeroFullScanRouteBody w) R).transition
      ⟨i.val - P1.numPhases, by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega⟩
      s (c.tape c.head)).2.2.2 = Move.stay := by
    simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2]
  rw [hmove]
  simp [Configuration.moveHead]

/-- **Tape unchanged at depth 2** (any inner-scan phase `p < w`). -/
theorem bZeroFullScanRouteBody_seqNested_stepConfig_tape
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    {i : Fin (seq P1 (seq (bZeroFullScanRouteBody w) R)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).tape = c.tape := by
  rcases Bool.eq_false_or_eq_true (c.tape c.head) with hbit | hbit
  · have hsub : i.val - P1.numPhases = p := by omega
    have hne : ¬ (p = w + 1) := by omega
    have hlt2 : p < w + 2 := by omega
    have hwrite : (TM.stepConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c).tape
        = c.write c.head true := by
      rw [seq_stepConfig_P2_tape P1 (seq (bZeroFullScanRouteBody w) R) c
          (h2 := by omega)
          (hlt := by rw [hsub, seq_numPhases, bZeroFullScanRouteBody_numPhases]; omega) hstate]
      simp [seq, bZeroFullScanRouteBody, bZeroFullScan, hsub, hbit, hp, hne, hlt2]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write, hbit]
    · simp [Configuration.write, hj]
  · exact bZeroFullScanRouteBody_seqNested_stepConfig_scan_tape P1 R w c hp hi hstate hbit

/-! ### Run-through at depth 2 -/

/-- **Scanning invariant at depth 2.**  From `c0` at composition phase `P1.numPhases`, if the `j` cells
from the head are all `0` (`j ≤ w`, in bounds), then after `j` steps the composition phase is
`P1.numPhases + j`, the head is at `c0.head + j`, and the tape is unchanged. -/
theorem bZeroFullScanRouteBody_seqNested_runConfig_scanning
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c0 : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ j : Nat, j ≤ w →
      (c0.head : Nat) + j < (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L →
      (∀ q : Fin ((seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + j → c0.tape q = false) →
      (((TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 j).state).fst
          : Nat) = P1.numPhases + j
      ∧ ((TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 j).tape
          = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨by simpa using hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun q hq1 hq2 => h0 q hq1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 j with hc
      have hbnd : (c.head : Nat) + 1
          < (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L := by rw [hhd]; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hpj : j < w := by omega
      have hiph : (c.state.fst : Nat) = P1.numPhases + j := hph
      refine ⟨?_, ?_, ?_⟩
      · rw [bZeroFullScanRouteBody_seqNested_stepConfig_scan_phase P1 R w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit]
        omega
      · rw [bZeroFullScanRouteBody_seqNested_stepConfig_scan_head P1 R w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit hbnd]
        omega
      · rw [bZeroFullScanRouteBody_seqNested_stepConfig_tape P1 R w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl, htp]

/-- **`B = 0` run-through at depth 2.**  All `w` cells `0` ⇒ after `w` steps the composition phase rests
at `P1.numPhases + w` (`B = 0`), head at `c0.head + w`, tape unchanged. -/
theorem bZeroFullScanRouteBody_seqNested_runConfig_zero
    (P1 R : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c0 : Configuration (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases)
    (hb : (c0.head : Nat) + w < (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L)
    (hzeros : ∀ q : Fin ((seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + w → c0.tape q = false) :
    (((TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 w).state).fst
        : Nat) = P1.numPhases + w
      ∧ ((TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 w).head : Nat)
          = (c0.head : Nat) + w
      ∧ (TM.runConfig (M := (seq P1 (seq (bZeroFullScanRouteBody w) R)).toPhased.toTM) c0 w).tape
          = c0.tape :=
  bZeroFullScanRouteBody_seqNested_runConfig_scanning P1 R w c0 hphase w (le_refl w) hb hzeros

end ContractExpansion
end Frontier
end Pnp4
