import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroFullScan

/-!
# `bZeroFullScan` as a non-first `seq` phase (NP-verifier track — D2t-3 `ε`, seqP2 lift)

`bZeroFullScan` (the sound width-`w` `B = 0` test, `TreeMCSPBZeroFullScan.lean`) must run **inside** the
conversion loop, where it sits as the head component of `seq (bZeroFullScanRouteBody w) rest` — i.e. as a
**non-first** program in a `seq` chain, started from an arbitrary configuration at composition phase
`P1.numPhases`.  This module re-derives its run-through in that P2-region, the offset analogue of the
standalone `bZeroFullScan_runConfig_{scanning,zero,pos}`, mirroring `gammaSelfLoopScan_seqP2_runConfig_*`
(`TreeMCSPScanComposition.lean`).

The only structural difference from `gammaSelfLoopScan`'s lift is that this scanner **advances its phase**
each step (`p → p+1`), so the single-step lemmas are parameterised by the local phase `p` (`= i.val −
P1.numPhases`), and the scanning invariant tracks the composition phase `P1.numPhases + j`.

**Progress classification (AGENTS.md): Infrastructure** — composition lift toward the NP-membership leg;
it builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

universe u

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Single-step lemmas in the P2 region (parameterised by the local scan phase `p`) -/

/-- **Scan step (read `0`) as a non-first phase.**  At composition phase `P1.numPhases + p` (`p < w`)
reading `0`, advance to composition phase `P1.numPhases + p + 1`. -/
theorem bZeroFullScan_seqP2_stepConfig_scan_phase (P1 : ConstStatePhasedProgram Unit) (w : Nat)
    {L : Nat} (c : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    {i : Fin (seq P1 (bZeroFullScan w)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).state).fst.val
      = P1.numPhases + p + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  rw [seq_stepConfig_P2_phase P1 (bZeroFullScan w) c
      (h2 := by omega) (hlt := by rw [hsub]; show p < w + 2; omega) hstate]
  simp [bZeroFullScan, hsub, hbit, hp, Nat.add_assoc]

/-- **Scan step (read `0`) as a non-first phase.**  Advance the head by one. -/
theorem bZeroFullScan_seqP2_stepConfig_scan_head (P1 : ConstStatePhasedProgram Unit) (w : Nat)
    {L : Nat} (c : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    {i : Fin (seq P1 (bZeroFullScan w)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < (seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  rw [seq_stepConfig_P2_head P1 (bZeroFullScan w) c
      (h2 := by omega) (hlt := by rw [hsub]; show p < w + 2; omega) hstate]
  have hmove : ((bZeroFullScan w).transition ⟨i.val - P1.numPhases, by rw [hsub]; show p < w + 2; omega⟩
      s (c.tape c.head)).2.2.2 = Move.right := by
    simp [bZeroFullScan, hsub, hbit, hp, Nat.add_assoc]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- **Divert step (read `1`) as a non-first phase.**  At composition phase `P1.numPhases + p` (`p < w`)
reading `1`, jump to composition phase `P1.numPhases + w + 1` (`B > 0`). -/
theorem bZeroFullScan_seqP2_stepConfig_divert_phase (P1 : ConstStatePhasedProgram Unit) (w : Nat)
    {L : Nat} (c : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    {i : Fin (seq P1 (bZeroFullScan w)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).state).fst.val
      = P1.numPhases + w + 1 := by
  have hsub : i.val - P1.numPhases = p := by omega
  rw [seq_stepConfig_P2_phase P1 (bZeroFullScan w) c
      (h2 := by omega) (hlt := by rw [hsub]; show p < w + 2; omega) hstate]
  simp [bZeroFullScan, hsub, hbit, hp, Nat.add_assoc]

/-- **Divert step (read `1`) as a non-first phase.**  The head stays put (on the set bit). -/
theorem bZeroFullScan_seqP2_stepConfig_divert_head (P1 : ConstStatePhasedProgram Unit) (w : Nat)
    {L : Nat} (c : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    {i : Fin (seq P1 (bZeroFullScan w)).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = P1.numPhases + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = p := by omega
  rw [seq_stepConfig_P2_head P1 (bZeroFullScan w) c
      (h2 := by omega) (hlt := by rw [hsub]; show p < w + 2; omega) hstate]
  have hmove : ((bZeroFullScan w).transition ⟨i.val - P1.numPhases, by rw [hsub]; show p < w + 2; omega⟩
      s (c.tape c.head)).2.2.2 = Move.stay := by
    simp [bZeroFullScan, hsub, hbit, hp, Nat.add_assoc]
  rw [hmove]
  simp [Configuration.moveHead]

/-- **Tape unchanged.**  Every P2 step writes the scanned bit back, so the tape is unchanged. -/
theorem bZeroFullScan_seqP2_stepConfig_tape (P1 : ConstStatePhasedProgram Unit) (w : Nat)
    {L : Nat} (c : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    {i : Fin (seq P1 (bZeroFullScan w)).numPhases} {s : Unit}
    (h2 : P1.numPhases ≤ i.val) (hlt : i.val - P1.numPhases < w + 2) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c).tape
      = c.write c.head
          ((bZeroFullScan w).transition ⟨i.val - P1.numPhases, hlt⟩ s (c.tape c.head)).2.2.1 := by
    rw [seq_stepConfig_P2_tape P1 (bZeroFullScan w) c (h2 := h2) (hlt := hlt) hstate]
  rw [hwrite, bZeroFullScan_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Run-through in the P2 region -/

/-- **Scanning invariant as a non-first phase.**  From `c0` at composition phase `P1.numPhases`, if the
`j` cells from the head are all `0` (`j ≤ w`, in bounds), then after `j` steps the composition phase is
`P1.numPhases + j`, the head has advanced to `c0.head + j`, and the tape is unchanged. -/
theorem bZeroFullScan_seqP2_runConfig_scanning (P1 : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c0 : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ j : Nat, j ≤ w →
      (c0.head : Nat) + j < (seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L →
      (∀ p : Fin ((seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 j).state).fst : Nat)
          = P1.numPhases + j
      ∧ ((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨by simpa using hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 j with hc
      have hbnd : (c.head : Nat) + 1 < (seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hpj : j < w := by omega
      have hiph : (c.state.fst : Nat) = P1.numPhases + j := hph
      refine ⟨?_, ?_, ?_⟩
      · rw [bZeroFullScan_seqP2_stepConfig_scan_phase P1 w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit]
        omega
      · rw [bZeroFullScan_seqP2_stepConfig_scan_head P1 w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit hbnd]
        omega
      · rw [bZeroFullScan_seqP2_stepConfig_tape P1 w c
          (i := c.state.fst) (s := c.state.snd) (by omega) (by rw [hiph]; omega) rfl, htp]

/-- **`B = 0` run-through as a non-first phase.**  All `w` cells `0` ⇒ after `w` steps the composition
phase rests at `P1.numPhases + w` (the `B = 0` accept), head at `c0.head + w`, tape unchanged. -/
theorem bZeroFullScan_seqP2_runConfig_zero (P1 : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c0 : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases)
    (hb : (c0.head : Nat) + w < (seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + w → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 w).state).fst : Nat)
        = P1.numPhases + w
      ∧ ((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 w).head : Nat)
          = (c0.head : Nat) + w
      ∧ (TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 w).tape = c0.tape :=
  bZeroFullScan_seqP2_runConfig_scanning P1 w c0 hphase w (le_refl w) hb hzeros

/-- **`B > 0` run-through as a non-first phase.**  Low `j` cells `0`, cell `j` set (`j < w`) ⇒ after
`j + 1` steps the composition phase is `P1.numPhases + w + 1` (`B > 0`), the head rests on the set bit
(`c0.head + j`), tape unchanged. -/
theorem bZeroFullScan_seqP2_runConfig_pos (P1 : ConstStatePhasedProgram Unit) (w : Nat) {L : Nat}
    (c0 : Configuration (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (j : Nat) (hjw : j < w)
    (hb : (c0.head : Nat) + j < (seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false)
    (hone : ∀ p : Fin ((seq P1 (bZeroFullScan w)).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + j → c0.tape p = true) :
    (((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 (j + 1)).state).fst : Nat)
        = P1.numPhases + w + 1
      ∧ ((TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 (j + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 (j + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    bZeroFullScan_seqP2_runConfig_scanning P1 w c0 hphase j (le_of_lt hjw) hb hzeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 (bZeroFullScan w)).toPhased.toTM) c0 j with hc
  have hbit : c.tape c.head = true := by rw [htp]; exact hone c.head (by rw [hhd])
  have hiph : (c.state.fst : Nat) = P1.numPhases + j := hph
  refine ⟨?_, ?_, ?_⟩
  · rw [bZeroFullScan_seqP2_stepConfig_divert_phase P1 w c
      (i := c.state.fst) (s := c.state.snd) hjw hiph rfl hbit]
  · rw [bZeroFullScan_seqP2_stepConfig_divert_head P1 w c
      (i := c.state.fst) (s := c.state.snd) hjw hiph rfl hbit]
    exact hhd
  · rw [bZeroFullScan_seqP2_stepConfig_tape P1 w c
      (i := c.state.fst) (s := c.state.snd) (by omega) (by rw [hiph]; omega) rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
