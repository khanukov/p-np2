import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanHbase

/-!
# `binToUnaryLoopFullScan` — the `B > 0` scan-to-divert run (NP-verifier track — D2t-3 `ε`, `hstep` core)

The `B > 0` half of the loop's first leg on the loop machine: from the loop start (phase `0`, head
`HOME`), the leading `stepRightOnce` (phase `0 → 2`, head `HOME → HOME+1`) then the width-`w` full scan
over `B`'s low `0`-run diverts on the lowest set bit (`HOME+1+j`, `j < w`) to the route-body's accept
(composition phase `w + 3`), head resting on that set bit.  From there `hstep`'s remaining legs (re-home,
body one-pass, back-edge) continue — those are the next bricks.

**Progress classification (AGENTS.md): Infrastructure** — standard triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Loop divert step (read `1`), phase.**  At composition phase `2 + p` (`p < w`) reading `1`, jump to
phase `w + 3` (the route-body's `B > 0` accept, lifted past the leading `stepRightOnce`). -/
theorem binToUnaryLoopFullScan_stepConfig_divert_phase (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 3 := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
      binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
  simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne, hlt2,
    hge]
  omega

/-- **Loop divert step (read `1`), head.**  The head stays put (on the set bit). -/
theorem binToUnaryLoopFullScan_stepConfig_divert_head (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
  have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
    rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne,
      hlt2, hge]
  rw [hmove]
  simp [Configuration.moveHead]

/-- **Loop divert step (read `1`), tape.**  The tape is unchanged. -/
theorem binToUnaryLoopFullScan_stepConfig_divert_tape (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  have hwrite : (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne,
      hlt2, hge]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- **`B > 0` scan-to-divert run.**  From the loop start (phase `0`, head `HOME`) with `B`'s low `j`
cells `0` and the cell at `HOME+1+j` set (`j < w`), the loop reaches phase `w + 3` after `j + 3` steps,
with the head on the set bit (`HOME+1+j`) and the tape unchanged. -/
theorem binToUnaryLoopFullScan_runConfig_pos (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0) (j : Nat) (hjw : j < w)
    (hb : (c0.head : Nat) + 1 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + 1 + j → c0.tape q = false)
    (hone : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = (c0.head : Nat) + 1 + j → c0.tape q = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3)).state).fst : Nat) = w + 3
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3)).head : Nat)
          = (c0.head : Nat) + 1 + j := by
  -- step 0 + step 1: the leading stepRightOnce (phase 0 → 2, head HOME → HOME+1)
  obtain ⟨h0p, h0h, h0t⟩ := binToUnaryLoopFullScan_step0 w c0 hstart rfl (by omega)
  set c1 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 1 with hc1
  have hc1eq : c1 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 := by
    rw [hc1, show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ]; rfl
  obtain ⟨h1p, h1h, h1t⟩ := binToUnaryLoopFullScan_step1 w c1
    (i := c1.state.fst) (s := c1.state.snd) (by rw [hc1eq]; exact h0p) rfl
  set c2 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2 with hc2
  have hc2eq : c2 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c1 := by
    rw [hc2, show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_succ, hc1]
  have h2p : (c2.state.fst : Nat) = 2 := by rw [hc2eq]; exact h1p
  have h2h : (c2.head : Nat) = (c0.head : Nat) + 1 := by rw [hc2eq, h1h, hc1eq, h0h]
  have h2t : c2.tape = c0.tape := by rw [hc2eq, h1t, hc1eq, h0t]
  -- scan j zeros from phase 2 → phase 2 + j, head HOME+1+j
  have hzeros2 : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c2.head : Nat) ≤ (q : Nat) → (q : Nat) < (c2.head : Nat) + j → c2.tape q = false := by
    intro q hq1 hq2; rw [h2t]; rw [h2h] at hq1 hq2; exact hzeros q hq1 (by omega)
  obtain ⟨hsp, hsh, hst⟩ := binToUnaryLoopFullScan_runConfig_scanning w c2 h2p j (le_of_lt hjw)
    (by rw [h2h]; omega) hzeros2
  set c2j := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2 j with hc2j
  -- divert on the lowest set bit (cell HOME+1+j) → phase w+3, head stays
  have hbit : c2j.tape c2j.head = true := by
    rw [hst, h2t]; exact hone c2j.head (by rw [hsh, h2h])
  have hc2jp : (c2j.state.fst : Nat) = 2 + j := hsp
  have hc2j_eq : c2j = TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + j) := by
    rw [hc2j, hc2, ← TM.runConfig_add]
  have hcompose : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3)
      = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2j := by
    rw [show (j + 3 : Nat) = (2 + j) + 1 from by omega, TM.runConfig_succ, ← hc2j_eq]
  rw [hcompose]
  refine ⟨?_, ?_⟩
  · rw [binToUnaryLoopFullScan_stepConfig_divert_phase w c2j (i := c2j.state.fst) (s := c2j.state.snd)
      hjw hc2jp rfl hbit]
  · rw [binToUnaryLoopFullScan_stepConfig_divert_head w c2j (i := c2j.state.fst) (s := c2j.state.snd)
      hjw hc2jp rfl hbit, hsh, h2h]

end ContractExpansion
end Frontier
end Pnp4
