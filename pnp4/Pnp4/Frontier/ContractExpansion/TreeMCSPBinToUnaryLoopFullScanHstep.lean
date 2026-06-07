import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanMeasure
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanSeek
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanStep2

/-!
# `binToUnaryLoopFullScan` `hstep` core — one `B > 0` body pass (NP-verifier track — D2t-3 `ε`)

The `B > 0` re-entry pass on the sound loop, composed end-to-end. From a HOME config at the loop start
(phase `0`) with the U-LEFT layout and `B`'s lowest set bit at offset `j`, one pass chains the four proven
legs — `pos` (scan-to-divert, phase `0 → w+3`), `postDivert` (the connector, `w+3 → w+6`),
`seekHomeAfterRoute` (re-home, `w+6 → w+15`), and the `binToUnaryBody` one-pass engine (`w+15 → w+29`,
decrement `B` / append `1` to `U`) — into a single run reaching the loop body's accept phase `w+29` with
the head back at HOME and the width-`w` counter value `counterValue B` strictly decreased by one.

`binToUnaryLoopFullScan_runConfig_pos_tape` strengthens `pos` with the tape preservation the chain needs
(every leg before the body engine leaves the tape unchanged), so the body engine's preconditions reduce to
the original layout. The headline `binToUnaryLoopFullScan_runConfig_bodyPass` is the per-iteration work
`loopUntilSink_reachesSink`'s `hstep` consumes (with `μ := counterValue B`); the back-edge re-entry and the
`reachesSink` assembly are the follow-up.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- `pos` with tape preservation: the B>0 scan-to-divert run leaves the tape unchanged. -/
theorem binToUnaryLoopFullScan_runConfig_pos_tape (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0) (j : Nat) (hjw : j < w)
    (hb : (c0.head : Nat) + 1 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + 1 + j → c0.tape q = false)
    (hone : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = (c0.head : Nat) + 1 + j → c0.tape q = true) :
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3)).tape = c0.tape := by
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
  have hzeros2 : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c2.head : Nat) ≤ (q : Nat) → (q : Nat) < (c2.head : Nat) + j → c2.tape q = false := by
    intro q hq1 hq2; rw [h2t]; rw [h2h] at hq1 hq2; exact hzeros q hq1 (by omega)
  obtain ⟨hsp, hsh, hst⟩ := binToUnaryLoopFullScan_runConfig_scanning w c2 h2p j (le_of_lt hjw)
    (by rw [h2h]; omega) hzeros2
  set c2j := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2 j with hc2j
  have hbit : c2j.tape c2j.head = true := by
    rw [hst, h2t]; exact hone c2j.head (by rw [hsh, h2h])
  have hc2jp : (c2j.state.fst : Nat) = 2 + j := hsp
  have hc2j_eq : c2j = TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + j) := by
    rw [hc2j, hc2, ← TM.runConfig_add]
  have hcompose : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3)
      = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2j := by
    rw [show (j + 3 : Nat) = (2 + j) + 1 from by omega, TM.runConfig_succ, ← hc2j_eq]
  rw [hcompose, binToUnaryLoopFullScan_stepConfig_divert_tape w c2j (i := c2j.state.fst) (s := c2j.state.snd)
    hjw hc2jp rfl hbit, hst, h2t]

set_option maxHeartbeats 1000000 in
theorem binToUnaryLoopFullScan_runConfig_bodyPass (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0) (j : Nat) (hjw : j < w)
    (hb : (c0.head : Nat) + 3 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + 1 + j → c0.tape q = false)
    (hone : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = (c0.head : Nat) + 1 + j → c0.tape q = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) → c0.tape q = true)
    (hUboundary : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = (c0.head : Nat) - u - 1 → c0.tape q = false)
    (hseed : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = (c0.head : Nat) - 1 → c0.tape q = true) :
    ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0
        ((j + 3) + 3 + (j + 10) + onePassSteps j u)).state.fst : Nat) = w + 29
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0
        ((j + 3) + 3 + (j + 10) + onePassSteps j u)).head : Nat) = (c0.head : Nat)
      ∧ counterValue (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0
            ((j + 3) + 3 + (j + 10) + onePassSteps j u)) ((c0.head : Nat) + 1) w + 1
          = counterValue c0 ((c0.head : Nat) + 1) w := by
  obtain ⟨hPp, hPh⟩ := binToUnaryLoopFullScan_runConfig_pos w c0 hstart j hjw (by omega) hzeros hone
  have hPt := binToUnaryLoopFullScan_runConfig_pos_tape w c0 hstart j hjw (by omega) hzeros hone
  set cP := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (j + 3) with hcPdef
  obtain ⟨hQp, hQh, hQt⟩ := binToUnaryLoopFullScan_runConfig_postDivert w cP hPp (by rw [hPh]; omega)
  set cQ := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cP 3 with hcQdef
  have hQt' : cQ.tape = c0.tape := hQt.trans hPt
  have hQh' : (cQ.head : Nat) = (c0.head : Nat) + 2 + j := by omega
  obtain ⟨hRp, hRh, hRt⟩ := binToUnaryLoopFullScan_seek_home w cQ (c0.head : Nat) j hQp hHOME hQh'
    (by omega)
    (by intro q hq1 hq2; rw [hQt']
        rcases Nat.lt_or_ge (q : Nat) ((c0.head : Nat) + 1) with hlt | hge
        · have heq : (q : Nat) = (c0.head : Nat) := by omega
          rw [show q = c0.head from Fin.ext heq]; exact h_sentinel
        · exact hzeros q hge (by omega))
    (by intro q hq; rw [hQt']; exact hseed q hq)
  set cR := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cQ (j + 10) with hcRdef
  have hRt' : cR.tape = c0.tape := hRt.trans hQt'
  have hRh' : (cR.head : Nat) = (c0.head : Nat) := hRh
  have hcF : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0
        ((j + 3) + 3 + (j + 10) + onePassSteps j u)
      = TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cR (onePassSteps j u) := by
    rw [hcRdef, hcQdef, hcPdef, ← TM.runConfig_add, ← TM.runConfig_add, ← TM.runConfig_add]
    congr 1; omega
  have hRsent : cR.tape cR.head = false := by
    rw [hRt']; rw [show cR.head = c0.head from Fin.ext hRh']; exact h_sentinel
  have hZ : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (cR.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (cR.head : Nat) + 1 + j → cR.tape p = false := by
    intro p hp1 hp2; rw [hRt']; exact hzeros p (by rw [hRh'] at hp1; omega) (by rw [hRh'] at hp2; omega)
  have hO : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (cR.head : Nat) + 1 + j → cR.tape p = true := by
    intro p hp; rw [hRt']; exact hone p (by rw [hRh'] at hp; omega)
  have hUU : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (cR.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (cR.head : Nat) → cR.tape p = true := by
    intro p hp1 hp2; rw [hRt']; exact hU p (by rw [hRh'] at hp1; omega) (by rw [hRh'] at hp2; omega)
  have hUb : ∀ p : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (cR.head : Nat) - u - 1 → cR.tape p = false := by
    intro p hp; rw [hRt']; exact hUboundary p (by rw [hRh'] at hp; omega)
  obtain ⟨hFp, hFh, _⟩ := binToUnaryLoopFullScan_body_runConfig_onePass w cR hRp j
    (by rw [hRh']; omega) hZ hO hRsent (by rw [hRh']; exact hHOME) u (by rw [hRh']; exact hUfit) hUU hUb
  have hMeasure := binToUnaryLoopFullScan_body_onePass_counterValue w cR hRp j
    (by rw [hRh']; omega) hZ hO hRsent (by rw [hRh']; exact hHOME) u (by rw [hRh']; exact hUfit) hUU hUb
    hjw (by rw [hRh']; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hcF]; exact hFp
  · rw [hcF, hFh, hRh']
  · rw [hcF]
    rw [show ((cR.head : Nat) + 1) = ((c0.head : Nat) + 1) from by rw [hRh']] at hMeasure
    rw [hMeasure]
    exact counterValue_eq_of_tape_eq cR c0 ((c0.head : Nat) + 1) w (fun p _ _ => by rw [hRt'])

end ContractExpansion
end Frontier
end Pnp4
