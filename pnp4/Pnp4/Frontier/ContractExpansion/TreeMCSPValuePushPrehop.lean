import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushPass

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, run III): the pre-hop

The pre-hop (phases `0–11`) turns the **start** configuration into the drain's loop layout at
`i = 0`: from the home anchor it walks left to the value stack's last `1`, skips the entry's
leading `0`, writes the entry's first framing `1` at `vend + 2`, and scans back to the home anchor.
The single cell `vend + 2` is the only change.

`ValuePushStart` is the entry contract (home anchor at `shwBase`, the shadow source `1^k` to its
right, the value stack ending in a `1` at `vend` with an all-`0` corridor between).  The headline
will feed this from `driverCorridorInv` + the `SHW` zone clause.

**Progress classification (AGENTS.md): Infrastructure** — a machine-component run lemma; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The value-push start contract** (phase `0`, head on the home anchor).  The shadow count
`SHW = [1]·1^k` sits at `[shwBase, shwBase + k + 1)`; the value stack ends in a `1` at `vend`; the
corridor `[vend + 1, shwBase)` and the two cells right of the source are all `0`. -/
structure ValuePushStart {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 0
  hhead : (c.head : Nat) = shwBase
  hvpos : 1 ≤ vend
  hD : vend + k + 4 ≤ shwBase
  hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hvend : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = vend → c.tape p = true
  hcorr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    vend + 1 ≤ (p : Nat) → (p : Nat) < shwBase → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase → c.tape p = true
  hsrc : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + 1 + k → c.tape p = true
  hgap : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 + k ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 → c.tape p = false
  hterm : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase + k + 3 → c.tape p = false

set_option maxHeartbeats 1200000 in
/-- **The pre-hop.**  From the start contract, in `T ≤ 2·shwBase + 10` steps reach the loop layout
at `i = 0`; only `vend + 2` (the entry's first framing `1`) changes. -/
theorem valuePush_prehop {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) (hstart : ValuePushStart c0 vend shwBase k) :
    ∃ T : Nat, T ≤ 2 * shwBase + 10
      ∧ ValuePushLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T)
          vend shwBase k 0
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (p : Nat) ≠ vend + 2 →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape p = c0.tape p := by
  obtain ⟨hphase, hhead, hvpos, hD, hL, hvend, hcorr, hanchor, hsrc, hgap, hterm⟩ := hstart
  -- L0: step left off the home anchor.
  obtain ⟨p1, h1, t1⟩ := valuePush_region_preStepLeft.run_stepLeft_hop c0 hphase (by omega)
  rw [hhead] at h1
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 2 with hc1
  have h1' : (c1.head : Nat) = shwBase - 1 := by rw [h1]
  -- L1: scan left over the corridor onto the value stack's last 1.
  obtain ⟨p2, h2, t2⟩ := valuePush_region_preScanLeft.run_scanLeft_hop c1 p1 vend (by omega)
    (fun p hp1 hp2 => by rw [t1]; exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [t1]; exact hvend p hp)
  rw [h1'] at h2 t2 p2
  set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 ((shwBase - 1 - vend) + 2) with hc2
  have h2' : (c2.head : Nat) = vend := by rw [h2]
  -- L2: step right (skip onto the entry's leading 0).
  obtain ⟨p3, h3, t3⟩ := valuePush_region_preStepRight1.run_stepRight_hop c2 p2 (by omega)
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 2 with hc3
  have h3' : (c3.head : Nat) = vend + 1 := by rw [h3, h2']
  -- L3: step right onto the entry's first cell.
  obtain ⟨p4, h4, t4⟩ := valuePush_region_preStepRight2.run_stepRight_hop c3 p3 (by omega)
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 2 with hc4
  have h4' : (c4.head : Nat) = vend + 2 := by rw [h4, h3']
  have htc4 : c4.tape = c0.tape := by rw [t4, t3, t2, t1]
  -- L4: write the entry's first framing 1.
  obtain ⟨p5, h5, t5⟩ := valuePush_region_preWrite.run_writeBits_hop c4 p4
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p5 h5 t5
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 2 with hc5
  have h5' : (c5.head : Nat) = vend + 3 := by rw [h5, h4']
  have htc5 : c5.tape = writeBlockTape c0.tape (vend + 2) [true] := by rw [t5, htc4, h4']
  -- L5: scan right over the corridor back onto the home anchor.
  obtain ⟨p6, h6, t6⟩ := valuePush_region_preScanRight.run_scanRight_hop c5 p5 (shwBase - (vend + 3))
    (by omega)
    (fun p hp1 hp2 => by
      rw [htc5, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [htc5, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hanchor p (by omega))
  rw [h5'] at h6
  set c6 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c5 ((shwBase - (vend + 3)) + 2)
    with hc6
  have h6' : (c6.head : Nat) = shwBase := by rw [h6]; omega
  have htc6 : c6.tape = writeBlockTape c0.tape (vend + 2) [true] := by rw [t6, htc5]
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c0
      (2 + (((shwBase - 1 - vend) + 2) + (2 + (2 + (2 + ((shwBase - (vend + 3)) + 2)))))) = c6 := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  have hcell : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) ≠ vend + 2 → c6.tape p = c0.tape p := fun p hp => by
    rw [htc6, writeBlockTape_singleton_ne _ _ _ _ hp]
  have hval : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = vend + 2 → c6.tape p = true := fun p hp => by
    rw [htc6, writeBlockTape_singleton_eq _ _ _ _ hp]
  refine ⟨2 + (((shwBase - 1 - vend) + 2) + (2 + (2 + (2 + ((shwBase - (vend + 3)) + 2))))),
    by omega, ?_, ?_⟩
  · rw [hrun]
    refine ⟨p6, h6', by omega, hvpos, hD, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [hcell p (by omega)]; exact hvend p hp
    · intro p hp; rw [hcell p (by omega)]; exact hcorr p (by omega) (by omega)
    · intro p hp1 hp2; exact hval p (by omega)
    · intro p hp1 hp2; rw [hcell p (by omega)]; exact hcorr p (by omega) hp2
    · intro p hp; rw [hcell p (by omega)]; exact hanchor p hp
    · intro p hp1 hp2; rw [hcell p (by omega)]; exact hsrc p hp1 (by omega)
    · intro p hp1 hp2; rw [hcell p (by omega)]; exact hgap p (by omega) (by omega)
    · intro p hp1 hp2; omega
    · intro p hp; rw [hcell p (by omega)]; exact hterm p hp
  · rw [hrun]; exact hcell

end ContractExpansion
end Frontier
end Pnp4
