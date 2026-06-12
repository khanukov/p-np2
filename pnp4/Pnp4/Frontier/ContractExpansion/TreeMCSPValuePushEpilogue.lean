import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushPrehop
import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushRelocate

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, run V): the branch transitions and the epilogue

The two single-branch transitions that bracket the relocate loop, and the epilogue:

* `valuePush_drain_to_reloc`: at the drained layout (`i = k`) the HOME branch reads the now-empty
  source (a `0`) and routes into the relocate loop — `ValuePushLayout … k → RelocateLayout … 0`;
* `valuePush_reloc_to_epilogue`: at the restored layout (`j = k`) the relocate branch reads the
  shadow terminator (a `0`) and routes to the epilogue — `RelocateLayout … k` + the preserved value
  entry/corridor facts `→ EpilogueLayout`;
* `valuePush_epilogue`: from `EpilogueLayout` (phase `68`), scan back to the value entry, append the
  entry's second framing `1` at `vend + 3 + k`, and park on the home anchor at the sink (phase `80`).

After the epilogue the entry block `[vend + 2, vend + 4 + k)` carries `k + 2` ones — exactly the
ones of `encodeNatEntryR k = 0·1^(k+2)` written at `vend + 1`.

**Progress classification (AGENTS.md): Infrastructure** — machine-component run lemmas; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The epilogue entry contract** (phase `68`, head on the shadow terminator).  The shadow source
is restored (`[shwBase, shwBase + k + 1)` all `1`), the three cells right of it are `0`, the value
entry carries `k + 1` ones at `[vend + 2, vend + 3 + k)`, and the corridor between the entry and the
shadow anchor is `0`. -/
structure EpilogueLayout {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 68
  hhead : (c.head : Nat) = shwBase + k + 3
  hvpos : 1 ≤ vend
  hD : vend + k + 4 ≤ shwBase
  hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    vend + 2 ≤ (p : Nat) → (p : Nat) < vend + 3 + k → c.tape p = true
  hcorrR : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    vend + 3 + k ≤ (p : Nat) → (p : Nat) < shwBase → c.tape p = false
  hsrcAll : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase ≤ (p : Nat) → (p : Nat) < shwBase + k + 1 → c.tape p = true
  hwork3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + k + 1 ≤ (p : Nat) → (p : Nat) < shwBase + k + 4 → c.tape p = false

/-! ### Transition A: the drained layout routes into relocate -/

/-- At `i = k` the HOME branch reads the emptied source and routes to the relocate loop. -/
theorem valuePush_drain_to_reloc {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) (hlay : ValuePushLayout c vend shwBase k k) :
    ∃ T : Nat, T ≤ 3
      ∧ RelocateLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T) shwBase k 0
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hik, hvpos, hD, hL, hvend, hframe, hentry, hcorr, hanchor, hsrc,
    hgap, hrebuilt, hterm⟩ := hlay
  obtain ⟨p1, h1, t1⟩ := valuePush_region_homeBranch.run_stepRightBranch_hop_zero c hphase
    (by omega) (by rfl) (by rfl) (by rfl)
    (fun p hp => by
      -- the source is empty at i = k, so the cell right of home is the working gap (a 0)
      rw [hhead] at hp
      exact hgap p (by omega) (by omega))
  rw [hhead] at h1
  refine ⟨3, le_refl _, ?_, fun p => by rw [t1]⟩
  refine ⟨p1, by rw [h1], by omega, by omega, hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [t1]; exact hanchor p hp
  · intro p hp1 hp2; omega
  · intro p hp1 hp2; rw [t1]; exact hgap p (by omega) (by omega)
  · intro p hp1 hp2; rw [t1]; exact hrebuilt p (by omega) (by omega)
  · intro p hp; rw [t1]; exact hterm p hp

/-! ### Transition B: the restored layout routes into the epilogue -/

set_option maxHeartbeats 800000 in
/-- At `j = k` the relocate branch reads the shadow terminator and routes to the epilogue.  The
value entry and corridor (untouched by relocate) are supplied explicitly. -/
theorem valuePush_reloc_to_epilogue {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) (hlay : RelocateLayout c shwBase k k)
    (hvpos : 1 ≤ vend) (hD : vend + k + 4 ≤ shwBase)
    (hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      vend + 2 ≤ (p : Nat) → (p : Nat) < vend + 3 + k → c.tape p = true)
    (hcorrR : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      vend + 3 + k ≤ (p : Nat) → (p : Nat) < shwBase → c.tape p = false) :
    ∃ T : Nat, T ≤ 5
      ∧ EpilogueLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T) vend shwBase k
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hjk, hbase, hL, hanchor, hnew, hwork, hrem, hterm⟩ := hlay
  -- L1: step right.
  obtain ⟨p1, h1, t1⟩ := valuePush_region_relocStepRight.run_stepRight_hop c hphase (by omega)
  rw [hhead] at h1
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 with hc1
  have h1' : (c1.head : Nat) = shwBase + 2 + k := by rw [h1]; omega
  -- L2: branch reads the shadow terminator (a 0) and routes to 68.
  obtain ⟨p2, h2, t2⟩ := valuePush_region_relocBranch.run_stepRightBranch_hop_zero c1 p1 (by omega)
    (by rfl) (by rfl) (by rfl)
    (fun p hp => by rw [t1]; exact hterm p (by omega))
  rw [h1'] at h2
  set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 3 with hc2
  have h2' : (c2.head : Nat) = shwBase + k + 3 := by rw [h2]; omega
  have htc2 : c2.tape = c.tape := by rw [t2, t1]
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 + 3) = c2 := by
    rw [TM.runConfig_add, ← hc1, ← hc2]
  refine ⟨2 + 3, by omega, ?_, fun p => by rw [hrun, htc2]⟩
  rw [hrun]
  refine ⟨p2, h2', hvpos, hD, hL, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp2; rw [htc2]; exact hentry p hp1 hp2
  · intro p hp1 hp2; rw [htc2]; exact hcorrR p hp1 hp2
  · intro p hp1 hp2
    rw [htc2]
    by_cases hp : (p : Nat) = shwBase
    · exact hanchor p hp
    · exact hnew p (by omega) (by omega)
  · intro p hp1 hp2
    rw [htc2]
    by_cases hp : (p : Nat) = shwBase + k + 3
    · exact hterm p hp
    · exact hwork p (by omega) (by omega)

/-! ### The epilogue -/

set_option maxHeartbeats 1200000 in
/-- **The epilogue.**  From `EpilogueLayout`, in `T ≤ 2·shwBase + 12` steps reach the sink
(phase `80`), head on the home anchor, with the entry's second framing `1` written at
`vend + 3 + k` (so the entry block `[vend + 2, vend + 4 + k)` now carries `k + 2` ones). -/
theorem valuePush_epilogue {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) (hlay : EpilogueLayout c0 vend shwBase k) :
    ∃ T : Nat, T ≤ 2 * shwBase + 12
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).state).fst : Nat) = 80
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).head : Nat) = shwBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (vend + 3 + k) [true] := by
  obtain ⟨hphase, hhead, hvpos, hD, hL, hentry, hcorrR, hsrcAll, hwork3⟩ := hlay
  -- L1: scan left over the work cells onto the shadow source's rightmost 1.
  obtain ⟨p1, h1, t1⟩ := valuePush_region_epiScanLeft1.run_scanLeft_hop c0 hphase (shwBase + k)
    (by omega)
    (fun p hp1 hp2 => by rw [hhead] at hp2; exact hwork3 p (by omega) (by omega))
    (fun p hp => hsrcAll p (by omega) (by omega))
  rw [hhead] at p1 h1 t1
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 ((shwBase + k + 3 - (shwBase + k)) + 2)
    with hc1
  have h1' : (c1.head : Nat) = shwBase + k := by rw [h1]
  -- L2: scan left over the shadow source onto the left corridor cell.
  obtain ⟨p2, h2, t2⟩ := valuePush_region_epiScanOnes.run_scanLeftOnes_hop c1 p1 (shwBase - 1)
    (by omega)
    (fun p hp1 hp2 => by rw [t1]; exact hsrcAll p (by omega) (by omega))
    (fun p hp => by rw [t1]; exact hcorrR p (by omega) (by omega))
  rw [h1'] at p2 h2 t2
  set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 ((shwBase + k - (shwBase - 1)) + 2)
    with hc2
  have h2' : (c2.head : Nat) = shwBase - 1 := by rw [h2]
  have htc2 : c2.tape = c0.tape := by rw [t2, t1]
  -- L3: scan left over the corridor onto the value entry's rightmost 1.
  obtain ⟨p3, h3, t3⟩ := valuePush_region_epiScanLeft2.run_scanLeft_hop c2 p2 (vend + 2 + k)
    (by omega)
    (fun p hp1 hp2 => by rw [htc2]; exact hcorrR p (by omega) (by omega))
    (fun p hp => by rw [htc2]; exact hentry p (by omega) (by omega))
  rw [h2'] at p3 h3 t3
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 ((shwBase - 1 - (vend + 2 + k)) + 2)
    with hc3
  have h3' : (c3.head : Nat) = vend + 2 + k := by rw [h3]
  have htc3 : c3.tape = c0.tape := by rw [t3, htc2]
  -- L4: step right onto the entry's next free cell.
  obtain ⟨p4, h4, t4⟩ := valuePush_region_epiStepRight.run_stepRight_hop c3 p3 (by omega)
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 2 with hc4
  have h4' : (c4.head : Nat) = vend + 3 + k := by rw [h4, h3']; omega
  have htc4 : c4.tape = c0.tape := by rw [t4, htc3]
  -- L5: write the entry's second framing 1.
  obtain ⟨p5, h5, t5⟩ := valuePush_region_epiWrite.run_writeBits_hop c4 p4
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p5 h5 t5
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 2 with hc5
  have h5' : (c5.head : Nat) = vend + 4 + k := by rw [h5, h4']; omega
  have htc5 : c5.tape = writeBlockTape c0.tape (vend + 3 + k) [true] := by rw [t5, htc4, h4']
  -- L6: scan right over the corridor back onto the home anchor (the sink).
  obtain ⟨p6, h6, t6⟩ := valuePush_region_epiScanRight.run_scanRight_hop c5 p5 (shwBase - (vend + 4 + k))
    (by omega)
    (fun p hp1 hp2 => by
      rw [htc5, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hcorrR p (by omega) (by omega))
    (fun p hp => by
      rw [htc5, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hsrcAll p (by omega) (by omega))
  rw [h5'] at h6
  set c6 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c5 ((shwBase - (vend + 4 + k)) + 2)
    with hc6
  have h6' : (c6.head : Nat) = shwBase := by rw [h6]; omega
  have htc6 : c6.tape = writeBlockTape c0.tape (vend + 3 + k) [true] := by rw [t6, htc5]
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c0
      (((shwBase + k + 3 - (shwBase + k)) + 2) + (((shwBase + k - (shwBase - 1)) + 2)
        + (((shwBase - 1 - (vend + 2 + k)) + 2) + (2 + (2 + ((shwBase - (vend + 4 + k)) + 2))))))
      = c6 := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  refine ⟨((shwBase + k + 3 - (shwBase + k)) + 2) + (((shwBase + k - (shwBase - 1)) + 2)
      + (((shwBase - 1 - (vend + 2 + k)) + 2) + (2 + (2 + ((shwBase - (vend + 4 + k)) + 2))))),
    by omega, ?_, ?_, ?_⟩
  · rw [hrun]; exact p6
  · rw [hrun]; exact h6'
  · rw [hrun]; exact htc6

end ContractExpansion
end Frontier
end Pnp4
