import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkRightFull
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorRoutes
import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram

/-!
# Corridor return routes — D2t-5b (Block A4r): the rightward cross-zone route back to the marker

The mirror of `TreeMCSPCorridorRoutes`: after an emit at the WORK frontier the head returns
`FM → value zone → control zone → M` rightward.  Each leg is a proven machine under
`driverCorridorInv`:

* a rightward **0-corridor scan** (`gammaSelfLoopScan`) landing on the next zone's **base sentinel**
  (or the cursor marker `M`) — this module first supplies the arbitrary-configuration
  scanning/terminator run lemmas the original module states only from `initialConfig`;
* a rightward **zone traversal** (`zoneWalkRight_runConfig_walkZone`, A4w) exiting on the second dead
  cell past the zone's content — where the next scan starts.

Legs: `corridor_back_scan_to_valSentinel` (from the cell right of `FM`),
`corridor_back_walk_val`, `corridor_back_scan_to_shwBase` (landing on the shadow-count zone's
base `1`), `corridor_back_scan_to_ctrlSentinel` (from the dead cell right of the `SHW` content;
crossing the `SHW` `1`-block rightward is a scan-over-ones connector, supplied with the pop arm),
`corridor_back_walk_ctrl`, `corridor_back_scan_to_M`.

**Progress classification (AGENTS.md): Infrastructure** — verifier machine run-throughs; build no
verifier and prove no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### `gammaSelfLoopScan` from an arbitrary configuration -/

/-- Rightward 0-scan invariant from an arbitrary configuration: `j` zero cells from the head, `j`
steps advance the head `j` cells, still scanning, tape unchanged. -/
theorem gammaSelfLoopScan_runConfigFrom_scanning {L : Nat}
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, (c0.head : Nat) + j < gammaSelfLoopScan.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false) →
      (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < gammaSelfLoopScan.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopScan_stepConfig_scan_zero_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopScan_stepConfig_scan_zero_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        rw [hhd]
        omega
      · rw [gammaSelfLoopScan_stepConfig_scan_zero_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Rightward 0-scan terminator from an arbitrary configuration: with the cells `[head, head + m)`
all `0` and a `1` at `head + m`, after `m + 1` steps the scan is done (phase `1`) **on** the `1`,
tape unchanged. -/
theorem gammaSelfLoopScan_runConfigFrom_terminator {L : Nat}
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (m : Nat)
    (hroom : (c0.head : Nat) + m < gammaSelfLoopScan.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + m → c0.tape p = false)
    (hterm : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + m → c0.tape p = true) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 (m + 1)).state).fst : Nat) = 1
    ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 (m + 1)).head : Nat)
        = (c0.head : Nat) + m
    ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 (m + 1)).tape = c0.tape := by
  rw [TM.runConfig_add]
  obtain ⟨hph, hhd, htp⟩ := gammaSelfLoopScan_runConfigFrom_scanning c0 hphase m hroom hzeros
  set c := TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0 m with hc
  rw [TM.runConfig_one]
  have hbit : c.tape c.head = true := by
    rw [htp]; exact hterm c.head (by rw [hhd])
  refine ⟨?_, ?_, ?_⟩
  · exact gammaSelfLoopScan_stepConfig_scan_one_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [gammaSelfLoopScan_stepConfig_scan_one_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, hhd]
  · rw [gammaSelfLoopScan_stepConfig_scan_one_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### The five return legs -/

/-- **Return leg 1 (scan → the value zone's base sentinel).**  From the dead cell right of `FM`
(`head = FM + 1`), the rightward 0-scan stops on the value sentinel at `valBase`. -/
theorem corridor_back_scan_to_valSentinel {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.workBase + (encodeGateRecordStream st.out).length + 1) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.valBase - (c0.head : Nat)) + 1)).state).fst : Nat) = 1
    ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.valBase - (c0.head : Nat)) + 1)).head : Nat) = z.valBase
    ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.valBase - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hsent : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = z.valBase → c0.tape p = true := by
    intro p hp
    obtain ⟨hf, hc⟩ := hval
    have := hc p (by omega) (by
      have : 1 ≤ (encodeNatStackR st.val).length := by
        cases hv : encodeNatStackR st.val with
        | nil =>
            have := encodeNatStackR_getLast_true st.val
            rw [hv] at this; simp at this
        | cons a l => simp
      omega)
    rw [this]
    have hidx : (p : Nat) - z.valBase = 0 := by omega
    rw [hidx]
    have : encodeNatStackR st.val = true :: st.val.reverse.flatMap encodeNatEntryR := rfl
    rw [this]
    rfl
  exact (by
    have := gammaSelfLoopScan_runConfigFrom_terminator c0 hphase (z.valBase - (c0.head : Nat))
      (by omega)
      (fun p hp1 hp2 => hfzeros p (by omega) (by omega))
      (fun p hp => hsent p (by omega))
    rwa [show (c0.head : Nat) + (z.valBase - (c0.head : Nat)) = z.valBase from by omega] at this)

/-- **Return leg 2 (walk the value zone rightward).**  From the value sentinel, the rightward walker
crosses the zone and exits on the second dead cell past its content. -/
theorem corridor_back_walk_val {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.valBase) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.val.map (· + 2)))).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.val.map (· + 2)))).head : Nat)
        = z.valBase + (encodeNatStackR st.val).length + 1
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.val.map (· + 2)))).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen : (encodeNatStackR st.val).length = (walkZone (st.val.map (· + 2))).length := by
    rw [encodeNatStackR_eq_walkZone]
  obtain ⟨hf1, hf2, hf3, _⟩ := zoneWalkRight_runConfig_walkZone c0 (st.val.map (· + 2))
    (by
      intro k hk
      rw [List.mem_map] at hk
      obtain ⟨v, -, rfl⟩ := hk
      omega)
    z.valBase hphase hhead
    (by rw [← hlen]; omega)
    (by rw [← encodeNatStackR_eq_walkZone]; exact hval)
    (fun p hp => hvzeros p (by rw [← hlen] at hp; omega) (by rw [← hlen] at hp; omega))
    (fun p hp => hvzeros p (by rw [← hlen] at hp; omega) (by rw [← hlen] at hp; omega))
  exact ⟨hf1, by rw [hf2, ← hlen], hf3⟩

/-- **Return leg 3 (scan → the shadow-count zone's base `1`).**  From the dead cell right of the
value content (`valBase + |encodeNatStackR st.val| + 1`), the rightward 0-scan stops on `shwBase`
(the `SHW` window's leftmost cell, always a `1`).  (Crossing the `SHW` `1`-block rightward is a
scan-over-ones connector, supplied with the pop arm.) -/
theorem corridor_back_scan_to_shwBase {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.valBase + (encodeNatStackR st.val).length + 1) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.shwBase - (c0.head : Nat)) + 1)).state).fst : Nat) = 1
    ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.shwBase - (c0.head : Nat)) + 1)).head : Nat) = z.shwBase
    ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.shwBase - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hsent : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = z.shwBase → c0.tape p = true := by
    intro p hp
    obtain ⟨hf, hc⟩ := hshw
    have := hc p (by omega) (by rw [List.length_replicate]; omega)
    rw [this]
    have hidx : (p : Nat) - z.shwBase = 0 := by omega
    rw [hidx]
    rfl
  have hvfit' : z.valBase + (encodeNatStackR st.val).length ≤ z.valEnd := hvfit
  have := gammaSelfLoopScan_runConfigFrom_terminator c0 hphase (z.shwBase - (c0.head : Nat))
    (by omega)
    (fun p hp1 hp2 => hvzeros p (by omega) (by omega))
    (fun p hp => hsent p (by omega))
  rwa [show (c0.head : Nat) + (z.shwBase - (c0.head : Nat)) = z.shwBase from by omega] at this

/-- **Return leg 3′ (scan → the control zone's base sentinel).**  From the dead cell right of the
`SHW` content (`shwBase + |out| + 1`), the rightward 0-scan stops on the control sentinel at
`ctrlBase`. -/
theorem corridor_back_scan_to_ctrlSentinel {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.shwBase + st.out.length + 1) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.ctrlBase - (c0.head : Nat)) + 1)).state).fst : Nat) = 1
    ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.ctrlBase - (c0.head : Nat)) + 1)).head : Nat) = z.ctrlBase
    ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.ctrlBase - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hsent : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = z.ctrlBase → c0.tape p = true := by
    intro p hp
    obtain ⟨hf, hc⟩ := hctrl
    have hlen1 : 1 ≤ (encodeCtrlStackR st.ctrl).length := by
      cases hv : encodeCtrlStackR st.ctrl with
      | nil =>
          have := encodeCtrlStackR_getLast_true st.ctrl
          rw [hv] at this; simp at this
      | cons a l => simp
    have := hc p (by omega) (by omega)
    rw [this]
    have hidx : (p : Nat) - z.ctrlBase = 0 := by omega
    rw [hidx]
    have : encodeCtrlStackR st.ctrl = true :: st.ctrl.reverse.flatMap encodeCtrlFrameR := rfl
    rw [this]
    rfl
  have := gammaSelfLoopScan_runConfigFrom_terminator c0 hphase (z.ctrlBase - (c0.head : Nat))
    (by omega)
    (fun p hp1 hp2 => hszeros p (by omega) (by omega))
    (fun p hp => hsent p (by omega))
  rwa [show (c0.head : Nat) + (z.ctrlBase - (c0.head : Nat)) = z.ctrlBase from by omega] at this

/-- **Return leg 4 (walk the control zone rightward).**  Needs the reachability fact `rem ≥ 1`. -/
theorem corridor_back_walk_ctrl {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hrem : ∀ f ∈ st.ctrl, 1 ≤ f.2)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).head : Nat)
        = z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 1
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0
        (walkZoneStepsR (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen : (encodeCtrlStackR st.ctrl).length
      = (walkZone (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])).length := by
    rw [encodeCtrlStackR_eq_walkZone]
  obtain ⟨hf1, hf2, hf3, _⟩ := zoneWalkRight_runConfig_walkZone c0
    (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
    (by
      intro k hk
      rw [List.mem_flatMap] at hk
      obtain ⟨f, hf, hkf⟩ := hk
      have := hrem f hf
      simp only [List.mem_cons] at hkf
      rcases hkf with rfl | rfl | hfalse
      · omega
      · omega
      · simp at hfalse)
    z.ctrlBase hphase hhead
    (by rw [← hlen]; omega)
    (by rw [← encodeCtrlStackR_eq_walkZone]; exact hctrl)
    (fun p hp => hczeros p (by rw [← hlen] at hp; omega) (by rw [← hlen] at hp; omega))
    (fun p hp => hczeros p (by rw [← hlen] at hp; omega) (by rw [← hlen] at hp; omega))
  exact ⟨hf1, by rw [hf2, ← hlen], hf3⟩

/-- **Return leg 5 (scan → the cursor marker `M`).** -/
theorem corridor_back_scan_to_M {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := gammaSelfLoopScan.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 1) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.certEnd - (encodePreorder width h_width st.toks).length - 1 - (c0.head : Nat)) + 1)).state).fst
        : Nat) = 1
    ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.certEnd - (encodePreorder width h_width st.toks).length - 1 - (c0.head : Nat)) + 1)).head
        : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1
    ∧ (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM) c0
        ((z.certEnd - (encodePreorder width h_width st.toks).length - 1 - (c0.head : Nat)) + 1)).tape
        = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have := gammaSelfLoopScan_runConfigFrom_terminator c0 hphase
    (z.certEnd - (encodePreorder width h_width st.toks).length - 1 - (c0.head : Nat))
    (by omega)
    (fun p hp1 hp2 => hczeros p (by omega) (by omega))
    (fun p hp => hM p (by omega))
  rwa [show (c0.head : Nat)
      + (z.certEnd - (encodePreorder width h_width st.toks).length - 1 - (c0.head : Nat))
      = z.certEnd - (encodePreorder width h_width st.toks).length - 1 from by omega] at this

end ContractExpansion
end Frontier
end Pnp4
