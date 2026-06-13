import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkFull
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftProgram

/-!
# Corridor routes — D2t-5b (Block A4r): the leftward cross-zone route, machine by machine

The driver's settle/emit arms travel `M → control top → value top → WORK frontier`.  Under
`driverCorridorInv` (A3, with the strict inter-zone gaps) every leg is one of two proven machines:

* a **0-corridor scan** (`selfLoopScanLeft`: scan left over `0`s, stop on the first `1`), landing on a
  pinned anchor — the stack's rightmost content cell (`windowSpells_getLast_true`) or the frontier
  marker `FM`;
* a **zone walk** (`zoneWalkLeft_runConfig_walkZone`, A4w), crossing a whole stack zone and parking on
  the dead `0` just left of its base sentinel — exactly where the next scan starts.

This module instantiates the legs against the invariant's clauses (run lemmas with exact step
counts, tape unchanged): `corridor_scan_M_to_ctrlTop`, `corridor_walk_ctrl`,
`corridor_scan_to_shwTop`, `corridor_scan_to_valTop`, `corridor_walk_val`, `corridor_scan_to_FM`.
With the shadow-count zone `SHW` between the value and control zones, the leftward route from the
control base crosses it in stages: the 0-scan from `ctrlBase − 1` lands on **`SHW`'s top `1`**
(`corridor_scan_to_shwTop`); the 0-scan towards the value top starts from the dead cell
`shwBase − 1` left of the zone (`corridor_scan_to_valTop`).  (The connector crossing the `SHW`
`1`-block leftward — a scan-over-ones — is part of the pop-arm brick that consumes this route.)
The A5 `driverBody` assembly sequences the legs (each leg is stated on its own component machine, as
throughout the toolkit; the `seq`-composition layer transfers them into the assembled body).

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

/-- A spelled window whose bit-list ends in `1` pins its **rightmost cell** to `1`. -/
theorem windowSpells_getLast_true {L : Nat} (tape : Fin L → Bool) (base : Nat) (bits : List Bool)
    (h : windowSpells tape base bits) (hlast : bits.getLast? = some true) :
    ∀ p : Fin L, (p : Nat) = base + bits.length - 1 → tape p = true := by
  intro p hp
  have hne : bits ≠ [] := by
    intro hb; rw [hb] at hlast; simp at hlast
  have hlen : 1 ≤ bits.length := List.length_pos_iff.mpr hne
  obtain ⟨hfit, hcells⟩ := h
  rw [hcells p (by omega) (by omega)]
  have hidx : (p : Nat) - base = bits.length - 1 := by omega
  rw [hidx, List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hlast]
  rfl

/-- **Leg 1 (scan M → control top).**  From the dead cell `cursor − 2` (just left of the cursor
marker), the leftward 0-scan stops exactly on the control stack's rightmost content cell, in
`(head − K) + 1` steps where `K = ctrlBase + |encodeCtrlStackR st.ctrl| − 1`, tape unchanged. -/
theorem corridor_scan_M_to_ctrlTop {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat)
      = z.certEnd - (encodePreorder width h_width st.toks).length - 2) :
    (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1)) + 1)).state).fst
        : Nat) = 1
    ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1)) + 1)).head : Nat)
        = z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1
    ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1)) + 1)).tape
        = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen1 : 1 ≤ (encodeCtrlStackR st.ctrl).length := by
    have := encodeCtrlStackR_getLast_true st.ctrl
    cases hctrl' : encodeCtrlStackR st.ctrl with
    | nil => rw [hctrl'] at this; simp at this
    | cons a l => simp
  exact selfLoopScanLeft_runConfig_terminator c0 hphase
    (z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1)
    (by omega)
    (fun p hp1 hp2 => hczeros p (by omega) (by omega))
    (windowSpells_getLast_true c0.tape z.ctrlBase _ hctrl (encodeCtrlStackR_getLast_true st.ctrl))

/-- **Leg 2 (walk the control zone).**  From the control top (every frame's `rem ≥ 1` — the
reachability fact from `Pending`), the walker crosses the whole control zone and parks on the dead
`0` at `ctrlBase − 1`, in `walkZoneSteps` steps, tape unchanged. -/
theorem corridor_walk_ctrl {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hrem : ∀ f ∈ st.ctrl, 1 ≤ f.2)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1) :
    (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).head : Nat)
        = z.ctrlBase - 1
    ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]))).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen : (encodeCtrlStackR st.ctrl).length
      = (walkZone (st.ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])).length := by
    rw [encodeCtrlStackR_eq_walkZone]
  obtain ⟨hw1, hw2, hw3, _⟩ := zoneWalkLeft_runConfig_walkZone c0
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
    z.ctrlBase (by omega) hphase
    (by rw [hhead, hlen])
    (by rw [← encodeCtrlStackR_eq_walkZone]; exact hctrl)
    (fun p hp => hszeros p (by omega) (by omega))
  exact ⟨hw1, hw2, hw3⟩

/-- **Leg 3 (scan → the shadow-count top).**  From the dead cell `ctrlBase − 1`, the leftward 0-scan
stops on the `SHW` window's rightmost `1` (`shwBase + |out|`), tape unchanged.  (Crossing the `SHW`
`1`-block towards the value zone is a scan-over-ones connector, supplied with the pop arm.) -/
theorem corridor_scan_to_shwTop {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase - 1) :
    (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.shwBase + st.out.length)) + 1)).state).fst : Nat) = 1
    ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.shwBase + st.out.length)) + 1)).head : Nat)
        = z.shwBase + st.out.length
    ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.shwBase + st.out.length)) + 1)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hterm : ∀ p : Fin (selfLoopScanLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = z.shwBase + st.out.length → c0.tape p = true := by
    have := windowSpells_getLast_true c0.tape z.shwBase _ hshw (by
      rw [List.getLast?_replicate]
      simp)
    rw [List.length_replicate] at this
    intro p hp
    exact this p (by omega)
  exact selfLoopScanLeft_runConfig_terminator c0 hphase
    (z.shwBase + st.out.length)
    (by omega)
    (fun p hp1 hp2 => hszeros p (by omega) (by omega))
    hterm

/-- **Leg 3′ (scan → value top).**  From the dead cell `shwBase − 1` (just left of the shadow-count
zone), the leftward 0-scan stops on the value stack's rightmost content cell, tape unchanged. -/
theorem corridor_scan_to_valTop {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.shwBase - 1) :
    (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.valBase + (encodeNatStackR st.val).length - 1)) + 1)).state).fst
        : Nat) = 1
    ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.valBase + (encodeNatStackR st.val).length - 1)) + 1)).head : Nat)
        = z.valBase + (encodeNatStackR st.val).length - 1
    ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.valBase + (encodeNatStackR st.val).length - 1)) + 1)).tape
        = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen1 : 1 ≤ (encodeNatStackR st.val).length := by
    cases hv : encodeNatStackR st.val with
    | nil =>
        have := encodeNatStackR_getLast_true st.val
        rw [hv] at this; simp at this
    | cons a l => simp
  exact selfLoopScanLeft_runConfig_terminator c0 hphase
    (z.valBase + (encodeNatStackR st.val).length - 1)
    (by omega)
    (fun p hp1 hp2 => hvzeros p (by omega) (by omega))
    (windowSpells_getLast_true c0.tape z.valBase _ hval (encodeNatStackR_getLast_true st.val))

/-- **Leg 4 (walk the value zone).**  From the value top, the walker crosses the whole value zone
and parks on the dead `0` at `valBase − 1` (value blocks are `v + 2 ≥ 2` unconditionally), tape
unchanged. -/
theorem corridor_walk_val {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.valBase + (encodeNatStackR st.val).length - 1) :
    (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.val.map (· + 2)))).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.val.map (· + 2)))).head : Nat) = z.valBase - 1
    ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0
        (walkZoneSteps (st.val.map (· + 2)))).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hlen : (encodeNatStackR st.val).length = (walkZone (st.val.map (· + 2))).length := by
    rw [encodeNatStackR_eq_walkZone]
  obtain ⟨hw1, hw2, hw3, _⟩ := zoneWalkLeft_runConfig_walkZone c0 (st.val.map (· + 2))
    (by
      intro k hk
      rw [List.mem_map] at hk
      obtain ⟨v, -, rfl⟩ := hk
      omega)
    z.valBase (by omega) hphase
    (by rw [hhead, hlen])
    (by rw [← encodeNatStackR_eq_walkZone]; exact hval)
    (fun p hp => hfzeros p (by omega) (by omega))
  exact ⟨hw1, hw2, hw3⟩

/-- **Leg 5 (scan → the WORK frontier marker).**  From the dead cell `valBase − 1`, the leftward
0-scan stops exactly on `FM` (the `1` just past the last record), tape unchanged. -/
theorem corridor_scan_to_FM {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanLeft.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.valBase - 1) :
    (((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.workBase + (encodeGateRecordStream st.out).length)) + 1)).state).fst
        : Nat) = 1
    ∧ ((TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.workBase + (encodeGateRecordStream st.out).length)) + 1)).head : Nat)
        = z.workBase + (encodeGateRecordStream st.out).length
    ∧ (TM.runConfig (M := selfLoopScanLeft.toPhased.toTM) c0
        (((c0.head : Nat) - (z.workBase + (encodeGateRecordStream st.out).length)) + 1)).tape
        = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  exact selfLoopScanLeft_runConfig_terminator c0 hphase
    (z.workBase + (encodeGateRecordStream st.out).length)
    (by omega)
    (fun p hp1 hp2 => hfzeros p (by omega) (by omega))
    (fun p hp => hFM p hp)

end ContractExpansion
end Frontier
end Pnp4
