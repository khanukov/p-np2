import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionAtomHops

/-!
# The clear iteration, end to end — D2t-5b (Block A5m-3, run)

The first complete arm run on a concrete U-stack machine: on `clearIterProgram`, for a state with
an **empty control stack**, from the settle home (phase `0`, head on the cursor marker `M`), the
machine hops to the control top, probes (empty verdict), steps back over the sentinel and scans
home — ending at the read home (phase `14`), head back on `M`, **tape untouched** — in an explicit
step count bounded by `2 · certEnd + 13`.  The tape identity is exactly `driverStepTape` on the
clear branch, so this is the per-iteration fact of the eventual `DriverRealization` instance,
specialised to the clear arm.

Every leg is one instantiation: the atom hops (A5m-3a′), the U3 scans, and the region contracts of
`clearIterProgram`; every tape-side hypothesis (zeros, anchors) is a clause of
`driverCorridorInv`.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine's end-to-end run;
proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No
`P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The clear iteration, end to end.**  For a state with an empty control stack, from the settle
home (phase `0`, head on the cursor marker), `clearIterProgram` reaches the read home (phase `14`)
with the head back on the marker and the tape untouched, within `2 · certEnd + 13` steps. -/
theorem clearIter_run {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := clearIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = [])
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 13
      ∧ (((TM.runConfig (M := clearIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 14
      ∧ ((TM.runConfig (M := clearIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width st.toks).length - 1
      ∧ (TM.runConfig (M := clearIterProgram.toPhased.toTM) c0 T).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  replace hmark : ∀ p : Fin (clearIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (clearIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hsfit : z.shwBase + st.out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin (clearIterProgram.toPhased.toTM.tapeLength L),
      z.shwBase + st.out.length + 1 ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → c0.tape p = false := hszeros
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  -- The marker position and the empty-stack geometry.
  set M := z.certEnd - (encodePreorder width h_width st.toks).length - 1 with hM
  have hctrl_len : (encodeCtrlStackR st.ctrl).length = 1 := by rw [hctrl]; rfl
  have hsentinel : ∀ p : Fin (clearIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.ctrlBase → c0.tape p = true := by
    intro p hp
    have := windowSpells_cell c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) hctrlw 0
      (by rw [hctrl_len]; omega) p (by omega)
    rw [this, hctrl]
    rfl
  have hMlow : z.certBase - 1 ≤ M := by omega
  have hM1 : z.ctrlBase + 2 ≤ M := by omega
  -- Leg 1 (phases 0–1): step left off the marker.
  obtain ⟨hp1, hh1, ht1⟩ := clearIter_region_stepLeft.run_stepLeft_hop c0 hphase
    (by omega)
  -- Leg 2 (phases 2–3): scan left onto the control sentinel.
  set c1 := TM.runConfig (M := clearIterProgram.toPhased.toTM) c0 2 with hc1
  obtain ⟨hp2, hh2, ht2⟩ := clearIter_region_scanLeft.run_scanLeft_hop c1 hp1 z.ctrlBase
    (by omega)
    (fun p hlo hhi => by
      rw [ht1]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [ht1]; exact hsentinel p hp)
  -- Leg 3 (phases 4–7): the probe, empty verdict.
  set c2 := TM.runConfig (M := clearIterProgram.toPhased.toTM) c1
    (((c1.head : Nat) - z.ctrlBase) + 2) with hc2
  obtain ⟨hp3, hh3, ht3⟩ := clearIter_region_probe.run_probe_empty_hop
    (by rfl) (by rfl) (by rfl) c2 hp2 (by omega)
    (fun p hp => by
      rw [ht2, ht1]
      exact hszeros p (by omega) (by omega))
  -- Leg 4 (phases 8–9): step right onto the sentinel.
  set c3 := TM.runConfig (M := clearIterProgram.toPhased.toTM) c2 3 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := clearIter_region_stepRight1.run_stepRight_hop c3 hp3
    (by
      have hfin : (c3.head : Nat) < clearIterProgram.toPhased.toTM.tapeLength L := c3.head.isLt
      omega)
  -- Leg 5 (phases 10–11): step right over the sentinel.
  set c4 := TM.runConfig (M := clearIterProgram.toPhased.toTM) c3 2 with hc4
  obtain ⟨hp5, hh5, ht5⟩ := clearIter_region_stepRight2.run_stepRight_hop c4 hp4
    (by
      have hfin : (c4.head : Nat) < clearIterProgram.toPhased.toTM.tapeLength L := c4.head.isLt
      have hM' : M < clearIterProgram.toPhased.toTM.tapeLength L := by
        have := c0.head.isLt; omega
      omega)
  -- Leg 6 (phases 12–13): scan right home onto the marker.
  set c5 := TM.runConfig (M := clearIterProgram.toPhased.toTM) c4 2 with hc5
  have hh5' : (c5.head : Nat) + (M - (z.ctrlBase + 1)) = M := by omega
  obtain ⟨hp6, hh6, ht6⟩ := clearIter_region_scanRight.run_scanRight_hop c5 hp5
    (M - (z.ctrlBase + 1))
    (by
      have hM' : M < clearIterProgram.toPhased.toTM.tapeLength L := by
        have := c0.head.isLt; omega
      omega)
    (fun p hlo hhi => by
      rw [ht5, ht4, ht3, ht2, ht1]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [ht5, ht4, ht3, ht2, ht1]
      exact hmark p (by omega))
  -- Assemble the chain (right-nested junctions; each split is one controlled rewrite).
  have hfinal : TM.runConfig (M := clearIterProgram.toPhased.toTM) c0
      (2 + ((((c1.head : Nat) - z.ctrlBase) + 2)
        + (3 + (2 + (2 + ((M - (z.ctrlBase + 1)) + 2))))))
      = TM.runConfig (M := clearIterProgram.toPhased.toTM) c5 ((M - (z.ctrlBase + 1)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  refine ⟨2 + ((((c1.head : Nat) - z.ctrlBase) + 2)
      + (3 + (2 + (2 + ((M - (z.ctrlBase + 1)) + 2))))), by omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp6]
  · rw [hfinal]
    omega
  · rw [hfinal, ht6, ht5, ht4, ht3, ht2, ht1]

end ContractExpansion
end Frontier
end Pnp4
