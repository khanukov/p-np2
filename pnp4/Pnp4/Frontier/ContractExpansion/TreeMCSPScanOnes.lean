import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# Crossing the `SHW` block — D2t-5b (Block A4r, connectors): the ones-scanners on the corridor

The shadow-count zone `SHW` spells a contiguous `1`-block (`1^(|out|+1)`), and the emit arms must
cross it in both directions: the leftward route `ctrlBase − 1 → SHW top → … → value top` (the
connector promised by `corridor_scan_to_shwTop`), and the rightward return, which after a
value-push restore lands exactly on the **tick cell** `shwBase + |out| + 1`.  The motion
primitives — `selfLoopScanLeftOne` / `selfLoopScanRightOne`, the bit-duals of the 0-corridor
scanners — are already in the toolkit with their terminator run lemmas; this module instantiates
them against `driverCorridorInv`'s `SHW` clauses:

* `corridor_cross_shw_left` — from `SHW`'s top `1` to the dead cell `shwBase − 1`, in
  `|out| + 2` steps, tape unchanged;
* `corridor_cross_shw_right` — from `SHW`'s base `1` to the tick cell `shwBase + |out| + 1`, in
  `|out| + 2` steps, tape unchanged.

Both are sound on the **single-`1`** block too (`|out| = 0`): the scan's first move already lands
next to the bounding `0`.

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

/-- `getD` into an all-`true` block is `true` at every in-range index (local form; the
`SettleProbe` copy lives far downstream of this module). -/
private theorem scanOnes_getD_replicate_true (m i : Nat) (h : i < m) :
    (List.replicate m true).getD i false = true := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      cases i with
      | zero => rfl
      | succ i => rw [List.replicate_succ, List.getD_cons_succ]; exact ih i (by omega)

/-- **The `SHW` block, crossed leftward.**  From its top `1` (`shwBase + |out|`),
`selfLoopScanLeftOne` lands on the dead cell `shwBase − 1` in `|out| + 2` steps, tape unchanged —
the connector between `corridor_scan_to_shwTop` and `corridor_scan_to_valTop`. -/
theorem corridor_cross_shw_left {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanLeftOne.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.shwBase + st.out.length) :
    (((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0
        (st.out.length + 2)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0
          (st.out.length + 2)).head : Nat) = z.shwBase - 1
      ∧ (TM.runConfig (M := selfLoopScanLeftOne.toPhased.toTM) c0
          (st.out.length + 2)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hvfit' : z.valBase + (encodeNatStackR st.val).length ≤ z.valEnd := hvfit
  have hones : ∀ p : Fin (selfLoopScanLeftOne.toPhased.toTM.tapeLength L),
      z.shwBase - 1 < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true := by
    intro p hp1 hp2
    have := hshw.2 p (by omega) (by rw [List.length_replicate]; omega)
    rw [this]
    exact scanOnes_getD_replicate_true _ _ (by omega)
  have hterm : ∀ p : Fin (selfLoopScanLeftOne.toPhased.toTM.tapeLength L),
      (p : Nat) = z.shwBase - 1 → c0.tape p = false := by
    intro p hp
    exact hvzeros p (by omega) (by omega)
  have hsteps : (c0.head : Nat) - (z.shwBase - 1) + 1 = st.out.length + 2 := by omega
  rw [← hsteps]
  exact selfLoopScanLeftOne_runConfig_terminator c0 hphase (z.shwBase - 1) (by omega) hones hterm

/-- **The `SHW` block, crossed rightward.**  From its base `1` (`shwBase`),
`selfLoopScanRightOne` lands on the first `0` past the block — exactly the **tick cell**
`shwBase + |out| + 1` — in `|out| + 2` steps, tape unchanged. -/
theorem corridor_cross_shw_right {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.shwBase) :
    (((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
        (st.out.length + 2)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
          (st.out.length + 2)).head : Nat) = z.shwBase + st.out.length + 1
      ∧ (TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
          (st.out.length + 2)).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  have hfin : z.ctrlEnd < selfLoopScanRightOne.toPhased.toTM.tapeLength L := by
    have := c0.head.isLt
    omega
  have hones : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < z.shwBase + st.out.length + 1 →
      c0.tape p = true := by
    intro p hp1 hp2
    have := hshw.2 p (by omega) (by rw [List.length_replicate]; omega)
    rw [this]
    exact scanOnes_getD_replicate_true _ _ (by omega)
  have hterm : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (p : Nat) = z.shwBase + st.out.length + 1 → c0.tape p = false := by
    intro p hp
    exact hszeros p (by omega) (by omega)
  have := selfLoopScanRightOne_runConfig_terminator c0 hphase
    (z.shwBase + st.out.length + 1) (by omega) (by omega) hones hterm
  rwa [show z.shwBase + st.out.length + 1 - (c0.head : Nat) + 1 = st.out.length + 2 from
    by omega] at this

end ContractExpansion
end Frontier
end Pnp4
