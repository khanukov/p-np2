import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanReachesSink

/-!
# `binToUnaryLoopFullScan` — ζ core: the produced unary block has length `value(B)` (D2t-3 `ε`)

The output-correctness core of `ε`.  `reachesSink` (the prior brick) shows the sound loop halts; this
module shows **what it produced**: from a `LoopLayout w c u` config the loop reaches its sink with the
cells `[HOME - (u + counterValue B), HOME)` all `1` — a unary block of length `u + counterValue B =
u₀ + value(B)` (the seed `u₀` plus one `1` per decrement of `B`).  So the produced answer block has length
`value(B)` — the `ζ` bridge `|U| = value(B)`.

* `binToUnaryLoopFullScan_runConfig_hbase_tape` — the `B = 0` path to the sink leaves the tape unchanged
  (it only scans the all-`0` `B` block, never touching `U`), so the base case keeps `U` intact.
* `binToUnaryLoopFullScan_reachesSink_output` — bespoke strong induction on `counterValue B`: each `B > 0`
  pass (`oneIteration`) appends one `1` (`u ↦ u+1`, `counterValue ↦ counterValue-1`), so the invariant
  `u + counterValue B` — the block length — is preserved to the sink.

This settles `ε`'s run behaviour **and** its output length against `counterValue`.  The only remaining
formality is the pure spec identity `counterValue (little-endian B) = (decodeFin w …).val` connecting the
on-tape counter to the `Encoding.decodeFin` reference — a `BinaryCounter`/`Encoding` arithmetic lemma with
no run content.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- `hbase` with tape preservation: the `B = 0` path to the sink leaves the tape unchanged (it only scans
the all-`0` `B` block; it never touches `U`). -/
theorem binToUnaryLoopFullScan_runConfig_hbase_tape (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 1 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzero : counterValue c0 ((c0.head : Nat) + 1) w = 0) :
    (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + w)).tape = c0.tape := by
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
  have hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c2.head : Nat) ≤ (q : Nat) → (q : Nat) < (c2.head : Nat) + w → c2.tape q = false := by
    intro q hq1 hq2
    rw [h2t]
    have hqlt : (q : Nat) - ((c0.head : Nat) + 1) < w := by rw [h2h] at hq2; omega
    have hqge : (c0.head : Nat) + 1 ≤ (q : Nat) := by rw [h2h] at hq1; omega
    have := counterValue_eq_zero_imp_all_false c0 ((c0.head : Nat) + 1) w hzero
      ((q : Nat) - ((c0.head : Nat) + 1)) hqlt (by omega)
    simpa [Nat.add_sub_cancel' hqge] using this
  obtain ⟨_, _, hst⟩ := binToUnaryLoopFullScan_runConfig_scanning w c2 h2p w (le_refl w)
    (by rw [h2h]; omega) hzeros
  have : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + w)
      = TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2 w := by
    rw [hc2, ← TM.runConfig_add]
  rw [this, hst, h2t]


/-- **ζ core — the produced unary block.**  From a `LoopLayout w c u` config, the loop reaches its sink
and the cells `[HOME - (u + counterValue B), HOME)` are all `1`: the unary block of length
`u + counterValue B = u₀ + value(B)`.  (With the seed `u₀`, the produced answer block has length
`value(B)`.)  Bespoke strong induction on `counterValue B`, base `B = 0` (head scans to the sink, `U`
untouched, length `u`), step `B > 0` (one pass appends a `1`, `u ↦ u+1`, `counterValue ↦ counterValue-1`,
the block length `u + counterValue` preserved). -/
theorem binToUnaryLoopFullScan_reachesSink_output (w : Nat) {L : Nat} :
    ∀ (m : Nat) (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat),
      LoopLayout w c u → counterValue c ((c.head : Nat) + 1) w = m →
      ∃ t, ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).state.fst : Nat) = w + 2
        ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
            (c.head : Nat) - (u + m) ≤ (q : Nat) → (q : Nat) < (c.head : Nat) →
            (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape q = true) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c u hL hm
    obtain ⟨hph0, hu1, hHOME1, hbound, hsent, hUlay, hblank, hroom⟩ := hL
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · refine ⟨2 + w, binToUnaryLoopFullScan_runConfig_hbase w c hph0 (by omega) (by rw [hm]; exact hm0), ?_⟩
      intro q hq1 hq2
      rw [binToUnaryLoopFullScan_runConfig_hbase_tape w c hph0 (by omega) (by rw [hm]; exact hm0)]
      exact hUlay q (by omega) hq2
    · obtain ⟨sB, _, hhd, hLnext, hdec⟩ :=
        binToUnaryLoopFullScan_oneIteration w c u
          ⟨hph0, hu1, hHOME1, hbound, hsent, hUlay, hblank, hroom⟩ (by rw [hm]; omega)
      set d := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1) with hddef
      have hmlt : counterValue d ((d.head : Nat) + 1) w < m := by
        rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      obtain ⟨t, htsink, htU⟩ :=
        ih (counterValue d ((d.head : Nat) + 1) w) hmlt d (u + 1) hLnext rfl
      refine ⟨(sB + 1) + t, by rw [TM.runConfig_add, ← hddef]; exact htsink, ?_⟩
      intro q hq1 hq2
      rw [TM.runConfig_add, ← hddef]
      have hdc : counterValue d ((d.head : Nat) + 1) w + 1 = m := by
        rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      apply htU q
      · rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      · rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega

end ContractExpansion
end Frontier
end Pnp4
