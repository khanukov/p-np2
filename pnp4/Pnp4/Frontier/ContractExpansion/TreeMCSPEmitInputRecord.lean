import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanCorrect

/-!
# `emitInputRecord` — D2t-4b: emit an `input i` gate record `0 1^i 0` (NP-verifier leaf emit)

The second **leaf-emit** brick (D2t-4b).  An `input i` gate encodes (`encodeGateRecord`, D0) as
`unaryField 0 ++ unaryField i = [false] ++ 1^i ++ [false]` (`0 1^i 0`) — the tag `0`, the index in unary,
the field terminator `0`.  The `1^i` is exactly the **binary→unary of the index** produced by D2t-3's
`binToUnaryLoopFullScan`: from a `LoopLayout w c u` config the loop halts with the unary block
`[HOME - (u + i), HOME)` all `1` (`transcoder_correct`), and — proved here — the **sentinel `HOME` stays
`0`**, so the window `[HOME - i, HOME]` realises `unaryField i = 1^i 0` directly on the tape.

This module ships the layout-reconciliation core of D2t-4b:
* `binToUnaryLoopFullScan_reachesSink_output_framed` — strengthens `reachesSink_output` with sentinel
  preservation (`LoopLayout`'s sentinel is preserved by every iteration and the `B=0` base path).
* `emitInputRecord_runConfig_unaryField` — from `LoopLayout`, the loop halts, the width-`w` window decodes
  to `i`, and the window `[HOME - i, HOME]` holds `unaryField i` (the `i` value-ones + the terminator `0`).

The tag-`0` framing into the full `encodeGateRecord (.input i)` record is the next brick.

**Progress classification (AGENTS.md): Infrastructure** — a verifier emit-component proven against the
pure record codec; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **Sentinel-framed reachesSink/output.**  Strengthens `binToUnaryLoopFullScan_reachesSink_output` with
the fact that the sentinel cell `HOME` still holds `0` at the sink: it is part of the `LoopLayout`
invariant, preserved by every `B > 0` iteration (`oneIteration` re-establishes the layout) and by the
`B = 0` base path (`hbase_tape` leaves the tape unchanged). -/
theorem binToUnaryLoopFullScan_reachesSink_output_framed (w : Nat) {L : Nat} :
    ∀ (m : Nat) (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat),
      LoopLayout w c u → counterValue c ((c.head : Nat) + 1) w = m →
      ∃ t, ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).state.fst : Nat) = w + 2
        ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
            (c.head : Nat) - (u + m) ≤ (q : Nat) → (q : Nat) < (c.head : Nat) →
            (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape q = true)
        ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape c.head = false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c u hL hm
    obtain ⟨hph0, hu1, hHOME1, hbound, hsent, hUlay, hblank, hroom⟩ := hL
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · refine ⟨2 + w, binToUnaryLoopFullScan_runConfig_hbase w c hph0 (by omega) (by rw [hm]; exact hm0),
        ?_, ?_⟩
      · intro q hq1 hq2
        rw [binToUnaryLoopFullScan_runConfig_hbase_tape w c hph0 (by omega) (by rw [hm]; exact hm0)]
        exact hUlay q (by omega) hq2
      · rw [binToUnaryLoopFullScan_runConfig_hbase_tape w c hph0 (by omega) (by rw [hm]; exact hm0)]
        exact hsent
    · obtain ⟨sB, _, hhd, hLnext, hdec⟩ :=
        binToUnaryLoopFullScan_oneIteration w c u
          ⟨hph0, hu1, hHOME1, hbound, hsent, hUlay, hblank, hroom⟩ (by rw [hm]; omega)
      set d := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (sB + 1) with hddef
      have hmlt : counterValue d ((d.head : Nat) + 1) w < m := by
        rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      obtain ⟨t, htsink, htU, htsent⟩ :=
        ih (counterValue d ((d.head : Nat) + 1) w) hmlt d (u + 1) hLnext rfl
      refine ⟨(sB + 1) + t, by rw [TM.runConfig_add, ← hddef]; exact htsink, ?_, ?_⟩
      · intro q hq1 hq2
        rw [TM.runConfig_add, ← hddef]
        have hdc : counterValue d ((d.head : Nat) + 1) w + 1 = m := by
          rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
        apply htU q
        · rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
        · rw [show (d.head : Nat) = (c.head : Nat) from hhd]; omega
      · rw [TM.runConfig_add, ← hddef, show c.head = d.head from Fin.ext (by rw [hhd])]
        exact htsent

/-- **D2t-4b core — the index as a unary field.**  From a valid `LoopLayout`, the sound loop halts, the
width-`w` input window decodes to `i = decodeFin …`, and the tape window `[HOME - i, HOME]` holds
`unaryField i = 1^i 0`: the `i` value-ones (`[HOME - i, HOME)`) and the terminator `0` at `HOME`.  This is
the binary→unary of the index, framed as a self-delimiting unary field — the substance of an `input i`
record (`encodeGateRecord (.input i) = unaryField 0 ++ unaryField i`); the leading tag-`0` is the next
brick. -/
theorem emitInputRecord_runConfig_unaryField (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat)
    (hL : LoopLayout w c u) :
    ∃ (t : Nat) (i : Fin (2 ^ w)),
      ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).state.fst : Nat) = w + 2
      ∧ decodeFin w (tapeBits c ((c.head : Nat) + 1) w) = some i
      ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (c.head : Nat) - i.val ≤ (q : Nat) → (q : Nat) < (c.head : Nat) →
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape q = true)
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape c.head = false := by
  have hlt : counterValue c ((c.head : Nat) + 1) w < 2 ^ w := counterValue_lt_two_pow c _ w
  obtain ⟨t, hsink, hU, hsent⟩ :=
    binToUnaryLoopFullScan_reachesSink_output_framed w (counterValue c ((c.head : Nat) + 1) w) c u hL rfl
  refine ⟨t, ⟨counterValue c ((c.head : Nat) + 1) w, hlt⟩, hsink,
    decodeFin_tapeBits c ((c.head : Nat) + 1) w hlt, ?_, hsent⟩
  intro q hq1 hq2
  simp only [Fin.val_mk] at hq1
  -- the `i` value-ones sit inside the `u + i`-wide block, so they are all `1`
  exact hU q (by omega) hq2

end ContractExpansion
end Frontier
end Pnp4
