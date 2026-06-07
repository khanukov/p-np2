import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanOutput
import Pnp4.Frontier.ContractExpansion.TreeMCSPCounterDecodeFin

/-!
# `binToUnaryLoopFullScan` — D2t-3 transcoder correctness capstone (NP-verifier track — `ζ`)

The headline tying D2t-3's sound binary→unary transcoder together.  Composing
`binToUnaryLoopFullScan_reachesSink_output` (the loop halts and the produced unary block has length
`u + counterValue B`) with the `counterValue ↔ decodeFin` bridge (`decodeFin_tapeBits`), this states the
full `ζ` correctness: from a valid `LoopLayout`, the loop reaches its sink, the width-`w` input window
decodes to some `i : Fin (2^w)`, and the produced unary block has length `u₀ + i.val` — i.e.
`|U| = value(B) = (decodeFin w …).val`, the seed `u₀` plus exactly `value(B)` fresh `1`s.

This settles the sound full-scan transcoder end-to-end: **δ** (sound zero-test `bZeroFullScan`), **ε** (the
loop — `hbase`, `hstep`/`oneIteration`, `reachesSink`), and **ζ** (output length against `decodeFin`).

**Progress classification (AGENTS.md): Infrastructure** — a verifier-component correctness statement; it
proves no separation and makes no `P ≠ NP` claim.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **D2t-3 transcoder correctness (the `ζ` headline).**  From a valid `LoopLayout` config, the sound
binary→unary loop halts (reaches its sink `w + 2`), the width-`w` input window decodes to `i`
(`decodeFin w (tapeBits …) = some i`), and the produced unary block `[HOME - (u + i.val), HOME)` is all
`1` — length `u₀ + i.val`, the seed plus exactly `value(B) = i.val` fresh `1`s.  This is
`|U| = value(B) = (decodeFin w …).val`. -/
theorem binToUnaryLoopFullScan_transcoder_correct (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat)
    (hL : LoopLayout w c u) :
    ∃ (t : Nat) (i : Fin (2 ^ w)),
      ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).state.fst : Nat) = w + 2
      ∧ decodeFin w (tapeBits c ((c.head : Nat) + 1) w) = some i
      ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
          (c.head : Nat) - (u + i.val) ≤ (q : Nat) → (q : Nat) < (c.head : Nat) →
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c t).tape q = true) := by
  have hlt : counterValue c ((c.head : Nat) + 1) w < 2 ^ w := counterValue_lt_two_pow c _ w
  obtain ⟨t, hsink, hU⟩ :=
    binToUnaryLoopFullScan_reachesSink_output w (counterValue c ((c.head : Nat) + 1) w) c u hL rfl
  refine ⟨t, ⟨counterValue c ((c.head : Nat) + 1) w, hlt⟩, hsink,
    decodeFin_tapeBits c ((c.head : Nat) + 1) w hlt, ?_⟩
  intro q hq1 hq2
  exact hU q hq1 hq2

end ContractExpansion
end Frontier
end Pnp4
