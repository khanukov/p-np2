import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroFullScan
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehome

/-!
# `binToUnaryLoopFullScan` — the binary→unary loop on the SOUND zero-test (NP-verifier track — D2t-3 `ε`)

The merged `binToUnaryLoopRehome` (`TreeMCSPBinToUnaryLoopRehome.lean`) routes via the **unsound**
`bZeroRouteProgram` (PR #1582).  This module assembles the **revised** loop on the sound width-`w`
zero-test `bZeroFullScan` (`TreeMCSPBZeroFullScan.lean`, the δ layer):

```
binToUnaryLoopBodyFullScan w :=
  seq stepRightOnce                       -- HOME → B's low end (HOME+1)
    (seq (bZeroFullScanRouteBody w)        -- sound scan of the w-window; B=0 → terminal, B>0 → accept
      (seq stepRightOnce                   -- step past the located set bit (→ HOME+j+2, the seek start)
        (seq seekHomeAfterRoute            -- re-home to the sentinel (reuses the proven seek design)
          binToUnaryBody)))                -- one pass: decrement B, append to U, return to HOME
binToUnaryLoopFullScan w := loopUntilSink (binToUnaryLoopBodyFullScan w) ⟨w + 2⟩
```

* The leading `stepRightOnce` places the scan window at exactly `[HOME+1, HOME+1+w)`, matching the
  `counterValue` measure.  `bZeroFullScanRouteBody` (the `B>0`-re-pointed accept) hands off into the body
  legs on `B > 0` and leaves its `B = 0` phase (composition phase `w + 2`) terminal for the sink.
* The interposed `stepRightOnce` advances the head from the located set bit (`HOME+1+j`) to `HOME+j+2`,
  the discriminator-style position the proven `seekHomeAfterRoute` design re-homes from — so the existing
  seek + body navigation transfers (its run-through is re-derived on this machine in the follow-up).
* `loopUntilSink … ⟨w + 2⟩` re-enters the body on its accept (a completed `B > 0` pass) and halts at the
  sink phase `w + 2` (`B = 0`).

This brick ships the **definitions + phase-count facts** (the loop object and its shape), introduced
**additively** so the unsound `binToUnaryLoopRehome` stays intact.  The run behaviour — `hbase`
(`B = 0` → sink, via the δ seqP2 `zero` lift), the fresh seek + body run-through on this machine,
`hstep` (`B > 0` → re-enter with `counterValue B` decreasing), then `loopUntilSink_reachesSink` and the
`ζ` bridge `|U| = value B` — is the follow-up.

**Progress classification (AGENTS.md): Infrastructure** — the sound loop assembly toward the
NP-membership leg; it proves no run behaviour and no separation here.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The revised loop body on the sound zero-test: step to `B`'s low end, run the width-`w` full scan,
and on `B > 0` step past the located set bit, re-home, and run one pass of `binToUnaryBody`. -/
def binToUnaryLoopBodyFullScan (w : Nat) : ConstStatePhasedProgram Unit :=
  seq stepRightOnce
    (seq (bZeroFullScanRouteBody w)
      (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)))

/-- Phase count: `stepRightOnce (2) + bZeroFullScanRouteBody (w+2) + stepRightOnce (2) +
seekHomeAfterRoute (9) + binToUnaryBody (15) = w + 30`. -/
@[simp] theorem binToUnaryLoopBodyFullScan_numPhases (w : Nat) :
    (binToUnaryLoopBodyFullScan w).numPhases = w + 30 := by
  simp only [binToUnaryLoopBodyFullScan, seq_numPhases, bZeroFullScanRouteBody_numPhases,
    stepRightOnce_numPhases, seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases]
  omega

/-- The sound binary→unary loop: re-enter the body on its accept (a completed `B > 0` pass), halt at the
sink phase `w + 2` (`B = 0`, the full scan's `B=0` outcome lifted past the leading `stepRightOnce`). -/
def binToUnaryLoopFullScan (w : Nat) : ConstStatePhasedProgram Unit :=
  loopUntilSink (binToUnaryLoopBodyFullScan w)
    ⟨w + 2, by rw [binToUnaryLoopBodyFullScan_numPhases]; omega⟩

@[simp] theorem binToUnaryLoopFullScan_numPhases (w : Nat) :
    (binToUnaryLoopFullScan w).numPhases = w + 30 := by
  simp [binToUnaryLoopFullScan]

@[simp] theorem binToUnaryLoopFullScan_startPhase_val (w : Nat) :
    ((binToUnaryLoopFullScan w).startPhase : Nat) = 0 := by
  simp [binToUnaryLoopFullScan, binToUnaryLoopBodyFullScan]

@[simp] theorem binToUnaryLoopFullScan_acceptPhase_val (w : Nat) :
    ((binToUnaryLoopFullScan w).acceptPhase : Nat) = w + 2 := rfl

end ContractExpansion
end Frontier
end Pnp4
