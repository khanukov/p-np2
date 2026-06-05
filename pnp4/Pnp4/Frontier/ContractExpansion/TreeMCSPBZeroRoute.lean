import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightBranch
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# `bZeroRouteProgram` — the composed loop-exit routing program (NP-verifier track — D2t-3 routing)

The `bZeroTest` routing (`TM_VERIFIER_STRATEGY.md` §12) is *scan, then read the next cell and branch*:
`gammaSelfLoopScan` advances over `0`s and halts **on** the first `1` (the scan-stop), then the
discriminating read one cell further decides `B = 0` vs `B > 0` (`TreeMCSPBZeroTest.lean`,
`TreeMCSPStepRightBranch.lean`).  This module composes the two into a single program:

```
bZeroRouteProgram := seq gammaSelfLoopScan stepRightThenBranch
```

`seq` runs the scan (phases `0..1`), then on the scan's done phase performs the one free handoff step
into `stepRightThenBranch` (phases `2..5`): step right, read, branch.  The composed accept phase is the
`read = 1` branch target — i.e. **`B = 0` → accept/sink**; the other branch (phase `5`) is the
`B > 0` → body re-entry target.

This brick ships the **definition** and its **structural** lemmas (phase count, start/accept phase
indices, `neverMovesLeft` — so it composes further under `seqList`), following the toolkit's
structural-first discipline (`seq`, `loopUntilSink` shipped these before run-invariants).  The composed
**run-through** (`seq`'s `liftP1ToP2`/`embedSeqP2Config` lift: scan to the stop, handoff, then the two
branch steps — reaching accept iff `B = 0`) and the `loopUntilSink` `hbase`/`hstep` discharge are the
follow-up assembly.

**Progress classification (AGENTS.md): Infrastructure** — composed control program toward the
NP-membership leg; it builds no verifier and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The composed loop-exit routing program: scan over `0`s to the first `1` (`gammaSelfLoopScan`),
then step right, read, and branch (`stepRightThenBranch`).  See the module docstring. -/
def bZeroRouteProgram : ConstStatePhasedProgram Unit :=
  seq gammaSelfLoopScan stepRightThenBranch

@[simp] theorem bZeroRouteProgram_numPhases : bZeroRouteProgram.numPhases = 6 := rfl

/-- The composed routing program never moves its head left (lifts the two components'
`neverMovesLeft` through `seq`), so it composes further under `seqList`. -/
theorem bZeroRouteProgram_neverMovesLeft :
    TMNeverMovesLeft (bZeroRouteProgram.toPhased.toTM) :=
  seq_neverMovesLeft gammaSelfLoopScan stepRightThenBranch
    gammaSelfLoopScan_neverMovesLeft stepRightThenBranch_neverMovesLeft

end ContractExpansion
end Frontier
end Pnp4
