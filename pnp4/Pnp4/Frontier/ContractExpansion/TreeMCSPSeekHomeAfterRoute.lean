import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Home-seek after the routing decision (NP-verifier track — D2 transcoder, D2t-3 `ε`, scaffolding)

The binary→unary loop's routing decision (`bZeroRouteProgram`, §12 `ε`) scans **right** over the counter
`B` and, on `B > 0`, rests at the **discriminator** cell — index `s + (j + 2)` where `s` is the HOME
sentinel and `B = 0^j 1` (`j` low zeros then the terminator `1`).  To run another body pass the head must
return to `s`, but `s` is a `0` indistinguishable from `B`'s interior zeros: the only left-landmark is the
unary output `U`'s `1`s.

This is the classic Turing-machine *return-to-home without an endmarker symbol* problem (Hopcroft–Ullman
"marking"/checking-off technique; the standard fix is a reserved boundary symbol — forbidden here by the
binary-alphabet, all-`Unit`-state discipline, `TM_VERIFIER_STRATEGY.md` §6f).  The binary-alphabet
realization is a **permanent unary sentinel**: keep `U` non-empty (seed one `1`), so the left scan always
terminates on `U`'s `1`.  Under that invariant the home-seek is the deterministic **four-sub-program**
composite (four sub-programs, *not* four TM steps — see the step-count note below)

  `seekHomeAfterRoute := seqList [stepLeftOnce, stepLeftOnce, selfLoopScanLeft, stepRightOnce]`

reading, from the discriminator: step left off the discriminator (onto the terminator `1`), step left
into `B`'s `0`-block, **scan left over the contiguous `0`s** (`B`'s `j` zeros and the sentinel) until the
first `1` (`U`'s rightmost cell at `s − 1`), then **step right** back onto the sentinel `s`.  Net head
move `−(j + 2)`, tape unchanged; the `j = 0` edge (no interior zeros) is absorbed by the scan's
zero-length-admitting invariant.

**Step count.**  `seqList` folds into nested `seq` over a trailing `idleCS`, so the program has `9` phases
(4 × 2-phase bricks + the `idleCS`) and its `timeBound` includes the per-`seq` handoff steps plus the
*variable* `selfLoopScanLeft` cost — the executed run is `(j + 1) + 3` head moves plus handoffs, not a
literal `4` TM steps.

This brick ships the **definition + phase-count facts**.  The run behaviour (reaching the sentinel from
the discriminator config), the `binToUnaryLoopBody` revision `seq route (seq seekHomeAfterRoute body)`,
and the `loopUntilSink_reachesSink` `hstep` it unblocks are the follow-ups.

**Progress classification (AGENTS.md): Infrastructure** — loop-navigation assembly toward the
NP-membership leg; no run behaviour and no separation here.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

/-- Home-seek after the routing decision: from the discriminator, return the head to the HOME sentinel by
stepping past the discriminator and terminator, scanning left over `B`'s `0`-block, and stepping right
onto the sentinel.  Relies on the seed-`U` invariant (`U` non-empty) so the left scan stops on `U`'s `1`. -/
def seekHomeAfterRoute : ConstStatePhasedProgram Unit :=
  seqList [stepLeftOnce, stepLeftOnce, selfLoopScanLeft, stepRightOnce]

/-- The composite has `9` phases (four 2-phase programs plus the trailing `idleCS`). -/
@[simp] theorem seekHomeAfterRoute_numPhases : seekHomeAfterRoute.numPhases = 9 := rfl

/-- The home-seek's start phase is `0`. -/
@[simp] theorem seekHomeAfterRoute_startPhase_val : (seekHomeAfterRoute.startPhase : Nat) = 0 := rfl

/-- The home-seek's accept phase is the trailing `idleCS` at `8`. -/
@[simp] theorem seekHomeAfterRoute_acceptPhase_val : (seekHomeAfterRoute.acceptPhase : Nat) = 8 := rfl

end ContractExpansion
end Frontier
end Pnp4
