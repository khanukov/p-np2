import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoop
import Pnp4.Frontier.ContractExpansion.TreeMCSPSeekHomeAfterRoute

/-!
# `binToUnaryLoopRehome` — the binary→unary loop with the seek-HOME bridge (NP-verifier track — D2t-3 `ε`)

The merged `binToUnaryLoop = loopUntilSink (seq binToUnaryRouteBody binToUnaryBody) ⟨4⟩` (the route-only
loop, #1559) cannot discharge `hstep`: on `B > 0` the route exits at the discriminator, `j + 2` cells
right of the sentinel, but `binToUnaryBody` needs the head **on** the sentinel (see the `decide_false`
navigation analysis, #1563 / `TM_VERIFIER_STRATEGY.md` §12).  The resolution (literature-grounded: a
binary-alphabet *endmarker* realized as a permanent seed-`U` cell, #1571) is the **`seekHomeAfterRoute`**
primitive, now proven end-to-end (`seekHomeAfterRoute_runConfig_home`).

This module assembles the **revised** loop that inserts that re-homing between the route and the body:

* `binToUnaryLoopBodyRehome := seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)` — route first;
  on `B > 0` (route accept, phase `5`) hand off into `seekHomeAfterRoute` (re-home to the sentinel), then
  one pass of `binToUnaryBody`;
* `binToUnaryLoopRehome := loopUntilSink binToUnaryLoopBodyRehome ⟨4⟩` — re-enter the body on its accept and halt at
  the sink phase `4` (`B = 0`).

It is introduced **additively** (the route-only `binToUnaryLoop` and its merged `hbase`/`decide_false`
stay intact) so nothing breaks; the route region (phases `0..5`) and sink `⟨4⟩` are unchanged, so the
`B = 0` and `B > 0` route decisions re-derive on this machine exactly as before, and `hstep` becomes
provable (route → seek-HOME → body one-pass → loop back-edge).  This brick ships the **definitions +
phase-count facts**; the run behaviour (`hbase`/`decide_false`/`hstep` on `binToUnaryLoopRehome`, then `ζ`) is
the follow-up.

**Progress classification (AGENTS.md): Infrastructure** — the loop assembly toward the NP-membership leg;
it proves no run behaviour here.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The revised loop body: route, then on `B > 0` re-home (`seekHomeAfterRoute`) and run one pass of
`binToUnaryBody`. -/
def binToUnaryLoopBodyRehome : ConstStatePhasedProgram Unit :=
  seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)

/-- Phase count: route `6` + (`seekHomeAfterRoute` `9` + `binToUnaryBody` `15`) `= 30`. -/
@[simp] theorem binToUnaryLoopBodyRehome_numPhases : binToUnaryLoopBodyRehome.numPhases = 30 := rfl

/-- The seek-HOME loop: re-enter the body on its accept (a completed `B > 0` pass), halt at the sink phase
`4` (`B = 0`). -/
def binToUnaryLoopRehome : ConstStatePhasedProgram Unit :=
  loopUntilSink binToUnaryLoopBodyRehome ⟨4, by decide⟩

@[simp] theorem binToUnaryLoopRehome_numPhases : binToUnaryLoopRehome.numPhases = 30 := rfl

@[simp] theorem binToUnaryLoopRehome_acceptPhase : (binToUnaryLoopRehome.acceptPhase : Nat) = 4 := rfl

/-- The route region of `binToUnaryLoopBodyRehome` is `binToUnaryRouteBody` (phases `0..5`), unchanged from the
route-only loop — so the `B = 0`/`B > 0` route decisions re-derive identically. -/
@[simp] theorem binToUnaryLoopBodyRehome_startPhase_val : (binToUnaryLoopBodyRehome.startPhase : Nat) = 0 := rfl

@[simp] theorem binToUnaryLoopRehome_startPhase_val : (binToUnaryLoopRehome.startPhase : Nat) = 0 := rfl

end ContractExpansion
end Frontier
end Pnp4
