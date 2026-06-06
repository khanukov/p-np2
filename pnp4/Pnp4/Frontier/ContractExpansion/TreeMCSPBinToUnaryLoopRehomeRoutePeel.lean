import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehome

/-!
# `binToUnaryLoopRehome` route-region transition peel (NP-verifier track — D2t-3 `ε`)

The seek-HOME loop `binToUnaryLoopRehome = loopUntilSink binToUnaryLoopBodyRehome ⟨4⟩` evaluates, in its
**route region** (phases `0..3`, none equal to the loop body's accept `29` or the sink `4`), to
`binToUnaryLoopBodyRehome`'s own transition — and since `binToUnaryRouteBody` is the outer `seq`'s P1 in
*both* the route-only `binToUnaryLoopBody` and the rehome `binToUnaryLoopBodyRehome`, that route region is
**identical** to the route-only loop's.  So the `B = 0`/`B > 0` route decisions re-derive on this machine
exactly as the merged `hbase`/`decide_false` did, modulo this peel (whose only difference from
`binToUnaryLoop_transition_route` is the loop body's accept index, `29` here vs `20` there).

This is the foundation for the `binToUnaryLoopRehome` run-through (`hbase`/`decide_false`, then `hstep`).

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The rehome loop body's accept phase: route `6` + seek-HOME `9` + `binToUnaryBody`'s `idleCS` accept
`14` `= 29` — well past the peel's route region (`i < 4`) and the sink (`4`), so neither equals it. -/
private theorem binToUnaryLoopBodyRehome_acceptPhase_val :
    (binToUnaryLoopBodyRehome.acceptPhase : Nat) = 29 := by decide

/-- In the route region (`i < 4`) the rehome loop's transition is the body's transition (head at neither
the loop body's accept `29` nor the sink `4`), so `loopUntilSink` runs `binToUnaryLoopBodyRehome`
verbatim — peeling the `loopUntilSink` layer and leaving the `seq` layers for `simp`. -/
theorem binToUnaryLoopRehome_transition_route {i : Fin binToUnaryLoopRehome.numPhases}
    (hlt : (i : Nat) < 4) (s : Unit) (b : Bool) :
    binToUnaryLoopRehome.transition i s b = binToUnaryLoopBodyRehome.transition i () b :=
  loopUntilSink_transition_body binToUnaryLoopBodyRehome ⟨4, by decide⟩
    (Fin.ne_of_val_ne (by rw [binToUnaryLoopBodyRehome_acceptPhase_val]; omega))
    (Fin.ne_of_val_ne (show (i : Nat) ≠ 4 by omega)) s b

end ContractExpansion
end Frontier
end Pnp4
