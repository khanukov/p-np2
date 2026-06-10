import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoop

/-!
# `binToUnaryLoop` route-region transition peel (shared helper — NP-verifier track, D2t-3 `ε`)

The loop machine `binToUnaryLoop = loopUntilSink binToUnaryLoopBody ⟨4⟩` evaluates, in its **route region**
(phases `0..3`, none equal to the loop body's accept `20` or the sink `4`), to `binToUnaryLoopBody`'s own
transition: `loopUntilSink` runs the body verbatim there.  `binToUnaryLoop_transition_route` peels that
`loopUntilSink` layer (whose guards are *Fin* equalities — refuted via the accept index `20` and `i < 4`),
leaving the two `seq` layers for `simp` at the call site.

This is the single shared peel used by every loop-machine run-through brick (`hbase`'s `B=0 → sink`,
`decide_false`'s `B>0 → phase 5`, and the forthcoming `hstep` navigation), so the peel logic lives in one
place rather than being copied per module.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The loop body's accept phase (the `idleCS` of `binToUnaryBody`, embedded past the `6`-phase route) is
`20` — distinct from the route region (`0..5`) and the sink (`4`). -/
private theorem binToUnaryLoopBody_acceptPhase_val :
    (binToUnaryLoopBody.acceptPhase : Nat) = 20 := by decide

/-- In the route region (`i < 4`) the loop's transition is the body's transition: the head is neither at
the loop body's accept phase (`20`) nor at the sink (`4`), so `loopUntilSink` runs `binToUnaryLoopBody`
verbatim.  This peels the `loopUntilSink` layer (whose guards are *Fin* equalities), leaving the `seq`
layers for `simp`. -/
theorem binToUnaryLoop_transition_route {i : Fin binToUnaryLoop.numPhases} (hlt : (i : Nat) < 4)
    (s : Unit) (b : Bool) :
    binToUnaryLoop.transition i s b = binToUnaryLoopBody.transition i () b :=
  loopUntilSink_transition_body binToUnaryLoopBody ⟨4, by decide⟩
    (Fin.ne_of_val_ne (by rw [binToUnaryLoopBody_acceptPhase_val]; omega))
    (Fin.ne_of_val_ne (show (i : Nat) ≠ 4 by omega)) s b

end ContractExpansion
end Frontier
end Pnp4
