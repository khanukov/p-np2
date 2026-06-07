import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScan

/-!
# `binToUnaryLoopFullScan` — loop-machine peel + accept-phase (NP-verifier track — D2t-3 `ε`)

Foundational lemmas for running `binToUnaryLoopFullScan` (`TreeMCSPBinToUnaryLoopFullScan.lean`): the
accept-phase index of its loop body and the body-region peel of `loopUntilSink` (away from the body
accept `w + 29` and the sink `w + 2`, the loop runs the body verbatim).  Mirrors
`binToUnaryLoopBodyRehome_acceptPhase_val` / `binToUnaryLoopRehome_transition_body`, with the
`w`-parameterised indices.

**Progress classification (AGENTS.md): Infrastructure** — standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The loop body's accept phase: `stepRightOnce (2) + bZeroFullScanRouteBody (w+2) + stepRightOnce (2) +
seekHomeAfterRoute (9) + binToUnaryBody's accept (14) = w + 29`. -/
@[simp] theorem binToUnaryLoopBodyFullScan_acceptPhase_val (w : Nat) :
    ((binToUnaryLoopBodyFullScan w).acceptPhase : Nat) = w + 29 := by
  have hbody : (binToUnaryBody.acceptPhase : Nat) = 14 := by decide
  simp only [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody_numPhases,
    stepRightOnce_numPhases, seekHomeAfterRoute_numPhases, hbody]
  omega

/-- **Body-region peel.**  Away from the loop body's accept `w + 29` and the sink `w + 2`,
`binToUnaryLoopFullScan` runs `binToUnaryLoopBodyFullScan` verbatim. -/
theorem binToUnaryLoopFullScan_transition_body (w : Nat)
    {i : Fin (binToUnaryLoopFullScan w).numPhases}
    (hneA : (i : Nat) ≠ w + 29) (hneS : (i : Nat) ≠ w + 2) (s : Unit) (b : Bool) :
    (binToUnaryLoopFullScan w).transition i s b = (binToUnaryLoopBodyFullScan w).transition i () b := by
  have h := loopUntilSink_transition_body (binToUnaryLoopBodyFullScan w)
    ⟨w + 2, by rw [binToUnaryLoopBodyFullScan_numPhases]; omega⟩
    (Fin.ne_of_val_ne (by rw [binToUnaryLoopBodyFullScan_acceptPhase_val]; exact hneA))
    (Fin.ne_of_val_ne hneS) s b
  exact h

end ContractExpansion
end Frontier
end Pnp4
