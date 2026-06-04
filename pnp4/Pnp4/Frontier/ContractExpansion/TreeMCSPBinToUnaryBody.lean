import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryAppendLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPCounterComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# The binary→unary loop body `binToUnaryBody` (NP-verifier track — D2 transcoder, D2t-3c-γ)

`binToUnaryBody` is the flattened, atomic 7-element `seqList` that performs **one pass** of the
binary→unary conversion loop (`TM_VERIFIER_STRATEGY.md` §12 D2t-3c-γ).  Working on the U-left layout

```
[ … blank | U = 1^|U| | sentinel(0) | B = b_0 b_1 … b_{w-1} | rightMarker(1) | … ]
                         ^HOME
```

one pass — from HOME with `B > 0` — decrements the binary counter `B` by one and appends one `1` to the
unary output `U`, returning the head to HOME.  The seven steps are:

1. `stepRightOnce`        — move from the sentinel onto `B`'s low cell `b_0`;
2. `selfLoopDecrement`    — borrow-decrement `B` (stops on the lowest set bit `j`);
3. `stepLeftOnce`         — step left off the just-cleared `0`-cell;
4. `selfLoopScanLeftOne`  — scan left over the flipped `1`-run back to the sentinel (HOME);
5. `stepLeftOnce`         — step left off the sentinel onto `U`'s right end;
6. `selfLoopAppendLeftOne`— scan left over `U`'s `1`s and append one `1` at its left `0`-end;
7. `selfLoopScanRightOne` — scan right over `U`'s `1`s back to the sentinel (HOME).

This module fixes the **definition** and its structural facts (`numPhases`, `timeBound`).  The seven
per-element run-behaviour segment lemmas (the depth-1…depth-7 `_seqNested…_` re-derivations) are already
proven in the element modules; the one-pass run-behaviour composition (via `seqList_run_seven`) is the
next brick.  This builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
-/

/-- One pass of the binary→unary conversion loop body, as a flattened atomic 7-element `seqList`
(§12 D2t-3c-γ).  Right-nested, so element `k` sits at chain-depth `k`. -/
def binToUnaryBody : ConstStatePhasedProgram Unit :=
  seqList [stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
    selfLoopAppendLeftOne, selfLoopScanRightOne]

/-- `binToUnaryBody` is `seq stepRightOnce (seq selfLoopDecrement R)` where `R` is the trailing
five-element `seqList` — the shape the decrement's depth-2 `_seqNested_` lemma consumes. -/
theorem binToUnaryBody_eq_seq :
    binToUnaryBody
      = seq stepRightOnce (seq selfLoopDecrement
          (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
            selfLoopScanRightOne])) := rfl

/-- The loop body has `15` phases (seven 2-phase programs plus the trailing `idleCS`). -/
@[simp] theorem binToUnaryBody_numPhases : binToUnaryBody.numPhases = 15 := rfl

/-- The loop body's start phase is `0`. -/
@[simp] theorem binToUnaryBody_startPhase_val : (binToUnaryBody.startPhase : Nat) = 0 := rfl

/-- Closed-form `timeBound`: `4·n + 10` (`stepRight 1 + decrement n + stepLeft 1 + scanLeft n +
stepLeft 1 + append n + scanRight n`, plus the seven `seqList` handoff steps).  Computed via
`seqList_timeBound_seven`; the polynomial bound the eventual `runTime_poly` accounting consumes. -/
@[simp] theorem binToUnaryBody_timeBound (n : Nat) : binToUnaryBody.timeBound n = 4 * n + 10 := by
  unfold binToUnaryBody
  rw [seqList_timeBound_seven]
  simp only [stepRightOnce_timeBound, selfLoopDecrement_timeBound, stepLeftOnce_timeBound,
    selfLoopScanLeftOne_timeBound, selfLoopAppendLeftOne_timeBound, selfLoopScanRightOne_timeBound]
  omega

/-! ### Next: the one-pass run composition

The seven per-element segment lemmas (`stepRightOnce` as the outermost P1 via `seq_stepConfig_P1_*`,
then `selfLoopDecrement_seqNested_*`, `stepLeftOnce_seqNested2_*`, `selfLoopScanLeftOne_seqNested3_*`,
`stepLeftOnce_seqNested4_*`, `selfLoopAppendLeftOne_seqNested5_*`, `selfLoopScanRightOne_seqNested6_*`)
compose — via `seqList_run_seven` for the time skeleton and `TM.runConfig_add` at each element boundary
— into the one-pass HOME→HOME run behaviour (`counterValue B − 1`, `|U| + 1`, head back at HOME) on the
U-left layout.  That composition is the next brick; this module fixes the definition and the structural
facts it consumes. -/

end ContractExpansion
end Frontier
end Pnp4
