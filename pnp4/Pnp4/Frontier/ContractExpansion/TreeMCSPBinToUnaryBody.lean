import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryAppendLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# The binary→unary loop body (NP-verifier track — D2 transcoder, D2t-3c-γ)

`binToUnaryBody` is one pass of the binary→unary conversion loop (`TM_VERIFIER_STRATEGY.md` §12,
D2t-3c-γ): starting at **HOME** (the `0`-sentinel just left of the little-endian binary counter `B`,
with the unary output `U` to its left) and assuming `B > 0`, it

1. `stepRightOnce` — steps off the sentinel onto `B`'s low cell;
2. `selfLoopDecrement` — decrements `B` (borrow ripple; head ends on the cleared lowest set bit);
3. `stepLeftOnce ; selfLoopScanLeftOne` — the **home-seek**: one left step onto the flipped `1`-block,
   then a leftward scan-over-`1`s back to the sentinel;
4. `stepLeftOnce` — steps off the sentinel onto `U`'s block;
5. `selfLoopAppendLeftOne` — grows `U` by one `1` on its left end;
6. `selfLoopScanRightOne` — scans back right over `U` to HOME (the sentinel).

## Left-nested composition (the key design choice)

`seq` does **not** reassociate, so a primitive at chain-depth `d` of a *right*-nested `seqList`
`seq p₁ (seq p₂ …)` is reached only through `d−1` nested `seq_stepConfig_P2_*` unfolds — forcing a
distinct `seqNested`-at-depth-`d` re-derivation per element.  Building the chain **left**-nested instead,
`seq (seq (… (seq p₁ p₂) …) p₆) p₇`, makes every element `pᵢ` (`i ≥ 2`) the **depth-1 `P2`** of
`seq ⟨prefixᵢ₋₁⟩ pᵢ`, so each is characterised by its already-merged `…_seqP2_*` lemma with
`P1 := prefixᵢ₋₁` (an arbitrary prefix; only its `numPhases` matters).  No deeper nesting is needed; the
one-pass run behaviour is then an inductive thread over the six handoffs.

This module ships the definition and its structural facts (`numPhases`/`startPhase`/`acceptPhase`); the
one-pass `runConfig` behaviour (`counterValue B − 1`, `|U| + 1`, head back at HOME) is the follow-up.
Builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
-/

/-- One pass of the binary→unary loop body, **left-nested** so every element is a depth-1 `seqP2`
phase (see the module docstring).  Order: step onto `B`, decrement, seek home (step left + scan left),
step onto `U`, append one `1`, scan right back to HOME. -/
def binToUnaryBody : ConstStatePhasedProgram Unit :=
  seq (seq (seq (seq (seq (seq stepRightOnce selfLoopDecrement)
    stepLeftOnce) selfLoopScanLeftOne) stepLeftOnce) selfLoopAppendLeftOne) selfLoopScanRightOne

@[simp] theorem binToUnaryBody_numPhases : binToUnaryBody.numPhases = 14 := rfl

@[simp] theorem binToUnaryBody_startPhase_val : (binToUnaryBody.startPhase : Nat) = 0 := rfl

@[simp] theorem binToUnaryBody_acceptPhase_val : (binToUnaryBody.acceptPhase : Nat) = 13 := rfl

/-- The six prefixes' phase counts, recorded as defeq facts so the run-behaviour proof can address each
element's offset (`P1.numPhases` for its `seqP2` lift) without re-unfolding the whole chain.  Each is the
left-nested prefix ending just before the correspondingly-numbered element. -/
theorem binToUnaryBody_prefix1_numPhases :
    (seq stepRightOnce selfLoopDecrement).numPhases = 4 := rfl

theorem binToUnaryBody_prefix2_numPhases :
    (seq (seq stepRightOnce selfLoopDecrement) stepLeftOnce).numPhases = 6 := rfl

theorem binToUnaryBody_prefix3_numPhases :
    (seq (seq (seq stepRightOnce selfLoopDecrement) stepLeftOnce) selfLoopScanLeftOne).numPhases
      = 8 := rfl

theorem binToUnaryBody_prefix4_numPhases :
    (seq (seq (seq (seq stepRightOnce selfLoopDecrement) stepLeftOnce) selfLoopScanLeftOne)
      stepLeftOnce).numPhases = 10 := rfl

theorem binToUnaryBody_prefix5_numPhases :
    (seq (seq (seq (seq (seq stepRightOnce selfLoopDecrement) stepLeftOnce) selfLoopScanLeftOne)
      stepLeftOnce) selfLoopAppendLeftOne).numPhases = 12 := rfl

end ContractExpansion
end Frontier
end Pnp4
