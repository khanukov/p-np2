import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanHstep
import Pnp4.Frontier.ContractExpansion.TreeMCSPCounterLowestBit

/-!
# `binToUnaryLoopFullScan` — `reachesSink` scaffolding (NP-verifier track — D2t-3 `ε`)

The final assembly of `ε`: the sound binary→unary loop reaches its sink (halts) on every valid input.
This module fixes the two reusable tools the assembly needs and the **loop layout invariant** it inducts
over; the bespoke termination proof itself is the documented follow-up.

`loopUntilSink_stepConfig_loop_tape` — the loop's back-edge (`B`'s accept → `B`'s start) **preserves the
tape** (the re-entry writes the scanned bit back). With `loopUntilSink_stepConfig_loop_{phase,head}` this
characterises the back-edge fully (phase → start, head/tape unchanged), so the per-iteration counter value
after re-entry equals the body pass's output.

`LoopLayout w c u` — the **U-LEFT layout invariant**: the loop is at the start phase with the head on the
sentinel `HOME`, `U = 1^u` occupies `[HOME-u, HOME)`, everything strictly left of `U` is blank, and the
**room invariant** `u + counterValue B ≤ HOME - 1` holds (so `U` can keep growing left as `B` shrinks).
One body pass (`binToUnaryLoopFullScan_runConfig_bodyPass`) maps `LoopLayout w c u` with `B > 0` to
`LoopLayout w c' (u+1)` with `counterValue B' = counterValue B - 1` (the borrow decrements `B`, the append
extends `U`; `u + counterValue` is preserved, so the room invariant survives). The standard library
combinator `loopUntilSink_reachesSink` cannot be applied directly — it quantifies its `hstep`/`hbase` over
*all* start-phase configs, but the run behaviour holds only on layouts — so termination is a **bespoke
strong induction on `counterValue B`** carrying `LoopLayout`, discharging the `B = 0` base from
`binToUnaryLoopFullScan_runConfig_hbase` and the `B > 0` step from `…_bodyPass` + the back-edge tools here.

This brick ships the tools + the invariant (everything below is `sorry`-free and axiom-clean); the
termination induction and the `ζ` correctness bridge (`|U| = value B`) are the remaining follow-ups.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- **Back-edge tape preservation.**  A step from `B`'s accept phase (the `loopUntilSink` re-entry) leaves
the tape unchanged — it writes the scanned bit back.  Completes the back-edge characterisation alongside
`loopUntilSink_stepConfig_loop_{phase,head}`. -/
theorem loopUntilSink_stepConfig_loop_tape (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    {L : Nat} (c : Configuration (M := (loopUntilSink B sink).toPhased.toTM) L) {s : Unit}
    (hstate : c.state = ⟨B.acceptPhase, s⟩) :
    (TM.stepConfig (M := (loopUntilSink B sink).toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (loopUntilSink B sink) c hstate]
  have hbit : ((loopUntilSink B sink).transition B.acceptPhase s (c.tape c.head)).2.2.1
      = c.tape c.head := by rw [loopUntilSink_transition_loop]
  rw [hbit]; funext j; by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- **The loop layout invariant.**  At the loop start phase `0` with the head on the sentinel `HOME`,
`U = 1^u` occupying `[HOME-u, HOME)` (`u ≥ 1`, the permanent endmarker seed is the rightmost `U` cell),
everything strictly left of `U` blank, the width-`w` counter window fitting, and the **room invariant**
`u + counterValue B ≤ HOME - 1` (so `U` keeps room to grow as `B` shrinks).  One body pass maps this to the
same invariant with `u ↦ u+1` and `counterValue B ↦ counterValue B - 1`. -/
def LoopLayout (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (u : Nat) : Prop :=
  (c.state.fst : Nat) = 0
  ∧ 1 ≤ u
  ∧ 1 ≤ (c.head : Nat)
  ∧ (c.head : Nat) + 3 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L
  ∧ c.tape c.head = false
  ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c.head : Nat) - u ≤ (q : Nat) → (q : Nat) < (c.head : Nat) → c.tape q = true)
  ∧ (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) < (c.head : Nat) - u → c.tape q = false)
  ∧ u + counterValue c ((c.head : Nat) + 1) w ≤ (c.head : Nat) - 1

end ContractExpansion
end Frontier
end Pnp4
