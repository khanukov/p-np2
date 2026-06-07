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

This brick ships the tools + the invariant (everything below is hole-free and axiom-clean); the
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

/-! ### The back-edge on the sound loop machine, directly (avoiding the expensive `loopUntilSink` defeq)

The generic `loopUntilSink_stepConfig_loop_*` lemmas can be applied to a `binToUnaryLoopFullScan` config
only through the `binToUnaryLoopFullScan ≡ loopUntilSink …` defeq, whose `whnf` blows up (it unfolds the
loop's transition, which contains `bZeroFullScan`'s `2^i`).  These FullScan-specific versions instead use
the cheap one-`delta` unfold at the *transition* level (`binToUnaryLoopFullScan_transition_backedge`) plus
the `binToUnaryLoopFullScan`-stated `toTM_stepConfig_*`, exactly the device of
`binToUnaryLoopFullScan_transition_body`. -/

/-- **Transition-level back-edge.**  At the loop body's accept phase `w + 29`, the loop jumps to the body's
start phase (writing the scanned bit back, head stay). -/
theorem binToUnaryLoopFullScan_transition_backedge (w : Nat)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} (hi : (i : Nat) = w + 29) (s : Unit) (b : Bool) :
    (binToUnaryLoopFullScan w).transition i s b
      = ((binToUnaryLoopBodyFullScan w).startPhase, (), b, Move.stay) := by
  have hacc : i = (binToUnaryLoopBodyFullScan w).acceptPhase :=
    Fin.ext (by rw [hi, binToUnaryLoopBodyFullScan_acceptPhase_val])
  rw [hacc]
  exact loopUntilSink_transition_loop (binToUnaryLoopBodyFullScan w)
    ⟨w + 2, by rw [binToUnaryLoopBodyFullScan_numPhases]; omega⟩ s b

/-- **Back-edge step, phase.**  From phase `w + 29` the loop re-enters at the start phase `0`. -/
theorem binToUnaryLoopFullScan_backedge_phase (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).state).fst.val = 0 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) cF hstate,
      binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  show ((binToUnaryLoopBodyFullScan w).startPhase : Nat) = 0
  exact binToUnaryLoopFullScan_startPhase_val w

/-- **Back-edge step, head.**  The re-entry leaves the head where the body finished (a `Move.stay`). -/
theorem binToUnaryLoopFullScan_backedge_head (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).head = cF.head := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) cF hstate]
  have hmove : ((binToUnaryLoopFullScan w).transition i s (cF.tape cF.head)).2.2.2 = Move.stay := by
    rw [binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  rw [hmove]; simp [Configuration.moveHead]

/-- **Back-edge step, tape.**  The re-entry writes the scanned bit back, leaving the tape unchanged. -/
theorem binToUnaryLoopFullScan_backedge_tape (w : Nat) {L : Nat}
    (cF : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 29) (hstate : cF.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) cF).tape = cF.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) cF hstate]
  have hbit : ((binToUnaryLoopFullScan w).transition i s (cF.tape cF.head)).2.2.1 = cF.tape cF.head := by
    rw [binToUnaryLoopFullScan_transition_backedge w hi s (cF.tape cF.head)]
  rw [hbit]; funext j; by_cases hj : j = cF.head
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
