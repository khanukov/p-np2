import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopHbase
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRoutePeel

/-!
# `binToUnaryLoop` — the `B > 0` route decision reaches the body-handoff phase (NP-verifier track — D2t-3 `ε`)

The companion to `TreeMCSPBinToUnaryLoopHbase.lean` (which handles `B = 0 → sink phase 4`): here the
routing decision, lifted into the loop machine, takes the **`B > 0`** branch — discriminator cell `0`
instead of `1` — and lands in **phase 5**, `binToUnaryRouteBody`'s accept (the `B > 0` target).  The
scanning → terminator → handoff → step1 prefix is **identical** to `hbase` (phases `0 → 1 → 2 → 3`), so
this module *reuses* the merged `binToUnaryLoop_runConfig_step1`; only the last step differs
(`binToUnaryLoop_stepConfig_branch0`: phase `3` reading `0` → phase `5`).

This is the route-decision half of `loopUntilSink_reachesSink`'s `hstep` and is valid regardless of how
the body re-entry is wired.

## Navigation gap (the `hstep` blocker — recorded for the follow-up)

Reaching phase `5` is **not** sufficient for `hstep`.  Under `binToUnaryLoopBody = seq binToUnaryRouteBody
binToUnaryBody`, phase `5` (route accept) hands off to phase `6` = `binToUnaryBody`'s start — but the head
is at the **discriminator** (`head₀ + z + 1`, where `z = j + 1` is the scan distance over the sentinel and
`B`'s `0^j`), i.e. `j + 2` cells **right** of the sentinel.  `binToUnaryBody_runConfig_onePass` requires
the head **on the sentinel** (`tape head = false`, `0 < head`) with `U = 1^u` immediately left and
`B = 0^j 1` immediately right.  So the as-merged `seq(route, body)` lacks a **seek-HOME bridge**: `hstep`
needs `binToUnaryLoopBody` revised to `seq binToUnaryRouteBody (seq seekHome binToUnaryBody)` with a new
`seekHome` primitive (scan left past the discriminator/terminator and `B`'s zeros to the sentinel — the
first `0` whose left neighbour is `U`'s `1`).  That primitive + the revised `hstep` run-through (route →
seek-HOME → body one-pass → loop back-edge, with `counterValue` strictly decreasing) is the next brick.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Branch read-`0`** (phase `3`, reading `0`): jump to phase `5` — `binToUnaryRouteBody`'s accept, the
`B > 0` body-handoff target.  (The route-region transition peel `binToUnaryLoop_transition_route` is
shared from `TreeMCSPBinToUnaryLoopRoutePeel.lean`.) -/
theorem binToUnaryLoop_stepConfig_branch0 {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 5 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
    binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
  simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
    stepRightThenBranch, hi]

/-- **`decide_false` headline.**  From a HOME config at the loop's start phase with the `B > 0` layout —
cells `[c0.head, c0.head + z)` all `0`, scan-stop marker `1` at `c0.head + z`, and discriminator **`0`**
at `c0.head + z + 1` — the loop reaches phase `5` (the `B > 0` route accept / body-handoff point) after
`z + 4` steps.  Reuses the merged `binToUnaryLoop_runConfig_step1` (shared with `hbase`). -/
theorem binToUnaryLoop_runConfig_decide_false {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz1 : (c0.head : Nat) + z + 1 < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true)
    (hdisc0 : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z + 1 → c0.tape p = false) :
    (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoop_runConfig_step1 c0 hstart z hz1 hzeros hterm
  have hbit : (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).head = false := by
    rw [htp]; exact hdisc0 _ hhd
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1) with hc
  clear_value c
  exact binToUnaryLoop_stepConfig_branch0 c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbit

/-- `initialConfig` places the loop machine's head at cell `0`. -/
private theorem binToUnaryLoop_initialConfig_head_val {L : Nat} (x : Boolcube.Point L) :
    ((binToUnaryLoop.toPhased.toTM.initialConfig x).head : Nat) = 0 := rfl

/-- The `B > 0` route decision is realizable: a concrete **single-marker** input (cell `z` set, all else
`0`, so the discriminator `z + 1` is `0`) drives `binToUnaryLoop` from `initialConfig` to phase `5` after
`z + 4` steps — the `B > 0` analogue of `binToUnaryLoop_hbase_realizable`. -/
theorem binToUnaryLoop_decide_false_realizable {L : Nat} (z : Nat) (hzL : z + 1 < L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM)
          (binToUnaryLoop.toPhased.toTM.initialConfig x) (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  refine ⟨fun j => decide ((j : Nat) = z), ?_⟩
  apply binToUnaryLoop_runConfig_decide_false _ rfl z
  · rw [binToUnaryLoop_initialConfig_head_val]; simp only [TM.tapeLength]; omega
  · intro p hp1 hp2
    rw [binToUnaryLoop_initialConfig_head_val] at hp2
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    rw [binToUnaryLoop_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    rw [binToUnaryLoop_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega

end ContractExpansion
end Frontier
end Pnp4
