import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeHbase
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeRoutePeel

/-!
# `binToUnaryLoopRehome` — the `B > 0` route decision reaches the body-handoff phase (NP-verifier track — D2t-3 `ε`)

The companion to `TreeMCSPBinToUnaryLoopRehomeHbase.lean` (which handles `B = 0 → sink phase 4`): here the
routing decision, lifted into the loop machine, takes the **`B > 0`** branch — discriminator cell `0`
instead of `1` — and lands in **phase 5**, `binToUnaryRouteBody`'s accept (the `B > 0` target).  The
scanning → terminator → handoff → step1 prefix is **identical** to `hbase` (phases `0 → 1 → 2 → 3`), so
this module *reuses* the merged `binToUnaryLoopRehome_runConfig_step1`; only the last step differs
(`binToUnaryLoopRehome_stepConfig_branch0`: phase `3` reading `0` → phase `5`).

This is the route-decision half of `loopUntilSink_reachesSink`'s `hstep` and is valid regardless of how
the body re-entry is wired.

## The `B > 0` `hstep` path (this machine resolves the navigation gap)

On `binToUnaryLoopRehome`, `binToUnaryLoopBodyRehome = seq binToUnaryRouteBody (seq seekHomeAfterRoute
binToUnaryBody)`, so phase `5` (route accept) hands off to phase `6` = **`seekHomeAfterRoute`'s start**
— *not* directly to the body.  `seekHomeAfterRoute` re-homes the head from the discriminator
(`head₀ + z + 1`, `j + 2` cells right of the sentinel) back **onto the sentinel** (proven end-to-end in
`seekHomeAfterRoute_runConfig_home`), after which `binToUnaryBody_runConfig_onePass` runs from HOME.  So
`decide_false` (reaching phase `5`) is the **first leg** of `hstep`; the remaining legs (seek-HOME lift →
body one-pass → loop back-edge with `counterValue` strictly decreasing) compose on this machine — the
route-only loop's navigation gap (route exits at the discriminator, the body needs the sentinel) is
exactly what the inserted `seekHomeAfterRoute` bridges.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Branch read-`0`** (phase `3`, reading `0`): jump to phase `5` — `binToUnaryRouteBody`'s accept, the
`B > 0` body-handoff target.  (The route-region transition peel `binToUnaryLoopRehome_transition_route` is
shared from `TreeMCSPBinToUnaryLoopRehomeRoutePeel.lean`.) -/
theorem binToUnaryLoopRehome_stepConfig_branch0 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 5 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
    binToUnaryLoopRehome_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
  simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
    stepRightThenBranch, hi]

/-- **`decide_false` headline.**  From a HOME config at the loop's start phase with the `B > 0` layout —
cells `[c0.head, c0.head + z)` all `0`, scan-stop marker `1` at `c0.head + z`, and discriminator **`0`**
at `c0.head + z + 1` — the loop reaches phase `5` (the `B > 0` route accept / body-handoff point) after
`z + 4` steps.  Reuses the merged `binToUnaryLoopRehome_runConfig_step1` (shared with `hbase`). -/
theorem binToUnaryLoopRehome_runConfig_decide_false {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz1 : (c0.head : Nat) + z + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true)
    (hdisc0 : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z + 1 → c0.tape p = false) :
    (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoopRehome_runConfig_step1 c0 hstart z hz1 hzeros hterm
  have hbit : (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1)).head = false := by
    rw [htp]; exact hdisc0 _ hhd
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1) with hc
  clear_value c
  exact binToUnaryLoopRehome_stepConfig_branch0 c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbit

/-- `initialConfig` places the loop machine's head at cell `0`. -/
private theorem binToUnaryLoopRehome_initialConfig_head_val {L : Nat} (x : Boolcube.Point L) :
    ((binToUnaryLoopRehome.toPhased.toTM.initialConfig x).head : Nat) = 0 := rfl

/-- The `B > 0` route decision is realizable: a concrete **single-marker** input (cell `z` set, all else
`0`, so the discriminator `z + 1` is `0`) drives `binToUnaryLoopRehome` from `initialConfig` to phase `5` after
`z + 4` steps — the `B > 0` analogue of `binToUnaryLoopRehome_hbase_realizable`. -/
theorem binToUnaryLoopRehome_decide_false_realizable {L : Nat} (z : Nat) (hzL : z + 1 < L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM)
          (binToUnaryLoopRehome.toPhased.toTM.initialConfig x) (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  refine ⟨fun j => decide ((j : Nat) = z), ?_⟩
  apply binToUnaryLoopRehome_runConfig_decide_false _ rfl z
  · rw [binToUnaryLoopRehome_initialConfig_head_val]; simp only [TM.tapeLength]; omega
  · intro p hp1 hp2
    rw [binToUnaryLoopRehome_initialConfig_head_val] at hp2
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    rw [binToUnaryLoopRehome_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    rw [binToUnaryLoopRehome_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega

end ContractExpansion
end Frontier
end Pnp4
