import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeDecideFalse

/-!
# `binToUnaryLoopRehome` `decide_false` with head/tape tracking (NP-verifier track — D2t-3 `ε`)

The merged `binToUnaryLoopRehome_runConfig_decide_false` establishes the `B > 0` route decision reaches
**phase `5`** (the `seekHomeAfterRoute` handoff target) but tracks only the phase.  `hstep`'s assembly
needs the **head** there too — it is the discriminator cell `c0.head + z + 1` — and that the tape is
unchanged (the route is read-only), so the seek-HOME leg can start from a known head position.

This module adds the head/tape conjuncts: the branch step (phase `3`, reading the discriminator `0`) is a
`Move.stay` writing the scanned bit back, so it leaves head and tape fixed; composing with the merged
`binToUnaryLoopRehome_runConfig_step1` (which lands the head on the discriminator) gives the full
behaviour.  Depends only on merged lemmas.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Branch read-`0` (full).**  At phase `3` reading the discriminator `0`, the loop jumps to phase `5`
(the `B > 0` body-handoff target), leaving the head and tape unchanged (the decision is a `Move.stay`
write-back).  Extends the merged `binToUnaryLoopRehome_stepConfig_branch0` (phase only) with the head/tape
conjuncts. -/
theorem binToUnaryLoopRehome_stepConfig_branch0_full {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 5
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨binToUnaryLoopRehome_stepConfig_branch0 c hi hstate hbit, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **`decide_false` headline with head/tape.**  From a HOME config at the loop's start phase with the
`B > 0` layout — cells `[c0.head, c0.head + z)` all `0`, scan-stop marker `1` at `c0.head + z`,
discriminator `0` at `c0.head + z + 1` — the loop reaches phase `5` after `z + 4` steps with the head on
the **discriminator** `c0.head + z + 1` and the tape unchanged.  The starting point for the seek-HOME leg
of `hstep`. -/
theorem binToUnaryLoopRehome_runConfig_decide_false_head {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz1 : (c0.head : Nat) + z + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true)
    (hdisc0 : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z + 1 → c0.tape p = false) :
    (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5
      ∧ ((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).head : Nat)
          = (c0.head : Nat) + z + 1
      ∧ (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoopRehome_runConfig_step1 c0 hstart z hz1 hzeros hterm
  have hbit : (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1)).head = false := by
    rw [htp]; exact hdisc0 _ hhd
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (z + 1 + 1 + 1) with hc
  clear_value c
  obtain ⟨bp, bh, bt⟩ := binToUnaryLoopRehome_stepConfig_branch0_full c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  exact ⟨bp, by rw [bh, hhd], by rw [bt, htp]⟩

end ContractExpansion
end Frontier
end Pnp4
