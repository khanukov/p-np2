import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeRoutePeel

/-!
# `binToUnaryLoopRehome` `hstep` — the `B > 0` re-entry pass (NP-verifier track — D2t-3 `ε`)

`loopUntilSink_reachesSink`'s `hstep` for `binToUnaryLoopRehome`: from a `B > 0` HOME config at phase `0`,
one loop pass returns to phase `0` with `counterValue` strictly decreased.  The pass chains, on
`binToUnaryLoopRehome = loopUntilSink (seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)) ⟨4⟩`:

  `decide_false` (phase `0 → 5`) → **handoff (`5 → 6`)** → `seekHomeAfterRoute` lift (`6 → 14`, re-home) →
  **handoff (`14 → 15`)** → `binToUnaryBody` lift (`15 → 29`, one pass) → `loopUntilSink` back-edge (`29 → 0`).

This module builds the **bounded `seq`-handoff / loop-back-edge single steps** first; the two run-through
*lifts* (`seekHomeAfterRoute` and `binToUnaryBody` re-derived at their phase offsets inside this loop
machine) and the `counterValue` measure are the substantial follow-ups.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The rehome loop body's accept phase is `29`; the sink is `4`. -/
private theorem accV : (binToUnaryLoopBodyRehome.acceptPhase : Nat) = 29 := by decide

/-- Away from the loop body's accept (`29`) and the sink (`4`), the loop's transition is the body's
transition (here for the route-accept phase `5`, outside the route region `i < 4`). -/
private theorem peel5 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    (s : Unit) (hi : i.val = 5) :
    binToUnaryLoopRehome.transition i s (c.tape c.head)
      = binToUnaryLoopBodyRehome.transition i () (c.tape c.head) :=
  loopUntilSink_transition_body binToUnaryLoopBodyRehome ⟨4, by decide⟩
    (Fin.ne_of_val_ne (by rw [accV]; omega)) (Fin.ne_of_val_ne (show (i : Nat) ≠ 4 by omega))
    s (c.tape c.head)

/-- **Handoff `5 → 6`** (route accept → `seekHomeAfterRoute` start): the outer `seq`'s P1-accept handoff.
Phase advances to `6`; head and tape unchanged. -/
theorem binToUnaryLoopRehome_stepConfig_handoff5 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 5) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 6
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate, peel5 c s hi]
    show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
        (c.tape c.head)).fst.val = 6
    rw [seq_transition_P1_accept_phase binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)]
    decide
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [peel5 c s hi]
      show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
          (c.tape c.head)).2.2.2 = Move.stay
      exact seq_transition_P1_accept_move binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbit : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [peel5 c s hi]
      show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
          (c.tape c.head)).2.2.1 = c.tape c.head
      exact seq_transition_P1_accept_bit binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)
    rw [hbit]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- Peel for phase `14` (the `seekHomeAfterRoute`-accept phase, `∉ {29, 4}`). -/
private theorem peel14 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    (s : Unit) (hi : i.val = 14) :
    binToUnaryLoopRehome.transition i s (c.tape c.head)
      = binToUnaryLoopBodyRehome.transition i () (c.tape c.head) :=
  loopUntilSink_transition_body binToUnaryLoopBodyRehome ⟨4, by decide⟩
    (Fin.ne_of_val_ne (by rw [accV]; omega)) (Fin.ne_of_val_ne (show (i : Nat) ≠ 4 by omega))
    s (c.tape c.head)

/-- **Handoff `14 → 15`** (`seekHomeAfterRoute` accept → `binToUnaryBody` start): the inner `seq`'s
P1-accept handoff, reached through the outer `seq`'s P2.  Phase advances to `15`; head and tape
unchanged. -/
theorem binToUnaryLoopRehome_stepConfig_handoff14 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 14) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 15
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate, peel14 c s hi]
    show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
        (c.tape c.head)).fst.val = 15
    rw [seq_transition_P2_phase binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head),
      seq_transition_P1_accept_phase seekHomeAfterRoute binToUnaryBody
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)]
    decide
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [peel14 c s hi]
      show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
          (c.tape c.head)).2.2.2 = Move.stay
      rw [seq_transition_P2_move binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
          (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)]
      exact seq_transition_P1_accept_move seekHomeAfterRoute binToUnaryBody
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbit : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [peel14 c s hi]
      show ((seq binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)).transition i ()
          (c.tape c.head)).2.2.1 = c.tape c.head
      rw [seq_transition_P2_bit binToUnaryRouteBody (seq seekHomeAfterRoute binToUnaryBody)
          (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)]
      exact seq_transition_P1_accept_bit seekHomeAfterRoute binToUnaryBody
        (by simp only [hi]; decide) (by simp only [hi]; decide) () (c.tape c.head)
    rw [hbit]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
