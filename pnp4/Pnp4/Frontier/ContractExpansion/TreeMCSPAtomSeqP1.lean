import Pnp4.Frontier.ContractExpansion.TreeMCSPSettleProbe
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram

/-!
# Atomic movers as the **first** `seq` phase — D2t-5b (Block A5m-3a)

The arm pipelines open with single-cell movers (`stepLeftOnce` off the cursor marker,
`stepRightOnce` back over a sentinel) and the settle probe; like the leftward scan (A5m-1a), their
run behaviour must transfer into a composite's P1 region with the handoff.  Three packaged legs, all
tape-preserving:

* `stepLeftOnce_seq_runConfig_handoff` — `2` steps: move left, hand off (lands at `P2`'s shifted
  start, head one left);
* `stepRightOnce_seq_runConfig_handoff` — `2` steps: move right, hand off (head one right; needs
  head-room);
* `settleProbe_seq_runConfig_empty_handoff` — `3` steps: peek left, take the **empty** verdict
  (`φ3` is the probe's accept phase), hand off (head one left).  The **frame** verdict (`φ2`) idles
  by design — a `seq` pipeline through the probe runs its continuation exactly on the empty branch,
  which is what the clear arm consumes.

**Progress classification (AGENTS.md): Infrastructure** — composition transfers for verifier
machine components; builds no verifier and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### `stepLeftOnce` as P1 -/

/-- `stepLeftOnce` as the first `seq` phase: `2` steps (move left, hand off) land at `P2`'s shifted
start with state `P2.startState`, head one cell left, tape unchanged. -/
theorem stepLeftOnce_seq_runConfig_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq stepLeftOnce P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hpos : 1 ≤ (c0.head : Nat)) :
    (((TM.runConfig (M := (seq stepLeftOnce P2).toPhased.toTM) c0 2).state).fst : Nat)
        = 2 + (P2.startPhase : Nat)
      ∧ ((TM.runConfig (M := (seq stepLeftOnce P2).toPhased.toTM) c0 2).state).snd
          = P2.startState
      ∧ ((TM.runConfig (M := (seq stepLeftOnce P2).toPhased.toTM) c0 2).head : Nat)
          = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq stepLeftOnce P2).toPhased.toTM) c0 2).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := (seq stepLeftOnce P2).toPhased.toTM) c0 with hc1
  -- Step 1: normal region (phase 0 ≠ accept 1): move left, phase → 1.
  have hph1 : (c1.state.fst : Nat) = 1 := by
    have h := seq_stepConfig_P1_normal_phase stepLeftOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    simp [stepLeftOnce, hphase]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    have h := seq_stepConfig_P1_normal_head stepLeftOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    have hm : (stepLeftOnce.transition ⟨(c0.state.fst : Nat), by simp [hphase]⟩ c0.state.snd
        (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [stepLeftOnce, hphase]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape stepLeftOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    have hb : (stepLeftOnce.transition ⟨(c0.state.fst : Nat), by simp [hphase]⟩ c0.state.snd
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepLeftOnce, hphase]
    rw [hb]
    funext j
    by_cases hj : j = c0.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]
  -- Step 2: handoff (phase 1 = accept).
  have hacc : (c1.state.fst : Nat) = (stepLeftOnce.acceptPhase : Nat) := by rw [hph1]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := seq_stepConfig_P1_accept_phase stepLeftOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
    rw [h]; rfl
  · exact seq_stepConfig_P1_accept_state stepLeftOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
  · rw [seq_stepConfig_P1_accept_head stepLeftOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl]
    exact hhd1
  · rw [seq_stepConfig_P1_accept_tape stepLeftOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl]
    exact htp1

/-! ### `stepRightOnce` as P1 -/

/-- `stepRightOnce` as the first `seq` phase: `2` steps (move right, hand off) land at `P2`'s
shifted start, head one cell right, tape unchanged. -/
theorem stepRightOnce_seq_runConfig_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hroom : (c0.head : Nat) + 1 < (seq stepRightOnce P2).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (seq stepRightOnce P2).toPhased.toTM) c0 2).state).fst : Nat)
        = 2 + (P2.startPhase : Nat)
      ∧ ((TM.runConfig (M := (seq stepRightOnce P2).toPhased.toTM) c0 2).state).snd
          = P2.startState
      ∧ ((TM.runConfig (M := (seq stepRightOnce P2).toPhased.toTM) c0 2).head : Nat)
          = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := (seq stepRightOnce P2).toPhased.toTM) c0 2).tape = c0.tape := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c0 with hc1
  have hph1 : (c1.state.fst : Nat) = 1 := by
    have h := seq_stepConfig_P1_normal_phase stepRightOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    simp [stepRightOnce, hphase]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + 1 := by
    have h := seq_stepConfig_P1_normal_head stepRightOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    have hm : (stepRightOnce.transition ⟨(c0.state.fst : Nat), by simp [hphase]⟩ c0.state.snd
        (c0.tape c0.head)).snd.snd.snd = Move.right := by
      simp [stepRightOnce, hphase]
    rw [hm]
    simp only [Configuration.moveHead, dif_pos hroom]
  have htp1 : c1.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape stepRightOnce P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase]) (by simp [hphase]) rfl
    rw [hc1, h]
    have hb : (stepRightOnce.transition ⟨(c0.state.fst : Nat), by simp [hphase]⟩ c0.state.snd
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepRightOnce, hphase]
    rw [hb]
    funext j
    by_cases hj : j = c0.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]
  have hacc : (c1.state.fst : Nat) = (stepRightOnce.acceptPhase : Nat) := by rw [hph1]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := seq_stepConfig_P1_accept_phase stepRightOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
    rw [h]; rfl
  · exact seq_stepConfig_P1_accept_state stepRightOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl
  · rw [seq_stepConfig_P1_accept_head stepRightOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl]
    exact hhd1
  · rw [seq_stepConfig_P1_accept_tape stepRightOnce P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1]) hacc rfl]
    exact htp1

/-! ### `settleProbe` (empty path) as P1 -/

/-- `settleProbe` as the first `seq` phase, on the **empty** branch (the peeked cell is `0`): `3`
steps (peek left, take the empty verdict — the probe's accept phase — and hand off) land at `P2`'s
shifted start (`4 + P2.startPhase`), head one cell left, tape unchanged.  On the frame branch the
probe idles in `φ2` and the pipeline never continues — the clear arm runs exactly on this branch. -/
theorem settleProbe_seq_runConfig_empty_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq settleProbe P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hpos : 1 ≤ (c0.head : Nat))
    (hpeek : ∀ p : Fin ((seq settleProbe P2).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = false) :
    (((TM.runConfig (M := (seq settleProbe P2).toPhased.toTM) c0 3).state).fst : Nat)
        = 4 + (P2.startPhase : Nat)
      ∧ ((TM.runConfig (M := (seq settleProbe P2).toPhased.toTM) c0 3).state).snd
          = P2.startState
      ∧ ((TM.runConfig (M := (seq settleProbe P2).toPhased.toTM) c0 3).head : Nat)
          = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq settleProbe P2).toPhased.toTM) c0 3).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (3 : Nat) = (1 + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := (seq settleProbe P2).toPhased.toTM) c0 with hc1
  -- Step 1: peek left (phase 0 → 1, normal region: 0 ≠ accept 3).
  have hph1 : (c1.state.fst : Nat) = 1 := by
    have h := seq_stepConfig_P1_normal_phase settleProbe P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbe])
      (by simp [hphase, settleProbe]) rfl
    rw [hc1, h]
    simp [settleProbe, hphase]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    have h := seq_stepConfig_P1_normal_head settleProbe P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbe])
      (by simp [hphase, settleProbe]) rfl
    rw [hc1, h]
    have hm : (settleProbe.transition ⟨(c0.state.fst : Nat), by simp [hphase, settleProbe]⟩
        c0.state.snd (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [settleProbe, hphase]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape settleProbe P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbe])
      (by simp [hphase, settleProbe]) rfl
    rw [hc1, h]
    have hb : (settleProbe.transition ⟨(c0.state.fst : Nat), by simp [hphase, settleProbe]⟩
        c0.state.snd (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [settleProbe, hphase]
    rw [hb]
    funext j
    by_cases hj : j = c0.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]
  -- Step 2: the empty verdict (phase 1 → 3, normal region: 1 ≠ 3), on the peeked `0`.
  set c2 := TM.stepConfig (M := (seq settleProbe P2).toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = false := by
    rw [htp1]
    exact hpeek c1.head (by omega)
  have hph2 : (c2.state.fst : Nat) = 3 := by
    have h := seq_stepConfig_P1_normal_phase settleProbe P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbe])
      (by simp [hph1, settleProbe]) rfl
    rw [hc2, h]
    simp [settleProbe, hph1, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) - 1 := by
    have h := seq_stepConfig_P1_normal_head settleProbe P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbe])
      (by simp [hph1, settleProbe]) rfl
    rw [hc2, h]
    have hm : (settleProbe.transition ⟨(c1.state.fst : Nat), by simp [hph1, settleProbe]⟩
        c1.state.snd (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [settleProbe, hph1, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape settleProbe P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbe])
      (by simp [hph1, settleProbe]) rfl
    rw [hc2, h]
    have hb : (settleProbe.transition ⟨(c1.state.fst : Nat), by simp [hph1, settleProbe]⟩
        c1.state.snd (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [settleProbe, hph1, hbit1]
    rw [hb]
    have : c1.write c1.head (c1.tape c1.head) = c1.tape := by
      funext j
      by_cases hj : j = c1.head
      · subst hj; simp [Configuration.write]
      · simp [Configuration.write, hj]
    rw [this, htp1]
  -- Step 3: handoff (phase 3 = accept).
  have hacc : (c2.state.fst : Nat) = (settleProbe.acceptPhase : Nat) := by rw [hph2]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := seq_stepConfig_P1_accept_phase settleProbe P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbe]) hacc rfl
    rw [h]; rfl
  · exact seq_stepConfig_P1_accept_state settleProbe P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbe]) hacc rfl
  · rw [seq_stepConfig_P1_accept_head settleProbe P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbe]) hacc rfl]
    exact hhd2
  · rw [seq_stepConfig_P1_accept_tape settleProbe P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbe]) hacc rfl]
    exact htp2

end ContractExpansion
end Frontier
end Pnp4
