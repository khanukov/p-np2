import Pnp4.Frontier.ContractExpansion.TreeMCSPAtomSeqP1

/-!
# `settleProbeFrame` — D2t-5b (Block A5m-3b): the frame-accepting probe

`settleProbe` (A5m-2) accepts on the **empty** verdict (`φ3`), so a `seq` pipeline through it
continues exactly on the empty branch — the clear arm's shape.  The dec/pop arms need the dual: a
probe that **accepts on the frame verdict**, so their pipelines continue exactly when the control
stack is nonempty.  `settleProbeFrame` is the same two-step machine with `acceptPhase := φ2`
(frame); on the empty branch it idles in `φ3` and a pipeline through it never continues.

`settleProbeFrame_seq_runConfig_frame_handoff` is the packaged P1 leg: on a peeked `1`, three steps
(peek, frame verdict, handoff) land at `P2`'s shifted start (`4 + P2.startPhase`), head one cell
left, tape unchanged — mirroring the empty-path leg of A5m-3a.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component with its
composition transfer; builds no verifier and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The frame-accepting settle probe**: identical transitions to `settleProbe` (step left to peek;
`1` → `φ2` frame, `0` → `φ3` empty; outcomes idle), but with the **frame** verdict as the accept
phase — a `seq` pipeline through it continues exactly on the nonempty branch. -/
def settleProbeFrame : ConstStatePhasedProgram Unit where
  numPhases := 4
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨2, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else if i.val = 1 then
      if b then (⟨2, by omega⟩, (), b, Move.stay)
      else (⟨3, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 2

/-- `settleProbeFrame` as the first `seq` phase, on the **frame** branch (the peeked cell is `1`):
`3` steps (peek left, take the frame verdict — the accept phase — and hand off) land at `P2`'s
shifted start (`4 + P2.startPhase`), head one cell left, tape unchanged.  On the empty branch it
idles in `φ3` and the pipeline never continues — the dec/pop arms run exactly on the frame
branch. -/
theorem settleProbeFrame_seq_runConfig_frame_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq settleProbeFrame P2).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hpos : 1 ≤ (c0.head : Nat))
    (hpeek : ∀ p : Fin ((seq settleProbeFrame P2).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true) :
    (((TM.runConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c0 3).state).fst : Nat)
        = 4 + (P2.startPhase : Nat)
      ∧ ((TM.runConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c0 3).state).snd
          = P2.startState
      ∧ ((TM.runConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c0 3).head : Nat)
          = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c0 3).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (3 : Nat) = (1 + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c0 with hc1
  have hph1 : (c1.state.fst : Nat) = 1 := by
    have h := seq_stepConfig_P1_normal_phase settleProbeFrame P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbeFrame])
      (by simp [hphase, settleProbeFrame]) rfl
    rw [hc1, h]
    simp [settleProbeFrame, hphase]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    have h := seq_stepConfig_P1_normal_head settleProbeFrame P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbeFrame])
      (by simp [hphase, settleProbeFrame]) rfl
    rw [hc1, h]
    have hm : (settleProbeFrame.transition
        ⟨(c0.state.fst : Nat), by simp [hphase, settleProbeFrame]⟩
        c0.state.snd (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [settleProbeFrame, hphase]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape settleProbeFrame P2 c0
      (i := c0.state.fst) (q := c0.state.snd) (by simp [hphase, settleProbeFrame])
      (by simp [hphase, settleProbeFrame]) rfl
    rw [hc1, h]
    have hb : (settleProbeFrame.transition
        ⟨(c0.state.fst : Nat), by simp [hphase, settleProbeFrame]⟩
        c0.state.snd (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [settleProbeFrame, hphase]
    rw [hb]
    funext j
    by_cases hj : j = c0.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]
  set c2 := TM.stepConfig (M := (seq settleProbeFrame P2).toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = true := by
    rw [htp1]
    exact hpeek c1.head (by omega)
  have hph2 : (c2.state.fst : Nat) = 2 := by
    have h := seq_stepConfig_P1_normal_phase settleProbeFrame P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbeFrame])
      (by simp [hph1, settleProbeFrame]) rfl
    rw [hc2, h]
    simp [settleProbeFrame, hph1, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) - 1 := by
    have h := seq_stepConfig_P1_normal_head settleProbeFrame P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbeFrame])
      (by simp [hph1, settleProbeFrame]) rfl
    rw [hc2, h]
    have hm : (settleProbeFrame.transition
        ⟨(c1.state.fst : Nat), by simp [hph1, settleProbeFrame]⟩
        c1.state.snd (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [settleProbeFrame, hph1, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    have h := seq_stepConfig_P1_normal_tape settleProbeFrame P2 c1
      (i := c1.state.fst) (q := c1.state.snd) (by simp [hph1, settleProbeFrame])
      (by simp [hph1, settleProbeFrame]) rfl
    rw [hc2, h]
    have hb : (settleProbeFrame.transition
        ⟨(c1.state.fst : Nat), by simp [hph1, settleProbeFrame]⟩
        c1.state.snd (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [settleProbeFrame, hph1, hbit1]
    rw [hb]
    have : c1.write c1.head (c1.tape c1.head) = c1.tape := by
      funext j
      by_cases hj : j = c1.head
      · subst hj; simp [Configuration.write]
      · simp [Configuration.write, hj]
    rw [this, htp1]
  have hacc : (c2.state.fst : Nat) = (settleProbeFrame.acceptPhase : Nat) := by rw [hph2]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := seq_stepConfig_P1_accept_phase settleProbeFrame P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbeFrame]) hacc rfl
    rw [h]; rfl
  · exact seq_stepConfig_P1_accept_state settleProbeFrame P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbeFrame]) hacc rfl
  · rw [seq_stepConfig_P1_accept_head settleProbeFrame P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbeFrame]) hacc rfl]
    exact hhd2
  · rw [seq_stepConfig_P1_accept_tape settleProbeFrame P2 c2
      (i := c2.state.fst) (q := c2.state.snd) (by simp [hph2, settleProbeFrame]) hacc rfl]
    exact htp2

end ContractExpansion
end Frontier
end Pnp4
