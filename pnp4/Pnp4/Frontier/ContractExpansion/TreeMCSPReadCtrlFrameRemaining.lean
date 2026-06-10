import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# `readCtrlFrameRemaining` — D2t-5b: the settle decision (emit vs decrement)

After `readCtrlFrameTag` (the tag), D2t-5's driver reads the control frame's **`remaining` field**
`unaryField remaining = 1^remaining 0` to decide its `settle` action: a frame is pushed with
`remaining = arity ∈ {1,2}` and decremented per completed child, so on tape `remaining ∈ {1,2}`.

* `remaining = 1` (this is the **last** child) ⇒ the internal gate is now complete: **emit** it;
* `remaining = 2` ⇒ one child still pending: **decrement** the frame and await the next.

Like `readCtrlFrameTag`, this is a **fixed-phase unary trie** (the field is ≤ 3 cells), not a `reachesSink`
loop.  Phase layout (`numPhases = 6`): `0,1,2` read the field; `3` = `rem1` (emit branch), `4` = `rem2`
(decrement branch), `5` = reject sink (`remaining = 0`, or `≥ 3` — malformed).  Each accept phase leaves
the head just past the field's terminator, so it composes with the next driver step.

**Progress classification (AGENTS.md): Infrastructure** — a scratch-free tape reader proven by fixed-phase
step-through; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- Phase routing for the `remaining` reader: bit `1` advances the field scan, bit `0` (terminator) lands
in the `rem1`/`rem2` branch (or the reject sink for `remaining = 0` / `≥ 3`). -/
def readCtrlFrameRemainingNext (iv : Nat) (b : Bool) : Nat :=
  if iv = 0 then (if b then 1 else 5)
  else if iv = 1 then (if b then 2 else 3)
  else if iv = 2 then (if b then 5 else 4)
  else iv

/-- Control-frame `remaining` reader: a depth-≤3 unary trie over `unaryField remaining` (`remaining ∈
{1,2}`), branching emit (`rem1`) vs decrement (`rem2`). -/
def readCtrlFrameRemaining : ConstStatePhasedProgram Unit where
  numPhases := 6
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨5, by omega⟩  -- nominal placeholder = reject sink; API is the runConfig lemmas below
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then ((if b then ⟨1, by omega⟩ else ⟨5, by omega⟩ : Fin 6), (), b, Move.right)
    else if i.val = 1 then ((if b then ⟨2, by omega⟩ else ⟨3, by omega⟩ : Fin 6), (), b, Move.right)
    else if i.val = 2 then ((if b then ⟨5, by omega⟩ else ⟨4, by omega⟩ : Fin 6), (), b, Move.right)
    else (i, (), b, Move.stay)
  timeBound := fun _ => 3

@[simp] theorem readCtrlFrameRemaining_numPhases : readCtrlFrameRemaining.numPhases = 6 := rfl
@[simp] theorem readCtrlFrameRemaining_startPhase_val : (readCtrlFrameRemaining.startPhase : Nat) = 0 := rfl
@[simp] theorem readCtrlFrameRemaining_timeBound (n : Nat) : readCtrlFrameRemaining.timeBound n = 3 := rfl

/-- Every step writes back the scanned bit, so the tape is unchanged. -/
theorem readCtrlFrameRemaining_transition_bit (i : Fin 6) (s : Unit) (b : Bool) :
    (readCtrlFrameRemaining.transition i s b).2.2.1 = b := by
  unfold readCtrlFrameRemaining; dsimp only; split_ifs <;> simp

theorem readCtrlFrameRemaining_stepConfig_tape {L : Nat}
    (c : Configuration (M := readCtrlFrameRemaining.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape readCtrlFrameRemaining c hstate,
    readCtrlFrameRemaining_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One reading move (`i.val < 3`): route to `readCtrlFrameRemainingNext i.val b`, advance the head, tape
unchanged. -/
theorem readCtrlFrameRemaining_stepConfig_read {L : Nat}
    (c : Configuration (M := readCtrlFrameRemaining.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val < 3) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < readCtrlFrameRemaining.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c).state).fst.val
        = readCtrlFrameRemainingNext i.val (c.tape c.head)
      ∧ ((TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase readCtrlFrameRemaining c hstate]
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 from by omega) with h | h | h <;>
      cases c.tape c.head <;> simp [readCtrlFrameRemaining, readCtrlFrameRemainingNext, h]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head readCtrlFrameRemaining c hstate]
    have hmove : (readCtrlFrameRemaining.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 from by omega) with h | h | h <;>
        cases c.tape c.head <;> simp [readCtrlFrameRemaining, h]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbound]
  · exact readCtrlFrameRemaining_stepConfig_tape c hstate

/-- **`remaining = 1` (emit branch).**  Field `unaryField 1 = [1,0]`: two steps ⇒ phase `3`, head `+2`. -/
theorem readCtrlFrameRemaining_runConfig_rem1 {L : Nat}
    (c0 : Configuration (M := readCtrlFrameRemaining.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 2 < readCtrlFrameRemaining.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (readCtrlFrameRemaining.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (readCtrlFrameRemaining.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false) :
    (((TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 2
      ∧ (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).tape = c0.tape := by
  have e1 : TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1
      = TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2
      = TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  obtain ⟨s1p, s1h, s1t⟩ := readCtrlFrameRemaining_stepConfig_read c0 (i := c0.state.fst)
    (s := c0.state.snd) (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  have hbit1 : (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).head = false := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, s2h, s2t⟩ := readCtrlFrameRemaining_stepConfig_read
    (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; decide) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p s2h s2t
  refine ⟨by rw [s2p]; rfl, ?_, ?_⟩
  · rw [s2h, s1h]
  · rw [s2t, s1t]

/-- **`remaining = 2` (decrement branch).**  Field `unaryField 2 = [1,1,0]`: three steps ⇒ phase `4`,
head `+3`. -/
theorem readCtrlFrameRemaining_runConfig_rem2 {L : Nat}
    (c0 : Configuration (M := readCtrlFrameRemaining.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < readCtrlFrameRemaining.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (readCtrlFrameRemaining.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (readCtrlFrameRemaining.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (h2 : ∀ p : Fin (readCtrlFrameRemaining.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 3).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 3).tape = c0.tape := by
  have e1 : TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1
      = TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2
      = TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  have e3 : TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 3
      = TM.stepConfig (M := readCtrlFrameRemaining.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2) := TM.runConfig_succ c0 2
  obtain ⟨s1p, s1h, s1t⟩ := readCtrlFrameRemaining_stepConfig_read c0 (i := c0.state.fst)
    (s := c0.state.snd) (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  have hbit1 : (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).head = true := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, s2h, s2t⟩ := readCtrlFrameRemaining_stepConfig_read
    (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; decide) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p s2h s2t
  have hbit2 : (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).tape
      (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).head = false := by
    rw [s2t, s1t]; exact h2 _ (by rw [s2h, s1h])
  obtain ⟨s3p, s3h, s3t⟩ := readCtrlFrameRemaining_stepConfig_read
    (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2)
    (i := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameRemaining.toPhased.toTM) c0 2).state.snd)
    (by rw [s2p]; decide) rfl (by rw [s2h, s1h]; omega)
  rw [s2p, hbit2] at s3p
  rw [← e3] at s3p s3h s3t
  refine ⟨by rw [s3p]; rfl, ?_, ?_⟩
  · rw [s3h, s2h, s1h]
  · rw [s3t, s2t, s1t]

end ContractExpansion
end Frontier
end Pnp4
