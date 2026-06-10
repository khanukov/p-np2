import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# `readCtrlFrameTag` — D2t-5b: read a control frame's tag (the settle/pop entry)

D2t-5's driver, on a completed subtree, must read the **top control frame** `(tag, remaining)` off
`STACK_ctrl` to decide what to do (decrement, or emit the `tag` gate).  This brick is the first step: read
the frame's **tag-code field** `unaryField tag.tagCode = 1^tagCode 0` (with `tagCode ∈ {0,1,2}` for
`tnot`/`tand`/`tor`, `CtrlFrameStack`) and dispatch to a per-tag phase.

Because `tagCode ≤ 2`, the field is at most 3 cells, so this is a **fixed-phase unary trie in finite
control** — the control-frame analogue of `treeTagDispatch` (D2t-1), and like it dispatch is by
phase-routing, **not** a `reachesSink` loop.  Each read step advances the head past one `1`; hitting the
terminator `0` lands in the tag's phase with the head just past the field (at the `remaining` field), so it
composes directly with the next reader.

Phase layout (`numPhases = 7`): `0,1,2` read the field; `3`=tnot, `4`=tand, `5`=tor are the per-tag accept
phases; `6` = reject sink (a `1` in the 3rd cell, i.e. tag code `≥ 3` with no terminator — malformed).

* `readCtrlFrameTag_runConfig_tnot/tand/tor` — from the frame's tag field at the head (phase `0`), after
  `tagCode + 1` steps the program lands in the tag's phase, head advanced by `tagCode + 1` (past the
  terminator), tape unchanged.  The cell hypotheses are exactly `unaryField tagCode`.

**Progress classification (AGENTS.md): Infrastructure** — a scratch-free tape reader proven by fixed-phase
step-through; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- The tag-reader's phase-routing as a pure `Nat → Bool → Nat`: at reading phase `iv`, bit `1` advances to
the next reading phase, bit `0` (terminator) lands in the tag's accept phase. -/
def readCtrlFrameTagNext (iv : Nat) (b : Bool) : Nat :=
  if iv = 0 then (if b then 1 else 3)
  else if iv = 1 then (if b then 2 else 4)
  else if iv = 2 then (if b then 6 else 5)
  else iv

/-- Control-frame tag reader: a depth-≤3 unary trie reading `unaryField tagCode`. -/
def readCtrlFrameTag : ConstStatePhasedProgram Unit where
  numPhases := 7
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨6, by omega⟩  -- nominal placeholder = reject sink; API is the runConfig lemmas below
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then ((if b then ⟨1, by omega⟩ else ⟨3, by omega⟩ : Fin 7), (), b, Move.right)
    else if i.val = 1 then ((if b then ⟨2, by omega⟩ else ⟨4, by omega⟩ : Fin 7), (), b, Move.right)
    else if i.val = 2 then ((if b then ⟨6, by omega⟩ else ⟨5, by omega⟩ : Fin 7), (), b, Move.right)
    else (i, (), b, Move.stay)
  timeBound := fun _ => 3

@[simp] theorem readCtrlFrameTag_numPhases : readCtrlFrameTag.numPhases = 7 := rfl
@[simp] theorem readCtrlFrameTag_startPhase_val : (readCtrlFrameTag.startPhase : Nat) = 0 := rfl
@[simp] theorem readCtrlFrameTag_timeBound (n : Nat) : readCtrlFrameTag.timeBound n = 3 := rfl

/-- Every step writes back the scanned bit, so the tape is unchanged. -/
theorem readCtrlFrameTag_transition_bit (i : Fin 7) (s : Unit) (b : Bool) :
    (readCtrlFrameTag.transition i s b).2.2.1 = b := by
  unfold readCtrlFrameTag; dsimp only; split_ifs <;> simp

theorem readCtrlFrameTag_stepConfig_tape {L : Nat}
    (c : Configuration (M := readCtrlFrameTag.toPhased.toTM) L)
    {i : Fin 7} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape readCtrlFrameTag c hstate,
    readCtrlFrameTag_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One reading move (`i.val < 3`): route to `readCtrlFrameTagNext i.val b`, advance the head, tape
unchanged. -/
theorem readCtrlFrameTag_stepConfig_read {L : Nat}
    (c : Configuration (M := readCtrlFrameTag.toPhased.toTM) L)
    {i : Fin 7} {s : Unit} (hi : i.val < 3) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < readCtrlFrameTag.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c).state).fst.val
        = readCtrlFrameTagNext i.val (c.tape c.head)
      ∧ ((TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase readCtrlFrameTag c hstate]
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 from by omega) with h | h | h <;>
      cases c.tape c.head <;> simp [readCtrlFrameTag, readCtrlFrameTagNext, h]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head readCtrlFrameTag c hstate]
    have hmove : (readCtrlFrameTag.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 from by omega) with h | h | h <;>
        cases c.tape c.head <;> simp [readCtrlFrameTag, h]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbound]
  · exact readCtrlFrameTag_stepConfig_tape c hstate

/-- **`tnot` tag** (`unaryField 0 = [0]`): one step (terminator at the head) ⇒ phase `3`, head `+1`. -/
theorem readCtrlFrameTag_runConfig_tnot {L : Nat}
    (c0 : Configuration (M := readCtrlFrameTag.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 1 < readCtrlFrameTag.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false) :
    (((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).tape = c0.tape := by
  obtain ⟨s1p, s1h, s1t⟩ := readCtrlFrameTag_stepConfig_read c0 (i := c0.state.fst) (s := c0.state.snd)
    (by rw [hphase]; omega) rfl hb
  rw [hphase, h0 c0.head rfl] at s1p
  rw [TM.runConfig_one]
  exact ⟨by rw [s1p]; rfl, s1h, s1t⟩

/-- **`tand` tag** (`unaryField 1 = [1,0]`): two steps ⇒ phase `4`, head `+2`. -/
theorem readCtrlFrameTag_runConfig_tand {L : Nat}
    (c0 : Configuration (M := readCtrlFrameTag.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 2 < readCtrlFrameTag.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false) :
    (((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 2
      ∧ (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).tape = c0.tape := by
  have e1 : TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1
      = TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2
      = TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  obtain ⟨s1p, s1h, s1t⟩ := readCtrlFrameTag_stepConfig_read c0 (i := c0.state.fst) (s := c0.state.snd)
    (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  have hbit1 : (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).head = false := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, s2h, s2t⟩ := readCtrlFrameTag_stepConfig_read
    (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; decide) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p s2h s2t
  refine ⟨by rw [s2p]; rfl, ?_, ?_⟩
  · rw [s2h, s1h]
  · rw [s2t, s1t]

/-- **`tor` tag** (`unaryField 2 = [1,1,0]`): three steps ⇒ phase `5`, head `+3`. -/
theorem readCtrlFrameTag_runConfig_tor {L : Nat}
    (c0 : Configuration (M := readCtrlFrameTag.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < readCtrlFrameTag.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (h2 : ∀ p : Fin (readCtrlFrameTag.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 3).state).fst : Nat) = 5
      ∧ ((TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 3).tape = c0.tape := by
  have e1 : TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1
      = TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2
      = TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  have e3 : TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 3
      = TM.stepConfig (M := readCtrlFrameTag.toPhased.toTM)
          (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2) := TM.runConfig_succ c0 2
  obtain ⟨s1p, s1h, s1t⟩ := readCtrlFrameTag_stepConfig_read c0 (i := c0.state.fst) (s := c0.state.snd)
    (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  have hbit1 : (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).head = true := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, s2h, s2t⟩ := readCtrlFrameTag_stepConfig_read
    (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; decide) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p s2h s2t
  have hbit2 : (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).tape
      (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).head = false := by
    rw [s2t, s1t]; exact h2 _ (by rw [s2h, s1h])
  obtain ⟨s3p, s3h, s3t⟩ := readCtrlFrameTag_stepConfig_read
    (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2)
    (i := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).state.fst)
    (s := (TM.runConfig (M := readCtrlFrameTag.toPhased.toTM) c0 2).state.snd)
    (by rw [s2p]; decide) rfl (by rw [s2h, s1h]; omega)
  rw [s2p, hbit2] at s3p
  rw [← e3] at s3p s3h s3t
  refine ⟨by rw [s3p]; rfl, ?_, ?_⟩
  · rw [s3h, s2h, s1h]
  · rw [s3t, s2t, s1t]

end ContractExpansion
end Frontier
end Pnp4
