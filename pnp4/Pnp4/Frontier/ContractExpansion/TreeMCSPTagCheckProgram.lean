import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Tag-check verifier program (NP-verifier track, first parse phase)

The first concrete phase of the verifier TM: scan the `tagLen`-bit tag field at the front of the
input left-to-right, AND-ing into the control state whether each scanned bit equals the
corresponding big-endian bit of `treePrefixTag`, advancing the head one cell per step.  After
`tagLen` steps the accept phase is reached with state `true` iff every tag bit matched — i.e. the
input carries the correct version tag.

This module establishes the program definition, its `timeBound`, and the structural fact that its
transition never moves the head left (the ingredient the later head-tracking correctness proof
needs).  The semantic correctness (`runConfig` behaviour ⇔ tag match) is the next brick.
-/

/-- Scan-and-compare program for the `tagLen`-bit version tag. -/
def tagCheckProgram : ConstStatePhasedProgram Bool where
  numPhases := tagLen + 1
  startPhase := ⟨0, by omega⟩
  startState := true
  acceptPhase := ⟨tagLen, by omega⟩
  acceptState := true
  transition := fun i s b =>
    if h : i.val < tagLen then
      (⟨i.val + 1, by omega⟩,
        s && (b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩), b, Move.right)
    else
      (⟨tagLen, by omega⟩, s, b, Move.stay)
  timeBound := fun _ => tagLen

@[simp] theorem tagCheckProgram_timeBound (n : Nat) :
    tagCheckProgram.timeBound n = tagLen := rfl

/-- The tag-check transition only ever moves the head right (scanning) or stays; never left. -/
theorem tagCheckProgram_transition_move (i : Fin (tagLen + 1)) (s b : Bool) :
    (tagCheckProgram.transition i s b).2.2.2 ≠ Move.left := by
  unfold tagCheckProgram
  dsimp only
  split <;> simp

/-- The compiled tag-check Turing machine never moves its head left (it only scans rightward),
lifting `tagCheckProgram_transition_move` through `toPhased`/`toTM`.  This underpins head-position
tracking in the forthcoming semantic-correctness proof. -/
theorem tagCheckProgram_neverMovesLeft :
    TMNeverMovesLeft (tagCheckProgram.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact tagCheckProgram_transition_move i s b

/-- One scanning step from a phase `i < tagLen` advances the phase index to `i + 1`.
Single-step building block for the tag-check `runConfig` invariant. -/
theorem tagCheckProgram_stepConfig_phase {L : Nat}
    (c : Configuration (M := tagCheckProgram.toPhased.toTM) L)
    {i : Fin (tagLen + 1)} {s : Bool} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, tagCheckProgram, dif_pos hi]

/-- One scanning step from a phase `i < tagLen` advances the head by one cell (it moves right),
provided the next cell is within the tape.  Companion to `tagCheckProgram_stepConfig_phase`. -/
theorem tagCheckProgram_stepConfig_head {L : Nat}
    (c : Configuration (M := tagCheckProgram.toPhased.toTM) L)
    {i : Fin (tagLen + 1)} {s : Bool} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < tagCheckProgram.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  have hmove : (TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased, tagCheckProgram, dif_pos hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- One scanning step leaves the tape unchanged: it writes back exactly the bit it read.
Companion to the phase/head single-step lemmas. -/
theorem tagCheckProgram_stepConfig_tape {L : Nat}
    (c : Configuration (M := tagCheckProgram.toPhased.toTM) L)
    {i : Fin (tagLen + 1)} {s : Bool} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased, tagCheckProgram, dif_pos hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
