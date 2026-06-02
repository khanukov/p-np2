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

/-- One scanning step updates the accumulated-match state: it ANDs in whether the scanned bit
equals the corresponding tag bit.  Companion to the phase/head/tape single-step lemmas. -/
theorem tagCheckProgram_stepConfig_state {L : Nat}
    (c : Configuration (M := tagCheckProgram.toPhased.toTM) L)
    {i : Fin (tagLen + 1)} {s : Bool} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := tagCheckProgram.toPhased.toTM) c).state).snd
      = (s && (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩)) := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, tagCheckProgram, dif_pos hi]

/--
Scan invariant: after `k ≤ tagLen` steps of the tag-check TM from the initial configuration, the
control phase index and the head are both at position `k`, and the tape is unchanged.  Proved by
induction on `k`, applying the single-step phase/head/tape lemmas (with `i`/`s` taken as the state
projections and `hstate := rfl` by Sigma-eta).
-/
theorem tagCheckProgram_runConfig_scan {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ tagLen →
      (((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).state).fst : Nat) = k
      ∧ ((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ (TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).tape
          = (tagCheckProgram.toPhased.toTM.initialConfig x).tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hi : (((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).state).fst : Nat) < tagLen := by
        rw [hph]; omega
      have hbnd : ((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).head : Nat) + 1
          < tagCheckProgram.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + tagLen + 1; omega
      rw [TM.runConfig_succ]
      refine ⟨?_, ?_, ?_⟩
      · rw [tagCheckProgram_stepConfig_phase _ hi rfl, hph]
      · rw [tagCheckProgram_stepConfig_head _ hi rfl hbnd, hhd]
      · rw [tagCheckProgram_stepConfig_tape _ hi rfl, htp]

/-- The tag-check TM accepts iff, after its `tagLen` scan steps, the accumulated-match Bool is set.
Combines `runConfig_scan` (the phase reaches `tagLen` = the accept phase) with the acceptance
definition. -/
theorem tagCheckProgram_accepts_eq_state {L : Nat} (x : Boolcube.Point L) :
    TM.accepts (M := tagCheckProgram.toPhased.toTM) (n := L) x
      = (TM.run (M := tagCheckProgram.toPhased.toTM) (n := L) x).state.snd := by
  obtain ⟨hph, _, _⟩ := tagCheckProgram_runConfig_scan x tagLen (Nat.le_refl tagLen)
  have hrun : TM.run (M := tagCheckProgram.toPhased.toTM) (n := L) x
      = TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) tagLen := rfl
  have key : ((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
        (tagCheckProgram.toPhased.toTM.initialConfig x) tagLen).state
        = (tagCheckProgram.toPhased.toTM).accept)
      ↔ (TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) tagLen).state.snd = true := by
    constructor
    · intro h; rw [h]; rfl
    · intro h
      exact Sigma.ext (Fin.ext (hph.trans rfl)) (heq_of_eq h)
  unfold TM.accepts
  rw [hrun]
  simp only [key]
  generalize (TM.runConfig (M := tagCheckProgram.toPhased.toTM)
    (tagCheckProgram.toPhased.toTM.initialConfig x) tagLen).state.snd = b
  cases b <;> rfl

end ContractExpansion
end Frontier
end Pnp4
