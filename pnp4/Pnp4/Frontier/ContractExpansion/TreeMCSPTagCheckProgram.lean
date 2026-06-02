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

This module establishes the program definition, its `timeBound`, the structural fact that its
transition never moves the head left, the single-step `runConfig` lemmas, the scan invariant
(phase/head reach `k`, tape unchanged), the accept-iff (`accepts = final matched Bool`), and the
end-to-end semantic correctness `tagCheckProgram_accepts_eq_tagMatch`: the phase accepts iff the
input's leading `tagLen` cells equal `treePrefixTag` bit-for-bit (`tagMatchPrefix x tagLen`).

This is one parse phase of the eventual verifier TM; on its own it is not the verifier and proves
no separation result.  The next bricks decode the remaining parser fields (gamma length, instance,
index, prefix) and the witness/circuit relation.
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

/-! ## Semantic characterization of the accumulated-match Bool

The accept-iff (`tagCheckProgram_accepts_eq_state`) reduces acceptance to the final value of the
accumulated-match Bool.  This section pins that Bool down *semantically*: it is exactly the
conjunction, over the first `tagLen` input cells, of "this cell equals the corresponding big-endian
tag bit".  That makes the tag-check phase a verified bit-by-bit equality test of the input's leading
`tagLen` bits against `treePrefixTag`. -/

/-- Big-endian bit `j` of the version tag `treePrefixTag`, as a total `Nat`-indexed `Bool`
(the `Fin`-free form of `natBitBE treePrefixTag tagLen`). -/
def tagBitAt (j : Nat) : Bool :=
  decide (treePrefixTag / 2 ^ (tagLen - 1 - j) % 2 = 1)

/-- `tagBitAt` agrees with `natBitBE treePrefixTag tagLen` on every in-range index (`rfl`: both are
`decide (treePrefixTag / 2 ^ (tagLen - 1 - j) % 2 = 1)`). -/
theorem natBitBE_tag_eq (j : Fin tagLen) :
    natBitBE treePrefixTag tagLen j = tagBitAt j.1 := rfl

/-- The bit the verifier reads at the `j`-th input cell of `x` (the initial-tape value at position
`j`, total in `j`: blank `false` past the input length). -/
def tagCheckInputBit {L : Nat} (x : Boolcube.Point L) (j : Nat) : Bool :=
  if h : j < L then x ⟨j, h⟩ else false

/-- Specification of the tag-check accumulator after `k` scan steps: the conjunction over the first
`k` input cells that each equals the corresponding big-endian tag bit. -/
def tagMatchPrefix {L : Nat} (x : Boolcube.Point L) : Nat → Bool
  | 0 => true
  | k + 1 => tagMatchPrefix x k && (tagCheckInputBit x k == tagBitAt k)

@[simp] theorem tagMatchPrefix_zero {L : Nat} (x : Boolcube.Point L) :
    tagMatchPrefix x 0 = true := rfl

theorem tagMatchPrefix_succ {L : Nat} (x : Boolcube.Point L) (k : Nat) :
    tagMatchPrefix x (k + 1)
      = (tagMatchPrefix x k && (tagCheckInputBit x k == tagBitAt k)) := rfl

/-- The bit read at the head equals the corresponding total input bit, whenever the tape is the
initial tape and the head sits at position `k`.  (The head value determines the cell; out-of-input
positions read blank `false`, matching `tagCheckInputBit`.) -/
theorem tagCheckProgram_tape_read {L : Nat} (x : Boolcube.Point L)
    (c : Configuration (M := tagCheckProgram.toPhased.toTM) L) (k : Nat)
    (htp : c.tape = (tagCheckProgram.toPhased.toTM.initialConfig x).tape)
    (hhd : (c.head : Nat) = k) :
    c.tape c.head = tagCheckInputBit x k := by
  rw [htp]
  unfold tagCheckInputBit
  by_cases hkL : k < L
  · have hlt : (c.head : Nat) < L := by rw [hhd]; exact hkL
    rw [TM.initial_tape_input (M := tagCheckProgram.toPhased.toTM) x hlt, dif_pos hkL]
    exact congrArg x (Fin.ext hhd)
  · have hge : L ≤ (c.head : Nat) := by rw [hhd]; omega
    rw [TM.initial_tape_blank (M := tagCheckProgram.toPhased.toTM) x hge, dif_neg hkL]

/--
Matched-state invariant: after `k ≤ tagLen` scan steps the accumulated-match Bool equals
`tagMatchPrefix x k` — the bitwise equality of the first `k` input cells against the tag.  Proved by
induction on `k`: the base case is the start state `true`, and the step combines the single-step
state-update lemma with the scan invariant (head at `k`, tape unchanged) and `natBitBE_tag_eq`.
-/
theorem tagCheckProgram_runConfig_matched {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ tagLen →
      ((TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) k).state).snd
        = tagMatchPrefix x k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := tagCheckProgram_runConfig_scan x k (by omega)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := tagCheckProgram.toPhased.toTM)
        (tagCheckProgram.toPhased.toTM.initialConfig x) k with hc
      have hi : (c.state.fst : Nat) < tagLen := by rw [hph]; omega
      have hstep := tagCheckProgram_stepConfig_state c
        (i := c.state.fst) (s := c.state.snd) hi rfl
      have htag : natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩ = tagBitAt k := by
        rw [natBitBE_tag_eq]; exact congrArg tagBitAt hph
      have hbit : c.tape c.head = tagCheckInputBit x k :=
        tagCheckProgram_tape_read x c k htp hhd
      have hsnd : c.state.snd = tagMatchPrefix x k := ih (by omega)
      rw [hstep, htag, hbit, hsnd, tagMatchPrefix_succ]

/-- End-to-end semantic correctness of the tag-check phase: it accepts iff the first `tagLen` cells
of the input match `treePrefixTag` bit-for-bit.  Combines the accept-iff with the matched-state
invariant at the final step `k = tagLen` (the program's `runTime`). -/
theorem tagCheckProgram_accepts_eq_tagMatch {L : Nat} (x : Boolcube.Point L) :
    TM.accepts (M := tagCheckProgram.toPhased.toTM) (n := L) x
      = tagMatchPrefix x tagLen := by
  rw [tagCheckProgram_accepts_eq_state]
  have hrun : TM.run (M := tagCheckProgram.toPhased.toTM) (n := L) x
      = TM.runConfig (M := tagCheckProgram.toPhased.toTM)
          (tagCheckProgram.toPhased.toTM.initialConfig x) tagLen := rfl
  rw [hrun]
  exact tagCheckProgram_runConfig_matched x tagLen (Nat.le_refl tagLen)

end ContractExpansion
end Frontier
end Pnp4
