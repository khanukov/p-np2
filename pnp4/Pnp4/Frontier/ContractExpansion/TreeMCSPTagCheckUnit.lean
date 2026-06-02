import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Unit-state tag-check verifier program (NP-verifier track, common-state assembly)

`TreeMCSPTagCheckProgram.lean` builds the tag check as a `ConstStatePhasedProgram Bool` (it AND-accumulates
"prefix matches tag so far" into a `Bool` control state).  But `seq`/`seqList` require *one* shared state
type for all phases of the assembled verifier `M`, and the self-loop phases (`gammaSelfLoopScan`,
`selfLoopIncrement`, …) are `ConstStatePhasedProgram Unit` (see `TM_VERIFIER_STRATEGY.md` §6a's
state-uniformity finding).  Rather than lift every self-loop to `Bool`, this module re-expresses the tag
check over **`Unit`**, so the common state can be `Unit` and the existing `Unit` composition machinery
applies directly.

The trick is to phase-encode the match state instead of carrying a `Bool`: phases `0 … tagLen-1` scan and
compare; a **match** advances to the next phase (moving right), a **mismatch** jumps to a dedicated
**reject sink** phase `tagLen + 1`; phase `tagLen` is the accept phase (reached iff *every* tag bit
matched).  Both the accept phase and the sink idle (stay).  `numPhases = tagLen + 2`.

This module builds the program and its structural facts (`timeBound`, never-moves-left).  It builds no
verifier and proves no separation. -/

/-- `Unit`-state tag-check: phase-encodes the match state.  Phases `0 … tagLen-1` compare the scanned bit
to the corresponding big-endian bit of `treePrefixTag`; a match advances (right), a mismatch jumps to the
reject sink phase `tagLen + 1`; the accept phase `tagLen` and the sink both idle. -/
def tagCheckProgramU : ConstStatePhasedProgram Unit where
  numPhases := tagLen + 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨tagLen, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h : i.val < tagLen then
      bif b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩ then
        (⟨i.val + 1, by omega⟩, (), b, Move.right)
      else
        (⟨tagLen + 1, by omega⟩, (), b, Move.right)
    else
      (i, (), b, Move.stay)
  timeBound := fun _ => tagLen

@[simp] theorem tagCheckProgramU_timeBound (n : Nat) :
    tagCheckProgramU.timeBound n = tagLen := rfl

@[simp] theorem tagCheckProgramU_numPhases :
    tagCheckProgramU.numPhases = tagLen + 2 := rfl

@[simp] theorem tagCheckProgramU_startPhase_val :
    (tagCheckProgramU.startPhase : Nat) = 0 := rfl

@[simp] theorem tagCheckProgramU_acceptPhase_val :
    (tagCheckProgramU.acceptPhase : Nat) = tagLen := rfl

/-- The `Unit` tag-check transition only ever moves the head right (scanning, match or mismatch) or
stays (accept/sink); never left. -/
theorem tagCheckProgramU_transition_move (i : Fin (tagLen + 2)) (s : Unit) (b : Bool) :
    (tagCheckProgramU.transition i s b).2.2.2 ≠ Move.left := by
  unfold tagCheckProgramU
  dsimp only
  split_ifs with h
  · cases b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩ <;> simp
  · simp

/-- The compiled `Unit` tag-check Turing machine never moves its head left (lifts
`tagCheckProgramU_transition_move` through `toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem tagCheckProgramU_neverMovesLeft :
    TMNeverMovesLeft (tagCheckProgramU.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact tagCheckProgramU_transition_move i s b

/-! ### Single-step lemmas

Each step writes back the scanned bit (tape unchanged).  A *match* (`i < tagLen`, scanned bit equals
the tag bit) advances the phase and head; a *mismatch* jumps to the sink `tagLen + 1`; from any phase
`≥ tagLen` (accept or sink) the machine idles. These consume the toolkit's generic single-step
characterization `toTM_stepConfig_*`. -/

/-- The tag-check transition always writes back the scanned bit (3rd component `= b`). -/
theorem tagCheckProgramU_transition_bit (i : Fin (tagLen + 2)) (s : Unit) (b : Bool) :
    (tagCheckProgramU.transition i s b).2.2.1 = b := by
  unfold tagCheckProgramU
  dsimp only
  split_ifs with h
  · cases b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩ <;> simp
  · simp

/-- Every step leaves the tape unchanged (writes the scanned bit back). -/
theorem tagCheckProgramU_stepConfig_tape {L : Nat}
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L)
    {i : Fin (tagLen + 2)} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape tagCheckProgramU c hstate,
    tagCheckProgramU_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- The bit read at the head equals the corresponding total input bit when the tape is the initial
tape and the head sits at position `k` (mirrors `tagCheckProgram_tape_read` for the `Unit` machine). -/
theorem tagCheckProgramU_tape_read {L : Nat} (x : Boolcube.Point L)
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L) (k : Nat)
    (htp : c.tape = (tagCheckProgramU.toPhased.toTM.initialConfig x).tape)
    (hhd : (c.head : Nat) = k) :
    c.tape c.head = tagCheckInputBit x k := by
  rw [htp]
  unfold tagCheckInputBit
  by_cases hkL : k < L
  · have hlt : (c.head : Nat) < L := by rw [hhd]; exact hkL
    rw [TM.initial_tape_input (M := tagCheckProgramU.toPhased.toTM) x hlt, dif_pos hkL]
    exact congrArg x (Fin.ext hhd)
  · have hge : L ≤ (c.head : Nat) := by rw [hhd]; omega
    rw [TM.initial_tape_blank (M := tagCheckProgramU.toPhased.toTM) x hge, dif_neg hkL]

/-- Match step (`i < tagLen`, scanned bit equals tag bit): advance the phase to `i + 1`. -/
theorem tagCheckProgramU_stepConfig_match_phase {L : Nat}
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L)
    {i : Fin (tagLen + 2)} {s : Unit} (hi : i.val < tagLen) (hstate : c.state = ⟨i, s⟩)
    (hmatch : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = true) :
    ((TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase tagCheckProgramU c hstate]
  simp only [tagCheckProgramU, dif_pos hi, hmatch, cond_true]

/-- Match step: advance the head by one (it moves right), within tape bounds. -/
theorem tagCheckProgramU_stepConfig_match_head {L : Nat}
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L)
    {i : Fin (tagLen + 2)} {s : Unit} (hi : i.val < tagLen) (hstate : c.state = ⟨i, s⟩)
    (hmatch : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = true)
    (hbound : (c.head : Nat) + 1 < tagCheckProgramU.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head tagCheckProgramU c hstate]
  have hmove : (tagCheckProgramU.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp only [tagCheckProgramU, dif_pos hi, hmatch, cond_true]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Mismatch step (`i < tagLen`, scanned bit differs from tag bit): jump to the sink `tagLen + 1`. -/
theorem tagCheckProgramU_stepConfig_mismatch_phase {L : Nat}
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L)
    {i : Fin (tagLen + 2)} {s : Unit} (hi : i.val < tagLen) (hstate : c.state = ⟨i, s⟩)
    (hmis : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = false) :
    ((TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).state).fst.val = tagLen + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase tagCheckProgramU c hstate]
  simp only [tagCheckProgramU, dif_pos hi, hmis, cond_false]

/-- Idle step (phase `≥ tagLen`, i.e. accept or sink): the phase is unchanged. -/
theorem tagCheckProgramU_stepConfig_idle_phase {L : Nat}
    (c : Configuration (M := tagCheckProgramU.toPhased.toTM) L)
    {i : Fin (tagLen + 2)} {s : Unit} (hi : ¬ i.val < tagLen) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).state).fst.val = i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase tagCheckProgramU c hstate]
  simp only [tagCheckProgramU, dif_neg hi]

/-! ### Unified run invariant and acceptance

After `k ≤ tagLen` steps the tape is unchanged, and the phase is `k` (with head `k`) **iff** the first
`k` input cells matched the tag (`tagMatchPrefix x k`), otherwise it has fallen into the sink phase
`tagLen + 1`.  At `k = tagLen` this gives `accepts ⟺ tagMatchPrefix x tagLen` — the same bit-for-bit
tag-equality characterization as the `Bool` tag-check, now for the `Unit` version. -/
theorem tagCheckProgramU_runConfig_inv {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ tagLen →
      (TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
          (tagCheckProgramU.toPhased.toTM.initialConfig x) k).tape
          = (tagCheckProgramU.toPhased.toTM.initialConfig x).tape
      ∧ (tagMatchPrefix x k = true →
          (((TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
              (tagCheckProgramU.toPhased.toTM.initialConfig x) k).state).fst : Nat) = k
          ∧ ((TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
              (tagCheckProgramU.toPhased.toTM.initialConfig x) k).head : Nat) = k)
      ∧ (tagMatchPrefix x k = false →
          (((TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
              (tagCheckProgramU.toPhased.toTM.initialConfig x) k).state).fst : Nat) = tagLen + 1) := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨rfl, ?_, ?_⟩
      · intro _; exact ⟨rfl, rfl⟩
      · intro h; simp at h
  | succ k ih =>
      intro hk
      obtain ⟨htp, hmc, hmsc⟩ := ih (by omega)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
        (tagCheckProgramU.toPhased.toTM.initialConfig x) k with hc
      have htape_new : (TM.stepConfig (M := tagCheckProgramU.toPhased.toTM) c).tape
          = (tagCheckProgramU.toPhased.toTM.initialConfig x).tape := by
        rw [tagCheckProgramU_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]
      refine ⟨htape_new, ?_, ?_⟩
      · intro hm1
        rw [tagMatchPrefix_succ, Bool.and_eq_true] at hm1
        obtain ⟨hmk, hbiteq⟩ := hm1
        obtain ⟨hphk, hhdk⟩ := hmc hmk
        have hi : (c.state.fst : Nat) < tagLen := by rw [hphk]; omega
        have hbit : c.tape c.head = tagCheckInputBit x k :=
          tagCheckProgramU_tape_read x c k htp hhdk
        have htag : natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩ = tagBitAt k := by
          rw [natBitBE_tag_eq]; exact congrArg tagBitAt hphk
        have hcmp : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩) = true := by
          rw [hbit, htag]; exact hbiteq
        have hbnd : (c.head : Nat) + 1 < tagCheckProgramU.toPhased.toTM.tapeLength L := by
          rw [hhdk]; show k + 1 < L + tagLen + 1; omega
        refine ⟨?_, ?_⟩
        · rw [tagCheckProgramU_stepConfig_match_phase c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp, hphk]
        · rw [tagCheckProgramU_stepConfig_match_head c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp hbnd, hhdk]
      · intro hm0
        rw [tagMatchPrefix_succ] at hm0
        by_cases hmk : tagMatchPrefix x k = true
        · obtain ⟨hphk, hhdk⟩ := hmc hmk
          have hi : (c.state.fst : Nat) < tagLen := by rw [hphk]; omega
          have hbiteq : (tagCheckInputBit x k == tagBitAt k) = false := by
            rw [hmk, Bool.true_and] at hm0; exact hm0
          have hbit : c.tape c.head = tagCheckInputBit x k :=
            tagCheckProgramU_tape_read x c k htp hhdk
          have htag : natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩ = tagBitAt k := by
            rw [natBitBE_tag_eq]; exact congrArg tagBitAt hphk
          have hcmp : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩) = false := by
            rw [hbit, htag]; exact hbiteq
          rw [tagCheckProgramU_stepConfig_mismatch_phase c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp]
        · have hmk' : tagMatchPrefix x k = false := by
            cases h : tagMatchPrefix x k
            · rfl
            · exact absurd h hmk
          have hphk := hmsc hmk'
          have hi : ¬ (c.state.fst : Nat) < tagLen := by rw [hphk]; omega
          rw [tagCheckProgramU_stepConfig_idle_phase c
            (i := c.state.fst) (s := c.state.snd) hi rfl, hphk]

/-- End-to-end correctness of the `Unit` tag-check phase: it accepts iff the first `tagLen` input cells
match `treePrefixTag` bit-for-bit (same characterization as the `Bool` version, reusing
`tagMatchPrefix_eq_true_iff`). -/
theorem tagCheckProgramU_accepts_iff {L : Nat} (x : Boolcube.Point L) :
    TM.accepts (M := tagCheckProgramU.toPhased.toTM) (n := L) x = true
      ↔ ∀ j, j < tagLen → tagCheckInputBit x j = tagBitAt j := by
  obtain ⟨_, hmc, hmsc⟩ := tagCheckProgramU_runConfig_inv x tagLen (Nat.le_refl tagLen)
  have hrun : TM.run (M := tagCheckProgramU.toPhased.toTM) (n := L) x
      = TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
          (tagCheckProgramU.toPhased.toTM.initialConfig x) tagLen := rfl
  rw [← tagMatchPrefix_eq_true_iff]
  unfold TM.accepts
  rw [hrun, decide_eq_true_eq]
  set r := TM.runConfig (M := tagCheckProgramU.toPhased.toTM)
    (tagCheckProgramU.toPhased.toTM.initialConfig x) tagLen with hr
  constructor
  · intro hacc
    have hpv : (r.state.fst : Nat) = tagLen := by rw [hacc]; rfl
    cases hm : tagMatchPrefix x tagLen
    · exfalso; have hsink := hmsc hm; rw [hsink] at hpv; omega
    · rfl
  · intro hm
    obtain ⟨hph, _⟩ := hmc hm
    haveI : Subsingleton (tagCheckProgramU.toPhased.phaseState r.state.fst) :=
      inferInstanceAs (Subsingleton Unit)
    exact Sigma.ext (Fin.ext (hph.trans rfl)) (Subsingleton.helim rfl _ _)

end ContractExpansion
end Frontier
end Pnp4
