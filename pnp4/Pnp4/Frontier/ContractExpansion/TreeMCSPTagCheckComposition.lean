import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckUnit
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Lifting the `Unit` tag check into the P1 region of a composition (NP-verifier track)

The `Unit`-state tag check (`tagCheckProgramU`) is `M`'s **first** phase, so for the native-`Unit`
assembly (`mSkeletonU = seqList [tagCheckProgramU, gammaSelfLoopScan, selfLoopIncrement]`) we must know
how it *runs* when embedded as the first component of a `seq`.  Per the cross-instance caveat
(`TM_VERIFIER_STRATEGY.md` §6a), the standalone `tagCheckProgramU_runConfig_inv` does **not** transfer
to `seq tagCheckProgramU P2` for free — `(seq tagCheckProgramU P2).toTM` has a different
runtime/tape-length/`Configuration` than `tagCheckProgramU.toTM`.  So we re-derive, on the composed
machine, the full tag-check behaviour in P1's *normal* region:

* the transition-level evaluations (match advances, mismatch sinks, sink idles);
* the single-step lemmas through `seq_stepConfig_P1_normal_*` (phase / head / tape);
* the unified P1-region run invariant (phase `= k` iff the first `k` cells match the tag, else it has
  fallen into the sink `tagLen + 1`), the exact analogue of `tagCheckProgramU_runConfig_inv`;
* and its first real consumer — the **P1→P2 handoff**: on a matching tag, after `tagLen + 1` steps
  (`tagLen` to scan the tag, one for the handoff) control jumps to `P2`'s shifted start phase with the
  head resting at `tagLen` and the tape unchanged.

This is the per-instance template already validated for the self-loops (`TreeMCSPScanComposition`,
`TreeMCSPCounterComposition`), now for the multi-phase tag check — closing the documented "transfer the
leading phase's run behaviour into the composition" item for `M`'s first phase.  Builds no verifier and
proves no separation; all surfaces carry only the standard `[propext, Classical.choice, Quot.sound]`
execution triple. -/

/-! ### Transition-level evaluations (on a raw phase index `j : Fin (tagLen + 2)`)

These isolate the `tagCheckProgramU.transition` reductions on a bare `Fin (tagLen + 2)` index, exactly
as in the standalone single-step proofs; the `seq` lemmas below feed them the P1-region index
`⟨i.val, h1⟩` (definitionally a `Fin (tagLen + 2)`). -/

/-- Match: at phase `j < tagLen` with the scanned bit equal to the tag bit, the transition advances the
phase to `j + 1`. -/
theorem tagCheckProgramU_transition_match_phase (j : Fin (tagLen + 2)) (s : Unit) (b : Bool)
    (hj : j.val < tagLen) (hm : (b == natBitBE treePrefixTag tagLen ⟨j.val, hj⟩) = true) :
    (tagCheckProgramU.transition j s b).fst.val = j.val + 1 := by
  simp only [tagCheckProgramU, dif_pos hj, hm, cond_true]

/-- Match: the transition moves the head right. -/
theorem tagCheckProgramU_transition_match_move (j : Fin (tagLen + 2)) (s : Unit) (b : Bool)
    (hj : j.val < tagLen) (hm : (b == natBitBE treePrefixTag tagLen ⟨j.val, hj⟩) = true) :
    (tagCheckProgramU.transition j s b).2.2.2 = Move.right := by
  simp only [tagCheckProgramU, dif_pos hj, hm, cond_true]

/-- Mismatch: at phase `j < tagLen` with the scanned bit differing from the tag bit, the transition
jumps to the sink `tagLen + 1`. -/
theorem tagCheckProgramU_transition_mismatch_phase (j : Fin (tagLen + 2)) (s : Unit) (b : Bool)
    (hj : j.val < tagLen) (hm : (b == natBitBE treePrefixTag tagLen ⟨j.val, hj⟩) = false) :
    (tagCheckProgramU.transition j s b).fst.val = tagLen + 1 := by
  simp only [tagCheckProgramU, dif_pos hj, hm, cond_false]

/-- Idle: at phase `j ≥ tagLen` (accept or sink) the transition leaves the phase unchanged. -/
theorem tagCheckProgramU_transition_idle_phase (j : Fin (tagLen + 2)) (s : Unit) (b : Bool)
    (hj : ¬ j.val < tagLen) :
    (tagCheckProgramU.transition j s b).fst.val = j.val := by
  simp only [tagCheckProgramU, dif_neg hj]

/-! ### Single-step lemmas on `seq tagCheckProgramU P2` (P1's normal region) -/

/-- Match step in the composition (phase `i < tagLen`, scanned bit matches): advance the phase. -/
theorem tagCheckProgramU_seq_stepConfig_match_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩)
    (hmatch : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = true) :
    ((TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).state).fst.val = i.val + 1 := by
  have h1 : i.val < tagCheckProgramU.numPhases := by rw [tagCheckProgramU_numPhases]; omega
  have hne : i.val ≠ tagCheckProgramU.acceptPhase.val := by rw [tagCheckProgramU_acceptPhase_val]; omega
  rw [seq_stepConfig_P1_normal_phase tagCheckProgramU P2 c h1 hne hstate]
  exact tagCheckProgramU_transition_match_phase ⟨i.val, h1⟩ s (c.tape c.head) hi hmatch

/-- Match step: the head advances by one (within tape bounds). -/
theorem tagCheckProgramU_seq_stepConfig_match_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩)
    (hmatch : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = true)
    (hbound : (c.head : Nat) + 1 < (seq tagCheckProgramU P2).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) + 1 := by
  have h1 : i.val < tagCheckProgramU.numPhases := by rw [tagCheckProgramU_numPhases]; omega
  have hne : i.val ≠ tagCheckProgramU.acceptPhase.val := by rw [tagCheckProgramU_acceptPhase_val]; omega
  rw [seq_stepConfig_P1_normal_head tagCheckProgramU P2 c h1 hne hstate,
    tagCheckProgramU_transition_match_move ⟨i.val, h1⟩ s (c.tape c.head) hi hmatch]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Mismatch step (phase `i < tagLen`, scanned bit differs): jump to the sink `tagLen + 1`. -/
theorem tagCheckProgramU_seq_stepConfig_mismatch_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val < tagLen)
    (hstate : c.state = ⟨i, s⟩)
    (hmis : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨i.val, hi⟩) = false) :
    ((TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).state).fst.val = tagLen + 1 := by
  have h1 : i.val < tagCheckProgramU.numPhases := by rw [tagCheckProgramU_numPhases]; omega
  have hne : i.val ≠ tagCheckProgramU.acceptPhase.val := by rw [tagCheckProgramU_acceptPhase_val]; omega
  rw [seq_stepConfig_P1_normal_phase tagCheckProgramU P2 c h1 hne hstate]
  exact tagCheckProgramU_transition_mismatch_phase ⟨i.val, h1⟩ s (c.tape c.head) hi hmis

/-- Sink step (phase `i = tagLen + 1`): the phase is unchanged (it idles in the reject sink). -/
theorem tagCheckProgramU_seq_stepConfig_sink_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val = tagLen + 1)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).state).fst.val = tagLen + 1 := by
  have h1 : i.val < tagCheckProgramU.numPhases := by rw [tagCheckProgramU_numPhases]; omega
  have hne : i.val ≠ tagCheckProgramU.acceptPhase.val := by rw [tagCheckProgramU_acceptPhase_val]; omega
  rw [seq_stepConfig_P1_normal_phase tagCheckProgramU P2 c h1 hne hstate,
    tagCheckProgramU_transition_idle_phase ⟨i.val, h1⟩ s (c.tape c.head) (by show ¬ i.val < tagLen; omega)]
  show i.val = tagLen + 1
  exact hi

/-- Every P1-normal step leaves the tape unchanged (the tag check writes back the scanned bit). -/
theorem tagCheckProgramU_seq_stepConfig_normal_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit}
    (h1 : i.val < tagCheckProgramU.numPhases) (hne : i.val ≠ tagCheckProgramU.acceptPhase.val)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).tape = c.tape := by
  rw [seq_stepConfig_P1_normal_tape tagCheckProgramU P2 c h1 hne hstate,
    tagCheckProgramU_transition_bit ⟨i.val, h1⟩ s (c.tape c.head)]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- The bit read at the head equals the corresponding total input bit when the tape is the composed
machine's initial tape and the head sits at position `k` (the `seq`-machine analogue of
`tagCheckProgramU_tape_read`). -/
theorem tagCheckProgramU_seq_tape_read (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L)
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L) (k : Nat)
    (htp : c.tape = ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x).tape)
    (hhd : (c.head : Nat) = k) :
    c.tape c.head = tagCheckInputBit x k := by
  rw [htp]
  unfold tagCheckInputBit
  by_cases hkL : k < L
  · have hlt : (c.head : Nat) < L := by rw [hhd]; exact hkL
    rw [TM.initial_tape_input (M := (seq tagCheckProgramU P2).toPhased.toTM) x hlt, dif_pos hkL]
    exact congrArg x (Fin.ext hhd)
  · have hge : L ≤ (c.head : Nat) := by rw [hhd]; omega
    rw [TM.initial_tape_blank (M := (seq tagCheckProgramU P2).toPhased.toTM) x hge, dif_neg hkL]

/-! ### Unified P1-region run invariant -/

/-- The tag check's run invariant inside `seq tagCheckProgramU P2`: after `k ≤ tagLen` steps from the
composed machine's initial configuration the tape is unchanged, and the phase is `k` (with head `k`)
**iff** the first `k` input cells match the tag (`tagMatchPrefix x k`), otherwise control has fallen
into the sink phase `tagLen + 1`.  The exact P1-region analogue of `tagCheckProgramU_runConfig_inv`. -/
theorem tagCheckProgramU_seq_runConfig_inv (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ tagLen →
      (TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
          ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) k).tape
          = ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x).tape
      ∧ (tagMatchPrefix x k = true →
          (((TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
              ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) k).state).fst : Nat) = k
          ∧ ((TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
              ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) k).head : Nat) = k)
      ∧ (tagMatchPrefix x k = false →
          (((TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
              ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) k).state).fst : Nat)
              = tagLen + 1) := by
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
      set c := TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
        ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) k with hc
      -- The phase at step `k` is either still scanning (`< tagLen`) or in the sink (`tagLen + 1`),
      -- never exactly `tagLen` (that is the accept/handoff boundary, reached only at `k = tagLen`).
      have hregion : (c.state.fst : Nat) < tagLen ∨ (c.state.fst : Nat) = tagLen + 1 := by
        cases hm : tagMatchPrefix x k with
        | true => obtain ⟨hphk, _⟩ := hmc hm; left; rw [hphk]; omega
        | false => right; exact hmsc hm
      have h1 : (c.state.fst : Nat) < tagCheckProgramU.numPhases := by
        rw [tagCheckProgramU_numPhases]; rcases hregion with h | h <;> omega
      have hnec : (c.state.fst : Nat) ≠ tagCheckProgramU.acceptPhase.val := by
        rw [tagCheckProgramU_acceptPhase_val]; rcases hregion with h | h <;> omega
      have htape_new : (TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).tape
          = ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x).tape := by
        rw [tagCheckProgramU_seq_stepConfig_normal_tape P2 c
          (i := c.state.fst) (s := c.state.snd) h1 hnec rfl, htp]
      refine ⟨htape_new, ?_, ?_⟩
      · intro hm1
        rw [tagMatchPrefix_succ, Bool.and_eq_true] at hm1
        obtain ⟨hmk, hbiteq⟩ := hm1
        obtain ⟨hphk, hhdk⟩ := hmc hmk
        have hi : (c.state.fst : Nat) < tagLen := by rw [hphk]; omega
        have hbit : c.tape c.head = tagCheckInputBit x k :=
          tagCheckProgramU_seq_tape_read P2 x c k htp hhdk
        have htag : natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩ = tagBitAt k := by
          rw [natBitBE_tag_eq]; exact congrArg tagBitAt hphk
        have hcmp : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩) = true := by
          rw [hbit, htag]; exact hbiteq
        have hbnd : (c.head : Nat) + 1 < (seq tagCheckProgramU P2).toPhased.toTM.tapeLength L := by
          rw [hhdk]; show k + 1 < L + (tagLen + P2.timeBound L + 1) + 1; omega
        refine ⟨?_, ?_⟩
        · rw [tagCheckProgramU_seq_stepConfig_match_phase P2 c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp, hphk]
        · rw [tagCheckProgramU_seq_stepConfig_match_head P2 c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp hbnd, hhdk]
      · intro hm0
        rw [tagMatchPrefix_succ] at hm0
        by_cases hmk : tagMatchPrefix x k = true
        · obtain ⟨hphk, hhdk⟩ := hmc hmk
          have hi : (c.state.fst : Nat) < tagLen := by rw [hphk]; omega
          have hbiteq : (tagCheckInputBit x k == tagBitAt k) = false := by
            rw [hmk, Bool.true_and] at hm0; exact hm0
          have hbit : c.tape c.head = tagCheckInputBit x k :=
            tagCheckProgramU_seq_tape_read P2 x c k htp hhdk
          have htag : natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩ = tagBitAt k := by
            rw [natBitBE_tag_eq]; exact congrArg tagBitAt hphk
          have hcmp : (c.tape c.head == natBitBE treePrefixTag tagLen ⟨c.state.fst.val, hi⟩) = false := by
            rw [hbit, htag]; exact hbiteq
          rw [tagCheckProgramU_seq_stepConfig_mismatch_phase P2 c
            (i := c.state.fst) (s := c.state.snd) hi rfl hcmp]
        · have hmk' : tagMatchPrefix x k = false := by
            cases h : tagMatchPrefix x k
            · rfl
            · exact absurd h hmk
          have hphk := hmsc hmk'
          rw [tagCheckProgramU_seq_stepConfig_sink_phase P2 c
            (i := c.state.fst) (s := c.state.snd) hphk rfl]

/-! ### The P1→P2 handoff after the tag matches -/

/-- Handoff step (phase `tagLen` = P1's accept phase): the phase jumps to `P2`'s shifted start. -/
theorem tagCheckProgramU_seq_stepConfig_handoff_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val = tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).state).fst.val
      = (tagLen + 2) + P2.startPhase.val := by
  rw [seq_stepConfig_P1_accept_phase tagCheckProgramU P2 c
      (h1 := by rw [tagCheckProgramU_numPhases, hi]; omega)
      (hacc := by rw [tagCheckProgramU_acceptPhase_val]; exact hi) hstate,
    tagCheckProgramU_numPhases]

/-- Handoff step: the head is unchanged (the handoff stays put). -/
theorem tagCheckProgramU_seq_stepConfig_handoff_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val = tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_accept_head tagCheckProgramU P2 c
      (h1 := by rw [tagCheckProgramU_numPhases, hi]; omega)
      (hacc := by rw [tagCheckProgramU_acceptPhase_val]; exact hi) hstate]

/-- Handoff step: the tape is unchanged. -/
theorem tagCheckProgramU_seq_stepConfig_handoff_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq tagCheckProgramU P2).toPhased.toTM) L)
    {i : Fin (seq tagCheckProgramU P2).numPhases} {s : Unit} (hi : i.val = tagLen)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq tagCheckProgramU P2).toPhased.toTM) c).tape = c.tape := by
  rw [seq_stepConfig_P1_accept_tape tagCheckProgramU P2 c
      (h1 := by rw [tagCheckProgramU_numPhases, hi]; omega)
      (hacc := by rw [tagCheckProgramU_acceptPhase_val]; exact hi) hstate]

/-- Tag-check-then-handoff on the composed machine: on a matching tag, after `tagLen + 1` steps of
`seq tagCheckProgramU P2` (`tagLen` to scan the tag, one for the handoff) control sits at `P2`'s shifted
start phase, the head rests at `tagLen` (just past the tag), and the tape is unchanged.  This is the
complete "tag verified, next phase begins" composition unit — `M`'s tag-check phase handing control to
whatever decodes the gamma payload.  The first real consumer of `tagCheckProgramU_seq_runConfig_inv`. -/
theorem tagCheckProgramU_seq_runConfig_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (hmatch : tagMatchPrefix x tagLen = true) :
    (((TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
        ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) (tagLen + 1)).state).fst : Nat)
        = (tagLen + 2) + P2.startPhase.val
      ∧ ((TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
          ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) (tagLen + 1)).head : Nat) = tagLen
      ∧ (TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
          ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) (tagLen + 1)).tape
          = ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨htp, hmc, _⟩ := tagCheckProgramU_seq_runConfig_inv P2 x tagLen (Nat.le_refl tagLen)
  obtain ⟨hphk, hhdk⟩ := hmc hmatch
  rw [TM.runConfig_succ]
  -- Generalize the `tagLen`-step config to an opaque variable; otherwise the elaborator tries to
  -- whnf the concrete `tagLen = 8`-fold iterate when checking the handoff lemmas' `rfl` state.
  revert htp hphk hhdk
  generalize TM.runConfig (M := (seq tagCheckProgramU P2).toPhased.toTM)
    ((seq tagCheckProgramU P2).toPhased.toTM.initialConfig x) tagLen = c
  intro htp hphk hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact tagCheckProgramU_seq_stepConfig_handoff_phase P2 c
      (i := c.state.fst) (s := c.state.snd) hphk rfl
  · rw [tagCheckProgramU_seq_stepConfig_handoff_head P2 c
      (i := c.state.fst) (s := c.state.snd) hphk rfl]
    exact hhdk
  · rw [tagCheckProgramU_seq_stepConfig_handoff_tape P2 c
      (i := c.state.fst) (s := c.state.snd) hphk rfl]
    exact htp

end ContractExpansion
end Frontier
end Pnp4
