import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordDecoder
import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink

/-!
# On-tape gate-record stream decoder (NP-verifier track — decoder brick D2)

The on-tape decoder for a contiguous stream of gate records (`TM_VERIFIER_STRATEGY.md` §6k): loop the
one-record decoder `gateOneRecordDecoder` (D1b) with the head-advancing self-terminating loop
`loopUntilSink`, halting at the decoder's **malformed sink** (phase `13`, reached on a `1^5` tag), which
the stream layout uses as the **end-of-stream marker**.  Each loop pass walks one record and re-enters
at the next record's start; the loop halts when it meets the end marker.

```
gateStreamDecoder := loopUntilSink gateOneRecordDecoder ⟨13⟩
```

This brick ships the **definition** and its **structural** lemmas (phase counts, `neverMovesLeft`
inherited from D1b through the loop combinator).  The run behaviour — discharging `loopUntilSink`'s
`reachesSink` obligations from `gateOneRecordDecoder`'s per-tag traversal (a record advances to accept
`12`) and malformed-sink behaviour (the end marker reaches `13`) on the *composed* machine — is the
documented follow-up, mirroring how the seqP2 lemmas re-derive D1b on a composed machine.

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg; it
builds no verifier and proves no separation.  All surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- The on-tape gate-record stream decoder: the head-advancing loop over the one-record decoder,
halting at its malformed sink (phase `13`), which doubles as the end-of-stream marker. -/
def gateStreamDecoder : ConstStatePhasedProgram Unit :=
  loopUntilSink gateOneRecordDecoder ⟨13, by simp⟩

@[simp] theorem gateStreamDecoder_numPhases : gateStreamDecoder.numPhases = 14 := rfl

@[simp] theorem gateStreamDecoder_startPhase_val : (gateStreamDecoder.startPhase : Nat) = 0 := rfl

@[simp] theorem gateStreamDecoder_acceptPhase_val : (gateStreamDecoder.acceptPhase : Nat) = 13 := rfl

/-- The stream decoder never moves the head left — inherited from `gateOneRecordDecoder` through the
loop combinator (the loop's control steps idle; the body steps are the decoder's, which advance right). -/
theorem gateStreamDecoder_neverMovesLeft : TMNeverMovesLeft (gateStreamDecoder.toPhased.toTM) :=
  loopUntilSink_neverMovesLeft gateOneRecordDecoder ⟨13, by simp⟩
    gateOneRecordDecoder_transition_move

/-- Every step writes back the scanned bit (inherited from D1b through the loop combinator). -/
theorem gateStreamDecoder_transition_bit (i : Fin 14) (s : Unit) (b : Bool) :
    (gateStreamDecoder.transition i s b).2.2.1 = b :=
  loopUntilSink_transition_bit gateOneRecordDecoder ⟨13, by simp⟩
    gateOneRecordDecoder_transition_bit i s b

/-- The stream decoder leaves the tape unchanged each step (it only ever reads). -/
theorem gateStreamDecoder_stepConfig_tape {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape gateStreamDecoder c hstate,
    gateStreamDecoder_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Transition bridge: the stream decoder runs the one-record decoder at body phases

At any phase `< 12` (i.e. not the one-record decoder's accept `12` or its sink `13`), the stream
decoder's transition is exactly the one-record decoder's — the loop only intercepts the accept/sink
phases.  This bridges D1b's transition behaviour onto `gateStreamDecoder`, so its run behaviour can be
re-derived on the composed machine (the `Configuration` types of the two `toTM`s are not defeq, so D1b's
lemmas cannot transfer directly; this bridge re-derives them at the transition level instead). -/
theorem gateStreamDecoder_transition_body (i : Fin 14) (s : Unit) (b : Bool) (hi : i.val < 12) :
    gateStreamDecoder.transition i s b = gateOneRecordDecoder.transition i s b := by
  have h1 : i ≠ gateOneRecordDecoder.acceptPhase :=
    Fin.ne_of_val_ne (by rw [gateOneRecordDecoder_acceptPhase_val]; omega)
  have h2 : i ≠ (⟨13, by simp⟩ : Fin gateOneRecordDecoder.numPhases) :=
    Fin.ne_of_val_ne (by simp; omega)
  exact loopUntilSink_transition_body gateOneRecordDecoder ⟨13, by simp⟩ h1 h2 s b

/-! ### Re-derived single-step lemmas (tag-read phases) via the bridge

Each is the `gateStreamDecoder` analogue of the corresponding `gateOneRecordDecoder` single-step,
obtained by `toTM_stepConfig_*` + the transition bridge + D1b's transition reduction.  These seed the
run-behaviour re-derivation (scanning / dispatch / per-tag traversal) on the composed machine. -/

/-- Tag-read `1` at phase `i < 4`: advance to phase `i + 1`. -/
theorem gateStreamDecoder_stepConfig_tag_one_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]

/-- Tag-read `1` at phase `i < 4`: advance the head by one. -/
theorem gateStreamDecoder_stepConfig_tag_one_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Tag-read `0` at phase `i < 4`: dispatch to operand-entry phase `5 + i`. -/
theorem gateStreamDecoder_stepConfig_tag_zero_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 5 + i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3) with h | h | h | h <;>
    simp [gateOneRecordDecoder, hbit, h]

/-- Tag-read `0` at phase `i < 4`: advance the head by one. -/
theorem gateStreamDecoder_stepConfig_tag_zero_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    simp [gateOneRecordDecoder, dif_pos hi, hbit]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Phase-`4` read `1` (tag `t ≥ 5`): route to the malformed sink `13`. -/
theorem gateStreamDecoder_stepConfig_phase4_one_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 13 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp only [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi, hbit, if_true]

/-- Phase-`4` read `0`: dispatch to the `or` operand-entry phase `10`. -/
theorem gateStreamDecoder_stepConfig_phase4_zero_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 10 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi, hbit]

/-- Phase-`4` step (either bit): advance the head by one. -/
theorem gateStreamDecoder_stepConfig_phase4_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    cases c.tape c.head <;>
      simp [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-! ### Re-derived single-step lemmas (operand-read phases) via the bridge -/

/-- "To-accept" field self-loop `1` step (phases `5/7/9/11`): stay in the same phase. -/
theorem gateStreamDecoder_stepConfig_loopAcc_one {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  rcases hp with h | h | h | h <;> simp [gateOneRecordDecoder, h, hbit]

/-- "To-accept" field self-loop `0` step (phases `5/7/9/11`): exit to accept `12`. -/
theorem gateStreamDecoder_stepConfig_loopAcc_zero {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 12 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  rcases hp with h | h | h | h <;> simp [gateOneRecordDecoder, h, hbit]

/-- Either-bit step at a "to-accept" field phase (`5/7/9/11`): advance the head by one. -/
theorem gateStreamDecoder_stepConfig_loopAcc_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    rcases hp with h | h | h | h <;> cases c.tape c.head <;> simp [gateOneRecordDecoder, h]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `const` literal step (phase `6`): exit to accept `12`. -/
theorem gateStreamDecoder_stepConfig_const_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 12 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, hi]

/-- `const` literal step (phase `6`): advance the head by one. -/
theorem gateStreamDecoder_stepConfig_const_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `and` first-operand self-loop `1` step (phase `8`): stay. -/
theorem gateStreamDecoder_stepConfig_loop8_one {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 8 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `and` first-operand self-loop `0` step (phase `8`): advance to second operand `9`. -/
theorem gateStreamDecoder_stepConfig_loop8_zero {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 9 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `and` first-operand step (phase `8`): advance the head by one. -/
theorem gateStreamDecoder_stepConfig_loop8_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `or` first-operand self-loop `1` step (phase `10`): stay. -/
theorem gateStreamDecoder_stepConfig_loop10_one {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 10 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `or` first-operand self-loop `0` step (phase `10`): advance to second operand `11`. -/
theorem gateStreamDecoder_stepConfig_loop10_zero {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = 11 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `or` first-operand step (phase `10`): advance the head by one. -/
theorem gateStreamDecoder_stepConfig_loop10_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-! ### Re-derived tag-read run invariants (scan / dispatch / malformed) via the single-steps -/

/-- Tag-scan invariant: from phase `0`, `j ≤ 4` leading `1`s ⇒ after `j` steps phase `j`, head `+ j`. -/
theorem gateStreamDecoder_runConfig_tagscan {L : Nat}
    (c0 : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ 4 → (c0.head : Nat) + j < gateStreamDecoder.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 j).state).fst : Nat) = j
      ∧ ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 j with hc
      have hi4 : (c.state.fst : Nat) < 4 := by rw [hph]; omega
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [gateStreamDecoder_stepConfig_tag_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit, hph]
      · rw [gateStreamDecoder_stepConfig_tag_one_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit hbnd]
        omega
      · rw [gateStreamDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- Dispatch (tags `0..3`): `1^t 0` (`t ≤ 3`) ⇒ after `t+1` steps phase `5+t`, head past the terminator. -/
theorem gateStreamDecoder_runConfig_dispatch {L : Nat}
    (c0 : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (t : Nat) (ht : t ≤ 3)
    (hb : (c0.head : Nat) + t + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + t → c0.tape p = true)
    (hterm : ∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + t → c0.tape p = false) :
    (((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 (t + 1)).state).fst : Nat) = 5 + t
      ∧ ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 (t + 1)).head : Nat)
          = (c0.head : Nat) + t + 1
      ∧ (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 (t + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := gateStreamDecoder_runConfig_tagscan c0 hphase t (by omega) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c0 t with hc
  have hi4 : (c.state.fst : Nat) < 4 := by rw [hph]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateStreamDecoder_stepConfig_tag_zero_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit, hph]
  · rw [gateStreamDecoder_stepConfig_tag_zero_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit hbnd]
    omega
  · rw [gateStreamDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
