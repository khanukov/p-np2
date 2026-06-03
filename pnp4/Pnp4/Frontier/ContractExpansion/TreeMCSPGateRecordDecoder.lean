import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout
import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryFieldReader

/-!
# Monolithic one-gate-record on-tape decoder (NP-verifier track — decoder brick D1b, part 2)

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg of
`VerifiedNPDAGLowerBoundSource`; it does not itself reduce a source obligation and is **not**
reportable as `P ≠ NP` mainline progress.

The full one-gate-record decoder: read one gate record `1^t 0 ‹operands›` off the tape (the §6k layout
proved by D0's `decodeGateRecord`), advancing the head to the next record's start. As established while
resolving the D1b-part-1 review (`gateTagDispatch`), the repo's all-`Unit` state-uniformity discipline
(§6a) and `ConstStatePhasedProgram.seq`'s single-phase, state-resetting handoff mean a 5-way tag branch
cannot be `seq`-composed; so the decoder is **one monolithic phase-routed program** with the per-tag
operand reads as **internal self-loop phases**, all converging on a **single common accept phase** (so
the decoder *as a whole* is `seq`-composable into `M`).

Phase layout (`numPhases = 14`, `Unit` state):
* `0..4` — read the unary tag `1^t 0` cell-by-cell (phase `i` = "seen `i` ones"); a `1` at phase `4`
  is a malformed tag (`t ≥ 5`) → sink `13`; a `0` at phase `i` dispatches to the operand-entry phase for
  tag `i`.
* operand reads (each a self-loop over a `1^k 0` field, advancing right): `5` input-index → accept;
  `6` const literal bit (one cell) → accept; `7` not-ref → accept; `8` and-ref1 → `9` and-ref2 → accept;
  `10` or-ref1 → `11` or-ref2 → accept.
* `12` — the common **accept** phase (idle); `13` — malformed **sink** (idle).

This part-2 PR ships the program definition and its **structural** lemmas (`timeBound`, `numPhases`,
never-moves-left, tape-unchanged). The per-tag `runConfig` behaviour and the correspondence to D0's
`decodeGateRecord` (a 5-case proof reusing the `gateTagDispatch` scanning pattern and the D1a unary-field
read) are layered on next.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The monolithic one-gate-record decoder (see the module header for the phase layout). -/
def gateOneRecordDecoder : ConstStatePhasedProgram Unit where
  numPhases := 14
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨12, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h4 : i.val < 4 then
      -- tag read, phases 0..3: a `1` advances; a `0` dispatches on the tag seen so far.
      if b then ((⟨i.val + 1, by omega⟩ : Fin 14), (), b, Move.right)
      else
        (((if i.val = 0 then ⟨5, by omega⟩
           else if i.val = 1 then ⟨6, by omega⟩
           else if i.val = 2 then ⟨7, by omega⟩
           else ⟨8, by omega⟩) : Fin 14), (), b, Move.right)
    else if i.val = 4 then
      -- tag read phase 4: a `1` is a malformed (`t ≥ 5`) tag → sink; a `0` is tag 4 (or) → phase 10.
      if b then ((⟨13, by omega⟩ : Fin 14), (), b, Move.right)
      else ((⟨10, by omega⟩ : Fin 14), (), b, Move.right)
    else if i.val = 6 then
      -- const literal bit: consume one cell → accept.
      ((⟨12, by omega⟩ : Fin 14), (), b, Move.right)
    else if i.val = 8 then
      -- and ref-1 field self-loop: `1` → self, `0` → ref-2 (phase 9).
      if b then ((⟨8, by omega⟩ : Fin 14), (), b, Move.right)
      else ((⟨9, by omega⟩ : Fin 14), (), b, Move.right)
    else if i.val = 10 then
      -- or ref-1 field self-loop: `1` → self, `0` → ref-2 (phase 11).
      if b then ((⟨10, by omega⟩ : Fin 14), (), b, Move.right)
      else ((⟨11, by omega⟩ : Fin 14), (), b, Move.right)
    else if i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11 then
      -- single / last unary field self-loops: `1` → self, `0` → accept (phase 12).
      if b then (i, (), b, Move.right) else ((⟨12, by omega⟩ : Fin 14), (), b, Move.right)
    else
      -- accept (12) and sink (13): idle.
      (i, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem gateOneRecordDecoder_timeBound (n : Nat) :
    gateOneRecordDecoder.timeBound n = n := rfl
@[simp] theorem gateOneRecordDecoder_numPhases : gateOneRecordDecoder.numPhases = 14 := rfl
@[simp] theorem gateOneRecordDecoder_startPhase_val :
    (gateOneRecordDecoder.startPhase : Nat) = 0 := rfl
@[simp] theorem gateOneRecordDecoder_acceptPhase_val :
    (gateOneRecordDecoder.acceptPhase : Nat) = 12 := rfl

/-- The decoder never moves the head left: it advances right while reading the record, and idles
(accept/sink) otherwise. -/
theorem gateOneRecordDecoder_transition_move (i : Fin 14) (s : Unit) (b : Bool) :
    (gateOneRecordDecoder.transition i s b).2.2.2 ≠ Move.left := by
  unfold gateOneRecordDecoder
  dsimp only
  split_ifs <;> simp

theorem gateOneRecordDecoder_neverMovesLeft :
    TMNeverMovesLeft (gateOneRecordDecoder.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact gateOneRecordDecoder_transition_move i s b

/-- Every step writes back the scanned bit. -/
theorem gateOneRecordDecoder_transition_bit (i : Fin 14) (s : Unit) (b : Bool) :
    (gateOneRecordDecoder.transition i s b).2.2.1 = b := by
  unfold gateOneRecordDecoder
  dsimp only
  split_ifs <;> simp

theorem gateOneRecordDecoder_stepConfig_tape {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape gateOneRecordDecoder c hstate,
    gateOneRecordDecoder_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Single-step lemmas — tag-read phases (`0..4`)

These mirror the `gateTagDispatch` single-step lemmas, specialised to the decoder's transition: phases
`0..3` advance on a `1` and dispatch on a `0`; phase `4` routes a `1` to the malformed sink `13` and a
`0` to the `or` operand-entry phase `10`. -/

/-- Tag-read `1` at phase `i < 4`: advance to phase `i + 1`. -/
theorem gateOneRecordDecoder_stepConfig_tag_one_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]

/-- Tag-read `1` at phase `i < 4`: advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_tag_one_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Tag-read `0` at phase `i < 4`: dispatch to operand-entry phase `5 + i` (`= 5/6/7/8` for tags
`0/1/2/3`). -/
theorem gateOneRecordDecoder_stepConfig_tag_zero_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 5 + i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3) with h | h | h | h <;>
    simp [gateOneRecordDecoder, hbit, h]

/-- Tag-read `0` at phase `i < 4`: advance the head by one (past the terminator). -/
theorem gateOneRecordDecoder_stepConfig_tag_zero_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp [gateOneRecordDecoder, dif_pos hi, hbit]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Phase-`4` read `1` (a sixth-or-later `1`, i.e. tag `t ≥ 5`): route to the malformed sink `13`. -/
theorem gateOneRecordDecoder_stepConfig_phase4_one_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 13 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp only [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi, hbit, if_true]

/-- Phase-`4` read `0`: dispatch to the `or` operand-entry phase `10` (tag `4`). -/
theorem gateOneRecordDecoder_stepConfig_phase4_zero_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 10 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi, hbit]

/-- Phase-`4` step (either bit): advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_phase4_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    cases c.tape c.head <;>
      simp [gateOneRecordDecoder, dif_neg (show ¬ i.val < 4 by omega), if_pos hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-! ### Tag-scan invariant and dispatch -/

/-- Scanning invariant for the tag-read phases: from a start `c0` in phase `0`, if the `j` cells from
the head are all `1` (`j ≤ 4`, in bounds), then after `j` steps the phase is `j`, the head has advanced
to `c0.head + j`, and the tape is unchanged. -/
theorem gateOneRecordDecoder_runConfig_tagscan {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ 4 → (c0.head : Nat) + j < gateOneRecordDecoder.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).state).fst : Nat) = j
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j with hc
      have hi4 : (c.state.fst : Nat) < 4 := by rw [hph]; omega
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [gateOneRecordDecoder_stepConfig_tag_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit, hph]
      · rw [gateOneRecordDecoder_stepConfig_tag_one_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit hbnd]
        omega
      · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **Dispatch (tags `0..3`).** From a start `c0` in phase `0` whose head sits at a unary tag `1^t 0`
(`t ≤ 3`), after `t + 1` steps the decoder is at operand-entry phase `5 + t`, the head has advanced past
the terminator, and the tape is unchanged. -/
theorem gateOneRecordDecoder_runConfig_dispatch {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (t : Nat) (ht : t ≤ 3)
    (hb : (c0.head : Nat) + t + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + t → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + t → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (t + 1)).state).fst : Nat) = 5 + t
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (t + 1)).head : Nat)
          = (c0.head : Nat) + t + 1
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (t + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := gateOneRecordDecoder_runConfig_tagscan c0 hphase t (by omega) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 t with hc
  have hi4 : (c.state.fst : Nat) < 4 := by rw [hph]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_tag_zero_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit, hph]
  · rw [gateOneRecordDecoder_stepConfig_tag_zero_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit hbnd]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **Dispatch (tag `4`, `or`).** From phase `0` at a unary tag `1^4 0`, after `5` steps the decoder is
at the `or` operand-entry phase `10`, head advanced past the terminator, tape unchanged. -/
theorem gateOneRecordDecoder_runConfig_dispatch_or {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 4 + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 4 → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 4 → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (4 + 1)).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (4 + 1)).head : Nat)
          = (c0.head : Nat) + 4 + 1
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (4 + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := gateOneRecordDecoder_runConfig_tagscan c0 hphase 4 (by omega) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 4 with hc
  have hi4 : (c.state.fst : Nat) = 4 := by rw [hph]
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_phase4_zero_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit]
  · rw [gateOneRecordDecoder_stepConfig_phase4_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl hbnd]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **Malformed tag.** From phase `0` at `1^5` (five leading `1`s — a tag `t ≥ 5`), after `5` steps the
decoder is in the malformed sink phase `13`. -/
theorem gateOneRecordDecoder_runConfig_malformed {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 4 + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 5 → c0.tape p = true) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (4 + 1)).state).fst : Nat) = 13 := by
  obtain ⟨hph, hhd, htp⟩ := gateOneRecordDecoder_runConfig_tagscan c0 hphase 4 (by omega) (by omega)
    (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 4 with hc
  have hi4 : (c.state.fst : Nat) = 4 := by rw [hph]
  have hbit : c.tape c.head = true := by
    rw [htp]; exact hones c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
  rw [gateOneRecordDecoder_stepConfig_phase4_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
    hbit]

/-! ### Single-step lemmas — operand-read phases (`5..11`)

Phases `5/7/9/11` are the single/last unary-field self-loops (`1` → self, `0` → accept `12`); phase `6`
is the one-cell `const` literal (any bit → accept `12`); phases `8`/`10` are the and/or first-operand
self-loops (`1` → self, `0` → second operand `9`/`11`). -/

/-- Self-loop `1` step at a "to-accept" field phase (`5/7/9/11`): stay in the same phase. -/
theorem gateOneRecordDecoder_stepConfig_loopAcc_one {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  rcases hp with h | h | h | h <;> simp [gateOneRecordDecoder, h, hbit]

/-- Self-loop `0` step at a "to-accept" field phase (`5/7/9/11`): exit to the common accept phase `12`. -/
theorem gateOneRecordDecoder_stepConfig_loopAcc_zero {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 12 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  rcases hp with h | h | h | h <;> simp [gateOneRecordDecoder, h, hbit]

/-- Either-bit step at a "to-accept" field phase (`5/7/9/11`): advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_loopAcc_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit}
    (hp : i.val = 5 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 11) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rcases hp with h | h | h | h <;> cases c.tape c.head <;>
      simp [gateOneRecordDecoder, h]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `const` literal step (phase `6`, either bit): consume one cell, exit to accept `12`. -/
theorem gateOneRecordDecoder_stepConfig_const_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 12 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, hi]

/-- `const` literal step (phase `6`): advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_const_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `and` first-operand self-loop `1` step (phase `8`): stay in phase `8`. -/
theorem gateOneRecordDecoder_stepConfig_loop8_one {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 8 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `and` first-operand self-loop `0` step (phase `8`): advance to the second operand (phase `9`). -/
theorem gateOneRecordDecoder_stepConfig_loop8_zero {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 9 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `and` first-operand step (phase `8`, either bit): advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_loop8_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- `or` first-operand self-loop `1` step (phase `10`): stay in phase `10`. -/
theorem gateOneRecordDecoder_stepConfig_loop10_one {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 10 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `or` first-operand self-loop `0` step (phase `10`): advance to the second operand (phase `11`). -/
theorem gateOneRecordDecoder_stepConfig_loop10_zero {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = 11 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp [gateOneRecordDecoder, hi, hbit]

/-- `or` first-operand step (phase `10`, either bit): advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_loop10_head {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateOneRecordDecoder c hstate]
  have hmove : (gateOneRecordDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    cases c.tape c.head <;> simp [gateOneRecordDecoder, hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-! ### Operand self-loop field invariants

Each operand field is a unary block `1^k 0`.  A "to-accept" field (phases `5/7/9/11`) self-loops over
the `1`s and exits to the common accept phase `12`; the and/or first-operand fields (phases `8`/`10`)
exit to the second-operand phase `9`/`11`.  All advance the head past the terminator. -/

/-- **To-accept field read** (phases `5/7/9/11`). From a start `c0` at one of these phases whose head
sits at a unary field `1^k 0`, after `k + 1` steps the decoder is at the common accept phase `12`, the
head has advanced past the terminator, and the tape is unchanged. -/
theorem gateOneRecordDecoder_runConfig_field_acc {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hp : (c0.state.fst : Nat) = 5 ∨ (c0.state.fst : Nat) = 7 ∨ (c0.state.fst : Nat) = 9
        ∨ (c0.state.fst : Nat) = 11) (k : Nat)
    (hb : (c0.head : Nat) + k + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + k → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).head : Nat)
          = (c0.head : Nat) + k + 1
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).tape = c0.tape := by
  have scan : ∀ j : Nat, j ≤ k →
      (c0.head : Nat) + j < gateOneRecordDecoder.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).state).fst : Nat)
          = (c0.state.fst : Nat)
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).tape = c0.tape := by
    intro j
    induction j with
    | zero => intro _ _ _; exact ⟨rfl, by simp, rfl⟩
    | succ j ih =>
        intro hj hbnd h1
        obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p a b => h1 p a (by omega))
        rw [TM.runConfig_succ]
        set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j with hc
        have hpp : (c.state.fst : Nat) = 5 ∨ (c.state.fst : Nat) = 7 ∨ (c.state.fst : Nat) = 9
            ∨ (c.state.fst : Nat) = 11 := by rw [hph]; exact hp
        have hbit : c.tape c.head = true := by
          rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
        have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by
          rw [hhd]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [gateOneRecordDecoder_stepConfig_loopAcc_one c (i := c.state.fst) (s := c.state.snd) hpp rfl
            hbit, hph]
        · rw [gateOneRecordDecoder_stepConfig_loopAcc_head c (i := c.state.fst) (s := c.state.snd) hpp rfl
            hbnd1]
          omega
        · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]
  obtain ⟨hph, hhd, htp⟩ := scan k (le_refl k) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 k with hc
  have hpp : (c.state.fst : Nat) = 5 ∨ (c.state.fst : Nat) = 7 ∨ (c.state.fst : Nat) = 9
      ∨ (c.state.fst : Nat) = 11 := by rw [hph]; exact hp
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_loopAcc_zero c (i := c.state.fst) (s := c.state.snd) hpp rfl hbit]
  · rw [gateOneRecordDecoder_stepConfig_loopAcc_head c (i := c.state.fst) (s := c.state.snd) hpp rfl
      hbnd1]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **`and` first-operand field read** (phase `8`). From phase `8` at `1^k 0`, after `k + 1` steps the
decoder is at the second-operand phase `9`, head advanced past the terminator, tape unchanged. -/
theorem gateOneRecordDecoder_runConfig_field8 {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hp : (c0.state.fst : Nat) = 8) (k : Nat)
    (hb : (c0.head : Nat) + k + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + k → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).state).fst : Nat) = 9
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).head : Nat)
          = (c0.head : Nat) + k + 1
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).tape = c0.tape := by
  have scan : ∀ j : Nat, j ≤ k →
      (c0.head : Nat) + j < gateOneRecordDecoder.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).state).fst : Nat) = 8
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).tape = c0.tape := by
    intro j
    induction j with
    | zero => intro _ _ _; exact ⟨hp, by simp, rfl⟩
    | succ j ih =>
        intro hj hbnd h1
        obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p a b => h1 p a (by omega))
        rw [TM.runConfig_succ]
        set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j with hc
        have hbit : c.tape c.head = true := by
          rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
        have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by
          rw [hhd]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [gateOneRecordDecoder_stepConfig_loop8_one c (i := c.state.fst) (s := c.state.snd) hph rfl
            hbit]
        · rw [gateOneRecordDecoder_stepConfig_loop8_head c (i := c.state.fst) (s := c.state.snd) hph rfl
            hbnd1]
          omega
        · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]
  obtain ⟨hph, hhd, htp⟩ := scan k (le_refl k) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 k with hc
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_loop8_zero c (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
  · rw [gateOneRecordDecoder_stepConfig_loop8_head c (i := c.state.fst) (s := c.state.snd) hph rfl hbnd1]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **`or` first-operand field read** (phase `10`). From phase `10` at `1^k 0`, after `k + 1` steps the
decoder is at the second-operand phase `11`, head advanced past the terminator, tape unchanged. -/
theorem gateOneRecordDecoder_runConfig_field10 {L : Nat}
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hp : (c0.state.fst : Nat) = 10) (k : Nat)
    (hb : (c0.head : Nat) + k + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + k → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).state).fst : Nat) = 11
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).head : Nat)
          = (c0.head : Nat) + k + 1
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (k + 1)).tape = c0.tape := by
  have scan : ∀ j : Nat, j ≤ k →
      (c0.head : Nat) + j < gateOneRecordDecoder.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j).tape = c0.tape := by
    intro j
    induction j with
    | zero => intro _ _ _; exact ⟨hp, by simp, rfl⟩
    | succ j ih =>
        intro hj hbnd h1
        obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p a b => h1 p a (by omega))
        rw [TM.runConfig_succ]
        set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 j with hc
        have hbit : c.tape c.head = true := by
          rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
        have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by
          rw [hhd]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [gateOneRecordDecoder_stepConfig_loop10_one c (i := c.state.fst) (s := c.state.snd) hph rfl
            hbit]
        · rw [gateOneRecordDecoder_stepConfig_loop10_head c (i := c.state.fst) (s := c.state.snd) hph rfl
            hbnd1]
          omega
        · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]
  obtain ⟨hph, hhd, htp⟩ := scan k (le_refl k) (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 k with hc
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd1 : (c.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_loop10_zero c (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
  · rw [gateOneRecordDecoder_stepConfig_loop10_head c (i := c.state.fst) (s := c.state.snd) hph rfl
      hbnd1]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-! ### Per-tag full-record traversal

Each lemma takes a start `c0` in phase `0` whose tape holds `encodeGateRecord g` from the head, and
concludes that after `gateRecordSize g` steps the decoder reaches the common accept phase `12`, the head
has advanced to the next record's start (`c0.head + gateRecordSize g`), and the tape is unchanged.  The
record's bit pattern is supplied as per-field cell predicates (the form the dispatch/field invariants
consume); the `decodeGateRecord` correspondence is layered on top in the next section. -/

/-- `input idx` (tag `0`): record `1^0 0 · 1^idx 0` (a `0` tag terminator then the index field). -/
theorem gateOneRecordDecoder_runConfig_input {L : Nat} {n : Nat} (idx : Fin n)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.input idx)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htag : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + idx.val → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + idx.val → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
        (gateRecordSize (SLGate.input idx))).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.input idx))).head : Nat)
          = (c0.head : Nat) + gateRecordSize (SLGate.input idx)
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.input idx))).tape = c0.tape := by
  have hsz : gateRecordSize (SLGate.input idx) = (0 + 1) + (idx.val + 1) := by
    simp only [gateRecordSize]; omega
  rw [hsz] at hb ⊢
  obtain ⟨hph1, hhd1, htp1⟩ := gateOneRecordDecoder_runConfig_dispatch c0 hphase 0 (by omega)
    (by omega) (fun p ha hb' => absurd hb' (by omega)) (fun p hp => htag p (by omega))
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (0 + 1) = c1
  intro hph1 hhd1 htp1
  obtain ⟨hph2, hhd2, htp2⟩ := gateOneRecordDecoder_runConfig_field_acc c1
    (Or.inl (by rw [hph1])) idx.val (by rw [hhd1]; omega)
    (by intro p hp1 hp2; rw [htp1]; rw [hhd1] at hp1 hp2; exact hones p (by omega) (by omega))
    (by intro p hp1; rw [htp1]; rw [hhd1] at hp1; exact hterm p (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [hph2]
  · rw [hhd2, hhd1]; omega
  · rw [htp2, htp1]

/-- `const b` (tag `1`): record `1^1 0 · b` (a unary tag `1`, then one literal bit, value unconstrained). -/
theorem gateOneRecordDecoder_runConfig_const {L : Nat} (b : Bool)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.const (n := 0) b)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hone : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
        (gateRecordSize (SLGate.const (n := 0) b))).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.const (n := 0) b))).head : Nat)
          = (c0.head : Nat) + gateRecordSize (SLGate.const (n := 0) b)
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.const (n := 0) b))).tape = c0.tape := by
  have hsz : gateRecordSize (SLGate.const (n := 0) b) = (1 + 1) + 1 := by
    simp only [gateRecordSize]
  rw [hsz] at hb ⊢
  obtain ⟨hph1, hhd1, htp1⟩ := gateOneRecordDecoder_runConfig_dispatch c0 hphase 1 (by omega)
    (by omega) hone hterm
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (1 + 1) = c1
  intro hph1 hhd1 htp1
  rw [TM.runConfig_one]
  have hi6 : (c1.state.fst : Nat) = 6 := by rw [hph1]
  have hbnd : (c1.head : Nat) + 1 < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by
    rw [hhd1]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateOneRecordDecoder_stepConfig_const_phase c1 (i := c1.state.fst) (s := c1.state.snd) hi6 rfl]
  · rw [gateOneRecordDecoder_stepConfig_const_head c1 (i := c1.state.fst) (s := c1.state.snd) hi6 rfl
      hbnd]
    omega
  · rw [gateOneRecordDecoder_stepConfig_tape c1 (i := c1.state.fst) (s := c1.state.snd) rfl, htp1]

/-- `notGate k` (tag `2`): record `1^2 0 · 1^k 0`. -/
theorem gateOneRecordDecoder_runConfig_not {L : Nat} (k : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.notGate (n := 0) k)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 2 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false)
    (hrefones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 3 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 3 + k → c0.tape p = true)
    (hrefterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 3 + k → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
        (gateRecordSize (SLGate.notGate (n := 0) k))).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.notGate (n := 0) k))).head : Nat)
          = (c0.head : Nat) + gateRecordSize (SLGate.notGate (n := 0) k)
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.notGate (n := 0) k))).tape = c0.tape := by
  have hsz : gateRecordSize (SLGate.notGate (n := 0) k) = (2 + 1) + (k + 1) := by
    simp only [gateRecordSize]; omega
  rw [hsz] at hb ⊢
  obtain ⟨hph1, hhd1, htp1⟩ := gateOneRecordDecoder_runConfig_dispatch c0 hphase 2 (by omega)
    (by omega) htagones htagterm
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (2 + 1) = c1
  intro hph1 hhd1 htp1
  obtain ⟨hph2, hhd2, htp2⟩ := gateOneRecordDecoder_runConfig_field_acc c1
    (Or.inr (Or.inl (by rw [hph1]))) k (by rw [hhd1]; omega)
    (by intro p hp1 hp2; rw [htp1]; rw [hhd1] at hp1 hp2; exact hrefones p (by omega) (by omega))
    (by intro p hp1; rw [htp1]; rw [hhd1] at hp1; exact hrefterm p (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [hph2]
  · rw [hhd2, hhd1]; omega
  · rw [htp2, htp1]

/-- `andGate k l` (tag `3`): record `1^3 0 · 1^k 0 · 1^l 0`. -/
theorem gateOneRecordDecoder_runConfig_and {L : Nat} (k l : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.andGate (n := 0) k l)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 3 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 3 → c0.tape p = false)
    (href1ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 4 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 4 + k → c0.tape p = true)
    (href1term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 4 + k → c0.tape p = false)
    (href2ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 5 + k ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 5 + k + l → c0.tape p = true)
    (href2term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 5 + k + l → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
        (gateRecordSize (SLGate.andGate (n := 0) k l))).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.andGate (n := 0) k l))).head : Nat)
          = (c0.head : Nat) + gateRecordSize (SLGate.andGate (n := 0) k l)
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.andGate (n := 0) k l))).tape = c0.tape := by
  have hsz : gateRecordSize (SLGate.andGate (n := 0) k l) = (3 + 1) + ((k + 1) + (l + 1)) := by
    simp only [gateRecordSize]; omega
  rw [hsz] at hb ⊢
  obtain ⟨hph1, hhd1, htp1⟩ := gateOneRecordDecoder_runConfig_dispatch c0 hphase 3 (by omega)
    (by omega) htagones htagterm
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (3 + 1) = c1
  intro hph1 hhd1 htp1
  obtain ⟨hph2, hhd2, htp2⟩ := gateOneRecordDecoder_runConfig_field8 c1 (by rw [hph1]) k
    (by rw [hhd1]; omega)
    (by intro p hp1 hp2; rw [htp1]; rw [hhd1] at hp1 hp2; exact href1ones p (by omega) (by omega))
    (by intro p hp1; rw [htp1]; rw [hhd1] at hp1; exact href1term p (by omega))
  rw [TM.runConfig_add]
  revert hph2 hhd2 htp2
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c1 (k + 1) = c2
  intro hph2 hhd2 htp2
  obtain ⟨hph3, hhd3, htp3⟩ := gateOneRecordDecoder_runConfig_field_acc c2
    (Or.inr (Or.inr (Or.inl hph2))) l (by rw [hhd2, hhd1]; omega)
    (by intro p hp1 hp2; rw [htp2, htp1]; rw [hhd2, hhd1] at hp1 hp2;
        exact href2ones p (by omega) (by omega))
    (by intro p hp1; rw [htp2, htp1]; rw [hhd2, hhd1] at hp1; exact href2term p (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [hph3]
  · rw [hhd3, hhd2, hhd1]; omega
  · rw [htp3, htp2, htp1]

/-- `orGate k l` (tag `4`): record `1^4 0 · 1^k 0 · 1^l 0`. -/
theorem gateOneRecordDecoder_runConfig_or {L : Nat} (k l : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.orGate (n := 0) k l)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 4 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 4 → c0.tape p = false)
    (href1ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 5 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 5 + k → c0.tape p = true)
    (href1term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 5 + k → c0.tape p = false)
    (href2ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 6 + k ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 6 + k + l → c0.tape p = true)
    (href2term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 6 + k + l → c0.tape p = false) :
    (((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
        (gateRecordSize (SLGate.orGate (n := 0) k l))).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.orGate (n := 0) k l))).head : Nat)
          = (c0.head : Nat) + gateRecordSize (SLGate.orGate (n := 0) k l)
      ∧ (TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0
          (gateRecordSize (SLGate.orGate (n := 0) k l))).tape = c0.tape := by
  have hsz : gateRecordSize (SLGate.orGate (n := 0) k l) = (4 + 1) + ((k + 1) + (l + 1)) := by
    simp only [gateRecordSize]; omega
  rw [hsz] at hb ⊢
  obtain ⟨hph1, hhd1, htp1⟩ := gateOneRecordDecoder_runConfig_dispatch_or c0 hphase (by omega)
    htagones htagterm
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c0 (4 + 1) = c1
  intro hph1 hhd1 htp1
  obtain ⟨hph2, hhd2, htp2⟩ := gateOneRecordDecoder_runConfig_field10 c1 (by rw [hph1]) k
    (by rw [hhd1]; omega)
    (by intro p hp1 hp2; rw [htp1]; rw [hhd1] at hp1 hp2; exact href1ones p (by omega) (by omega))
    (by intro p hp1; rw [htp1]; rw [hhd1] at hp1; exact href1term p (by omega))
  rw [TM.runConfig_add]
  revert hph2 hhd2 htp2
  generalize TM.runConfig (M := gateOneRecordDecoder.toPhased.toTM) c1 (k + 1) = c2
  intro hph2 hhd2 htp2
  obtain ⟨hph3, hhd3, htp3⟩ := gateOneRecordDecoder_runConfig_field_acc c2
    (Or.inr (Or.inr (Or.inr hph2))) l (by rw [hhd2, hhd1]; omega)
    (by intro p hp1 hp2; rw [htp2, htp1]; rw [hhd2, hhd1] at hp1 hp2;
        exact href2ones p (by omega) (by omega))
    (by intro p hp1; rw [htp2, htp1]; rw [hhd2, hhd1] at hp1; exact href2term p (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [hph3]
  · rw [hhd3, hhd2, hhd1]; omega
  · rw [htp3, htp2, htp1]

/-! ### Correspondence to the D0 spec `decodeGateRecord`

The bits the decoder traverses over a record region equal `encodeGateRecord g` (via the D1a tape↔list
bridge `tapeReadList_eq_unaryField` applied per field), hence decode back to `g` by the D0 round-trip
`decodeGateRecord_encodeGateRecord`.  This is the D1b deliverable: the on-tape traversal realises the
D0 spec for the gate it identifies. -/

/-- Splitting a tape read across a concatenation of lengths. -/
theorem tapeReadList_add {M : TM} {L : Nat} (c : Configuration (M := M) L) (h a b : Nat) :
    tapeReadList c h (a + b) = tapeReadList c h a ++ tapeReadList c (h + a) b := by
  induction a generalizing h with
  | zero => simp [tapeReadList]
  | succ a ih =>
      rw [show (a + 1) + b = (a + b) + 1 from by omega, tapeReadList_succ, ih (h + 1),
        tapeReadList_succ c h a, List.cons_append, show h + (a + 1) = h + 1 + a from by omega]

/-- `input idx` (tag `0`): the traversed bits decode to `input idx`. -/
theorem gateOneRecordDecoder_decodes_input {L : Nat} {n : Nat} (idx : Fin n)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.input idx)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htag : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (hones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + idx.val → c0.tape p = true)
    (hterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + idx.val → c0.tape p = false) :
    decodeGateRecord n (tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.input idx)))
      = some (SLGate.input idx, []) := by
  simp only [gateRecordSize] at hb
  have htape : tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.input idx))
      = encodeGateRecord (SLGate.input idx) := by
    rw [show gateRecordSize (SLGate.input idx) = (0 + 1) + (idx.val + 1) from by
        simp only [gateRecordSize]; omega, tapeReadList_add,
      tapeReadList_eq_unaryField c0 (c0.head : Nat) 0 (by omega)
        (fun p ha hb' => absurd hb' (by omega)) (fun p hp => htag p (by omega)),
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (0 + 1)) idx.val (by omega)
        (fun p ha hb' => hones p (by omega) (by omega)) (fun p hp => hterm p (by omega))]
    simp [encodeGateRecord]
  rw [htape]
  simpa using decodeGateRecord_encodeGateRecord (n := n) (SLGate.input idx) []

/-- `notGate k` (tag `2`): the traversed bits decode to `notGate k`. -/
theorem gateOneRecordDecoder_decodes_not {L : Nat} {n : Nat} (k : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.notGate (n := n) k)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 2 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false)
    (hrefones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 3 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 3 + k → c0.tape p = true)
    (hrefterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 3 + k → c0.tape p = false) :
    decodeGateRecord n (tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.notGate (n := n) k)))
      = some (SLGate.notGate k, []) := by
  simp only [gateRecordSize] at hb
  have htape : tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.notGate (n := n) k))
      = encodeGateRecord (SLGate.notGate (n := n) k) := by
    rw [show gateRecordSize (SLGate.notGate (n := n) k) = (2 + 1) + (k + 1) from by
        simp only [gateRecordSize]; omega, tapeReadList_add,
      tapeReadList_eq_unaryField c0 (c0.head : Nat) 2 (by omega)
        (fun p ha hb' => htagones p (by omega) (by omega)) (fun p hp => htagterm p (by omega)),
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (2 + 1)) k (by omega)
        (fun p ha hb' => hrefones p (by omega) (by omega)) (fun p hp => hrefterm p (by omega))]
    simp [encodeGateRecord]
  rw [htape]
  simpa using decodeGateRecord_encodeGateRecord (n := n) (SLGate.notGate k) []

/-- `andGate k l` (tag `3`): the traversed bits decode to `andGate k l`. -/
theorem gateOneRecordDecoder_decodes_and {L : Nat} {n : Nat} (k l : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.andGate (n := n) k l)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 3 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 3 → c0.tape p = false)
    (href1ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 4 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 4 + k → c0.tape p = true)
    (href1term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 4 + k → c0.tape p = false)
    (href2ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 5 + k ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 5 + k + l → c0.tape p = true)
    (href2term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 5 + k + l → c0.tape p = false) :
    decodeGateRecord n (tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.andGate (n := n) k l)))
      = some (SLGate.andGate k l, []) := by
  simp only [gateRecordSize] at hb
  have htape : tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.andGate (n := n) k l))
      = encodeGateRecord (SLGate.andGate (n := n) k l) := by
    rw [show gateRecordSize (SLGate.andGate (n := n) k l) = (3 + 1) + ((k + 1) + (l + 1)) from by
        simp only [gateRecordSize]; omega, tapeReadList_add,
      tapeReadList_eq_unaryField c0 (c0.head : Nat) 3 (by omega)
        (fun p ha hb' => htagones p (by omega) (by omega)) (fun p hp => htagterm p (by omega)),
      tapeReadList_add,
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (3 + 1)) k (by omega)
        (fun p ha hb' => href1ones p (by omega) (by omega)) (fun p hp => href1term p (by omega)),
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (3 + 1) + (k + 1)) l (by omega)
        (fun p ha hb' => href2ones p (by omega) (by omega)) (fun p hp => href2term p (by omega))]
    simp [encodeGateRecord]
  rw [htape]
  simpa using decodeGateRecord_encodeGateRecord (n := n) (SLGate.andGate k l) []

/-- `orGate k l` (tag `4`): the traversed bits decode to `orGate k l`. -/
theorem gateOneRecordDecoder_decodes_or {L : Nat} {n : Nat} (k l : Nat)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.orGate (n := n) k l)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (htagones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 4 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 4 → c0.tape p = false)
    (href1ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 5 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 5 + k → c0.tape p = true)
    (href1term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 5 + k → c0.tape p = false)
    (href2ones : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 6 + k ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 6 + k + l → c0.tape p = true)
    (href2term : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 6 + k + l → c0.tape p = false) :
    decodeGateRecord n (tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.orGate (n := n) k l)))
      = some (SLGate.orGate k l, []) := by
  simp only [gateRecordSize] at hb
  have htape : tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.orGate (n := n) k l))
      = encodeGateRecord (SLGate.orGate (n := n) k l) := by
    rw [show gateRecordSize (SLGate.orGate (n := n) k l) = (4 + 1) + ((k + 1) + (l + 1)) from by
        simp only [gateRecordSize]; omega, tapeReadList_add,
      tapeReadList_eq_unaryField c0 (c0.head : Nat) 4 (by omega)
        (fun p ha hb' => htagones p (by omega) (by omega)) (fun p hp => htagterm p (by omega)),
      tapeReadList_add,
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (4 + 1)) k (by omega)
        (fun p ha hb' => href1ones p (by omega) (by omega)) (fun p hp => href1term p (by omega)),
      tapeReadList_eq_unaryField c0 ((c0.head : Nat) + (4 + 1) + (k + 1)) l (by omega)
        (fun p ha hb' => href2ones p (by omega) (by omega)) (fun p hp => href2term p (by omega))]
    simp [encodeGateRecord]
  rw [htape]
  simpa using decodeGateRecord_encodeGateRecord (n := n) (SLGate.orGate k l) []

/-- `const b` (tag `1`): the traversed bits decode to `const b` (the literal cell at `head + 2`). -/
theorem gateOneRecordDecoder_decodes_const {L : Nat} {n : Nat} (b : Bool)
    (c0 : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    (hb : (c0.head : Nat) + gateRecordSize (SLGate.const (n := n) b)
        < gateOneRecordDecoder.toPhased.toTM.tapeLength L)
    (hone : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 → c0.tape p = true)
    (htagterm : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (hbit : ∀ p : Fin (gateOneRecordDecoder.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = b) :
    decodeGateRecord n (tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.const (n := n) b)))
      = some (SLGate.const b, []) := by
  simp only [gateRecordSize] at hb
  have hlt : (c0.head : Nat) + (1 + 1) < gateOneRecordDecoder.toPhased.toTM.tapeLength L := by omega
  have htape : tapeReadList c0 (c0.head : Nat) (gateRecordSize (SLGate.const (n := n) b))
      = encodeGateRecord (SLGate.const (n := n) b) := by
    rw [show gateRecordSize (SLGate.const (n := n) b) = (1 + 1) + (0 + 1) from by
        simp only [gateRecordSize], tapeReadList_add,
      tapeReadList_eq_unaryField c0 (c0.head : Nat) 1 (by omega)
        (fun p ha hb' => hone p (by omega) (by omega)) (fun p hp => htagterm p (by omega)),
      tapeReadList_succ c0 ((c0.head : Nat) + (1 + 1)) 0, dif_pos hlt,
      hbit ⟨(c0.head : Nat) + (1 + 1), hlt⟩ (by simp)]
    simp [tapeReadList, encodeGateRecord]
  rw [htape]
  simpa using decodeGateRecord_encodeGateRecord (n := n) (SLGate.const b) []

end ContractExpansion
end Frontier
end Pnp4
