import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

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

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

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

/-! ### Tag-read behaviour (phases 0..4)

The tag-read prefix behaves exactly as `gateTagDispatch`: a `1` at phase `i < 4` advances to phase
`i + 1` (moving right); after `j ≤ 4` ones the machine is in phase `j` with the head advanced `j`. -/

/-- Read-`1` step at tag-read phase `i < 4`: advance to phase `i + 1`. -/
theorem gateOneRecordDecoder_stepConfig_one_phase {L : Nat}
    (c : Configuration (M := gateOneRecordDecoder.toPhased.toTM) L)
    {i : Fin 14} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateOneRecordDecoder.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateOneRecordDecoder c hstate]
  simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]

/-- Read-`1` step at tag-read phase `i < 4`: advance the head by one. -/
theorem gateOneRecordDecoder_stepConfig_one_head {L : Nat}
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

/-- Tag-read scanning invariant: from a start `c0` in read phase `0`, if the `j` cells from the head are
all `1` (`j ≤ 4`, in bounds), then after `j` steps the phase is `j`, the head has advanced to
`c0.head + j`, and the tape is unchanged. -/
theorem gateOneRecordDecoder_runConfig_scanning {L : Nat}
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
      · rw [gateOneRecordDecoder_stepConfig_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit, hph]
      · rw [gateOneRecordDecoder_stepConfig_one_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl
          hbit hbnd]
        omega
      · rw [gateOneRecordDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
