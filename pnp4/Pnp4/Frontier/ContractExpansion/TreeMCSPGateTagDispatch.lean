import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# Gate-tag dispatcher (NP-verifier track — decoder brick D1b, part 1 of 2)

The control core of the one-gate-record on-tape decoder (`TM_VERIFIER_STRATEGY.md` §6k, D1b): read the
self-delimiting **unary tag** `1^t 0` (`t ∈ {0..4}` selects `input/const/notGate/andGate/orGate`) off
the tape and **dispatch** to a per-tag phase — exactly the phase-routing pattern of `tagCheckProgramU`,
specialised to a unary counter with a malformed-tag (`t ≥ 5`) reject sink.

Because the five tags route to five continuations that read *different numbers* of operand fields, the
tag value must reach finite control; so (unlike a `selfLoopScanRightOne` field read, which collapses the
count into head position) the tag is read **cell-by-cell**, one phase per `1`, with the count encoded in
the phase. The dispatch phase `5 + t` then selects the operand-reading continuation (built in part 2).

Phase layout (`numPhases = 11`): `0..4` read the unary tag (phase `i` = "seen `i` ones"); on a `0` at
phase `i` dispatch to phase `5 + i` (tag `= i`); a `1` at phase `4` is a sixth-or-later `1` (`t ≥ 5`,
malformed) routing to the sink phase `10`; phases `5..10` idle. This part proves the dispatcher's run
behaviour (reads `1^t 0` in `t + 1` steps, lands in phase `5 + t`, head advanced `t + 1`, tape
unchanged) and its correspondence to D0's `decodeUnaryField` on the tag field. Operand consumption and
the full `decodeGateRecord` correspondence are part 2.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- Gate-tag dispatcher: reads the unary tag `1^t 0` cell-by-cell, routing to dispatch phase `5 + t`
(`t ∈ {0..4}`) or the malformed sink `10` (`t ≥ 5`). -/
def gateTagDispatch : ConstStatePhasedProgram Unit where
  numPhases := 11
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨5, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h5 : i.val < 5 then
      if b then
        ((if i.val < 4 then ⟨i.val + 1, by omega⟩ else ⟨10, by omega⟩ : Fin 11), (), b, Move.right)
      else
        ((⟨5 + i.val, by omega⟩ : Fin 11), (), b, Move.right)
    else
      (i, (), b, Move.stay)
  timeBound := fun _ => 5

@[simp] theorem gateTagDispatch_timeBound (n : Nat) : gateTagDispatch.timeBound n = 5 := rfl
@[simp] theorem gateTagDispatch_numPhases : gateTagDispatch.numPhases = 11 := rfl
@[simp] theorem gateTagDispatch_startPhase_val : (gateTagDispatch.startPhase : Nat) = 0 := rfl

/-- The dispatcher never moves the head left (it advances right while reading the tag, and idles
otherwise). -/
theorem gateTagDispatch_transition_move (i : Fin 11) (s : Unit) (b : Bool) :
    (gateTagDispatch.transition i s b).2.2.2 ≠ Move.left := by
  unfold gateTagDispatch
  dsimp only
  split_ifs <;> simp

theorem gateTagDispatch_neverMovesLeft : TMNeverMovesLeft (gateTagDispatch.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact gateTagDispatch_transition_move i s b

/-- Every step writes back the scanned bit, so the tape is unchanged. -/
theorem gateTagDispatch_transition_bit (i : Fin 11) (s : Unit) (b : Bool) :
    (gateTagDispatch.transition i s b).2.2.1 = b := by
  unfold gateTagDispatch
  dsimp only
  split_ifs <;> simp

theorem gateTagDispatch_stepConfig_tape {L : Nat}
    (c : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    {i : Fin 11} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := gateTagDispatch.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape gateTagDispatch c hstate,
    gateTagDispatch_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Single-step lemmas -/

/-- Read-`1` step at phase `i < 4`: advance to phase `i + 1`. -/
theorem gateTagDispatch_stepConfig_one_phase {L : Nat}
    (c : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    {i : Fin 11} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateTagDispatch.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateTagDispatch c hstate]
  simp only [gateTagDispatch, dif_pos (show i.val < 5 by omega), hbit, if_true, if_pos hi]

/-- Read-`1` step at phase `i < 4`: advance the head by one. -/
theorem gateTagDispatch_stepConfig_one_head {L : Nat}
    (c : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    {i : Fin 11} {s : Unit} (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true)
    (hbound : (c.head : Nat) + 1 < gateTagDispatch.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateTagDispatch.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateTagDispatch c hstate]
  have hmove : (gateTagDispatch.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp only [gateTagDispatch, dif_pos (show i.val < 5 by omega), hbit, if_true, if_pos hi]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- Read-`0` (terminator) step at phase `i < 5`: dispatch to phase `5 + i` (tag `= i`). -/
theorem gateTagDispatch_stepConfig_term_phase {L : Nat}
    (c : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    {i : Fin 11} {s : Unit} (hi : i.val < 5) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gateTagDispatch.toPhased.toTM) c).state).fst.val = 5 + i.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateTagDispatch c hstate]
  simp [gateTagDispatch, dif_pos hi, hbit]

/-- Read-`0` (terminator) step at phase `i < 5`: advance the head by one (past the terminator). -/
theorem gateTagDispatch_stepConfig_term_head {L : Nat}
    (c : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    {i : Fin 11} {s : Unit} (hi : i.val < 5) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < gateTagDispatch.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateTagDispatch.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateTagDispatch c hstate]
  have hmove : (gateTagDispatch.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp [gateTagDispatch, dif_pos hi, hbit]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-! ### Scanning invariant and dispatch -/

/-- Scanning invariant: from a start `c0` in read phase `0`, if the `j` cells from the head are all `1`
(`j ≤ 4`, in bounds), then after `j` steps the phase is `j`, the head has advanced to `c0.head + j`, and
the tape is unchanged. -/
theorem gateTagDispatch_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ 4 → (c0.head : Nat) + j < gateTagDispatch.toPhased.toTM.tapeLength L →
      (∀ p : Fin (gateTagDispatch.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 j).state).fst : Nat) = j
      ∧ ((TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 j with hc
      have hi4 : (c.state.fst : Nat) < 4 := by rw [hph]; omega
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < gateTagDispatch.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [gateTagDispatch_stepConfig_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl hbit,
          hph]
      · rw [gateTagDispatch_stepConfig_one_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl hbit
          hbnd]
        omega
      · rw [gateTagDispatch_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **Dispatch correctness.** From a start `c0` in read phase `0` whose head sits at a unary tag field
`1^t 0` (`t ≤ 4`: the `t` cells from the head are `1`, cell `c0.head + t` is `0`, all in bounds), after
`t + 1` steps the dispatcher is in phase `5 + t` (tag identified `= t`), the head has advanced to
`c0.head + t + 1` (past the terminator, at the first operand cell), and the tape is unchanged. -/
theorem gateTagDispatch_runConfig_dispatch {L : Nat}
    (c0 : Configuration (M := gateTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (t : Nat) (ht : t ≤ 4)
    (hb : (c0.head : Nat) + t + 1 < gateTagDispatch.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateTagDispatch.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + t → c0.tape p = true)
    (hterm : ∀ p : Fin (gateTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + t → c0.tape p = false) :
    (((TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 (t + 1)).state).fst : Nat) = 5 + t
      ∧ ((TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 (t + 1)).head : Nat)
          = (c0.head : Nat) + t + 1
      ∧ (TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 (t + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := gateTagDispatch_runConfig_scanning c0 hphase t ht (by omega) hones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateTagDispatch.toPhased.toTM) c0 t with hc
  have hi5 : (c.state.fst : Nat) < 5 := by rw [hph]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head (by rw [hhd])
  have hbnd : (c.head : Nat) + 1 < gateTagDispatch.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateTagDispatch_stepConfig_term_phase c (i := c.state.fst) (s := c.state.snd) hi5 rfl hbit,
      hph]
  · rw [gateTagDispatch_stepConfig_term_head c (i := c.state.fst) (s := c.state.snd) hi5 rfl hbit
      hbnd]
    omega
  · rw [gateTagDispatch_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
