import Pnp4.Frontier.ContractExpansion.TreeMCSPCountdownLeft

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Bounded body-reentry loop combinator (NP-verifier track — the back-edge control structure)

`TM_VERIFIER_STRATEGY.md` §6c identifies the bounded body-reentry loop as the shared bottleneck for the
remaining data-dependent items.  Its counter half is built (`selfLoopCountdownLeft`); this module builds
the **control half** — a combinator `repeatBody B` that wraps a body program `B` with a *conditional
back-edge*: after each pass through `B` it inspects the cell under the head (the unary-counter control
cell) and either consumes one tick and re-enters `B`, or — on a `0` — halts.  This is the first
construct in the toolkit with a genuine **back-edge** to a *multi-phase* body (the self-loops back-edge
only to a single phase); the phased model permits it because a transition may target any phase.

This brick ships the combinator **definition** and the **single-step characterization of its loop
control** (the decide phase's consume/halt steps and the `B`-accept→decide handoff) — the novel
back-edge mechanism.  Per the toolkit's own pattern (`seq`'s single-step lemmas were a brick before its
run-invariants), the `B`-region run-through and the run-`K`-times correctness (an induction over the
counter value, with a head-preserving-body hypothesis — §6c option 1) are the documented follow-up.
The `timeBound` is provisional (a placeholder pending the run-correctness brick that pins the tight
`K·(body + 1)` bound); it affects only `tapeLength`, not the single-step lemmas below, which are
unconditionally true.  Builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple. -/

/-- Bounded body-reentry loop over a body `B`.  Phases `[0, B.numPhases)` run `B` (its accept phase
redirected to the decide phase); phase `B.numPhases` is the **decide** phase: reading a `1` (a unary
counter tick under the head) consumes it (writes `0`, moves left) and re-enters `B` at its start phase;
reading a `0` halts (the decide phase is the accept phase).  The conditional back-edge `decide → B.start`
is the loop. -/
def repeatBody (B : ConstStatePhasedProgram Unit) : ConstStatePhasedProgram Unit where
  numPhases := B.numPhases + 1
  startPhase := ⟨B.startPhase.val, by have := B.startPhase.isLt; omega⟩
  startState := ()
  acceptPhase := ⟨B.numPhases, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h : i.val < B.numPhases then
      if i.val = B.acceptPhase.val then
        (⟨B.numPhases, by omega⟩, (), b, Move.stay)
      else
        let r := B.transition ⟨i.val, h⟩ () b
        (⟨r.fst.val, by have := r.fst.isLt; omega⟩, (), r.2.2.1, r.2.2.2)
    else
      if b then
        (⟨B.startPhase.val, by have := B.startPhase.isLt; omega⟩, (), false, Move.left)
      else
        (⟨B.numPhases, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem repeatBody_numPhases (B : ConstStatePhasedProgram Unit) :
    (repeatBody B).numPhases = B.numPhases + 1 := rfl

@[simp] theorem repeatBody_startPhase_val (B : ConstStatePhasedProgram Unit) :
    ((repeatBody B).startPhase : Nat) = B.startPhase.val := rfl

@[simp] theorem repeatBody_acceptPhase_val (B : ConstStatePhasedProgram Unit) :
    ((repeatBody B).acceptPhase : Nat) = B.numPhases := rfl

/-! ### Single-step lemmas for the loop control (the decide phase + the handoff) -/

/-- Decide step, counter nonzero (bit `1`): consume one tick and re-enter `B` — the phase jumps to
`B.startPhase` (the conditional back-edge). -/
theorem repeatBody_stepConfig_consume_phase (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit} (hi : i.val = B.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).state).fst.val = B.startPhase.val := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (repeatBody B) c hstate]
  simp [repeatBody, dif_neg (show ¬ (i.val < B.numPhases) by omega), hbit]

/-- Decide step, counter nonzero (bit `1`): the head moves left (the countdown progresses). -/
theorem repeatBody_stepConfig_consume_head (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit} (hi : i.val = B.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (repeatBody B) c hstate]
  have hmove : ((repeatBody B).transition i s (c.tape c.head)).2.2.2 = Move.left := by
    simp [repeatBody, dif_neg (show ¬ (i.val < B.numPhases) by omega), hbit]
  rw [hmove]

/-- Decide step, counter nonzero (bit `1`): the consumed tick is overwritten with `0`. -/
theorem repeatBody_stepConfig_consume_tape (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit} (hi : i.val = B.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).tape = c.write c.head false := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (repeatBody B) c hstate]
  have hbitw : ((repeatBody B).transition i s (c.tape c.head)).2.2.1 = false := by
    simp [repeatBody, dif_neg (show ¬ (i.val < B.numPhases) by omega), hbit]
  rw [hbitw]

/-- Decide step, counter empty (bit `0`): the phase is unchanged (the loop halts in the decide /
accept phase `B.numPhases`). -/
theorem repeatBody_stepConfig_halt_phase (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit} (hi : i.val = B.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).state).fst.val = B.numPhases := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (repeatBody B) c hstate]
  simp [repeatBody, dif_neg (show ¬ (i.val < B.numPhases) by omega), hbit]

/-- Decide step, counter empty (bit `0`): the head stays put. -/
theorem repeatBody_stepConfig_halt_head (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit} (hi : i.val = B.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).head = c.head := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (repeatBody B) c hstate]
  have hmove : ((repeatBody B).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
    simp [repeatBody, dif_neg (show ¬ (i.val < B.numPhases) by omega), hbit]
  rw [hmove]
  simp [Configuration.moveHead]

/-- Handoff step (`B`'s accept phase, inside `[0, B.numPhases)`): one step jumps to the decide phase
`B.numPhases`, leaving head and tape untouched (it writes the scanned bit back and stays). -/
theorem repeatBody_stepConfig_handoff_phase (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit}
    (hlt : i.val < B.numPhases) (hi : i.val = B.acceptPhase.val)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).state).fst.val = B.numPhases := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (repeatBody B) c hstate]
  simp only [repeatBody, dif_pos hlt, if_pos hi]

/-- Handoff step: the head is unchanged. -/
theorem repeatBody_stepConfig_handoff_head (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit}
    (hlt : i.val < B.numPhases) (hi : i.val = B.acceptPhase.val)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).head = c.head := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (repeatBody B) c hstate]
  have hmove : ((repeatBody B).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
    simp only [repeatBody, dif_pos hlt, if_pos hi]
  rw [hmove]
  simp [Configuration.moveHead]

/-- Handoff step: the tape is unchanged (the scanned bit is written back). -/
theorem repeatBody_stepConfig_handoff_tape (B : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    {i : Fin (repeatBody B).numPhases} {s : Unit}
    (hlt : i.val < B.numPhases) (hi : i.val = B.acceptPhase.val)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (repeatBody B).toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (repeatBody B) c hstate]
  have hbitw : ((repeatBody B).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
    simp only [repeatBody, dif_pos hlt, if_pos hi]
  rw [hbitw]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### One loop iteration (the inductive step toward run-`K`-times correctness)

The body's behaviour enters as an **intrinsic** hypothesis on `(repeatBody B).toTM` (from any config at
`B`'s start phase, `sB` steps reach `B`'s accept phase, head- and tape-preserving) — stated directly on
the composed machine, so no cross-instance bisimulation with `B.toTM` is needed; a caller discharges it
per-instance.  (Tape-preserving = a read-only body, the clean first case; writing bodies generalise the
tape clause.) -/

/-- One loop iteration: from `B`'s start phase with a counter tick (`1`) under the head (`head ≠ 0`),
after `sB + 2` steps (`sB` body ▸ 1 handoff ▸ 1 consume) control is back at `B`'s start phase, the head
has retreated one cell, and that tick is cleared to `0` (rest of tape unchanged).  This is the inductive
step of the run-`K`-times correctness; it composes the intrinsic body hypothesis with the handoff and
consume single-step lemmas. -/
theorem repeatBody_runConfig_one_iteration (B : ConstStatePhasedProgram Unit) {L : Nat} (sB : Nat)
    (hbody : ∀ d : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (d.state.fst : Nat) = B.startPhase.val →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).state.fst : Nat) = B.acceptPhase.val
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).head = d.head
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).tape = d.tape)
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    (hstart : (c.state.fst : Nat) = B.startPhase.val)
    (hcell : c.tape c.head = true) (hpos : (c.head : Nat) ≠ 0) :
    ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).state.fst : Nat)
        = B.startPhase.val
      ∧ ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).tape
          = c.write c.head false := by
  obtain ⟨hbph, hbhd, hbtp⟩ := hbody c hstart
  set cb := TM.runConfig (M := (repeatBody B).toPhased.toTM) c sB with hcb
  -- Handoff step (cb is at B's accept phase).
  have hlt : (cb.state.fst : Nat) < B.numPhases := by rw [hbph]; exact B.acceptPhase.isLt
  have hcd_ph : ((TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).state.fst : Nat)
      = B.numPhases :=
    repeatBody_stepConfig_handoff_phase B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  have hcd_hd : (TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).head = cb.head :=
    repeatBody_stepConfig_handoff_head B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  have hcd_tp : (TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).tape = cb.tape :=
    repeatBody_stepConfig_handoff_tape B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  set cd := TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb with hcd
  -- The result config is one more (consume) step from cd.
  have hrun : TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)
      = TM.stepConfig (M := (repeatBody B).toPhased.toTM) cd := by
    rw [hcd, hcb, show sB + 2 = (sB + 1) + 1 from rfl, TM.runConfig_succ, TM.runConfig_succ]
  -- cd reads the counter tick (tape and head carried through body + handoff).
  have hcd_bit : cd.tape cd.head = true := by
    rw [hcd, hcd_tp, hbtp, hcd_hd, hbhd]; exact hcell
  rw [hrun]
  refine ⟨?_, ?_, ?_⟩
  · exact repeatBody_stepConfig_consume_phase B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit
  · rw [repeatBody_stepConfig_consume_head B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit]
    have hcd_hd' : (cd.head : Nat) = (c.head : Nat) := by rw [hcd, hcd_hd, hbhd]
    rw [Configuration.moveHead_left_val_of_pos cd (by rw [hcd_hd']; omega), hcd_hd']
  · rw [repeatBody_stepConfig_consume_tape B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit]
    have hcd_hd' : cd.head = c.head := by rw [hcd, hcd_hd, hbhd]
    have hcd_tp' : cd.tape = c.tape := by rw [hcd, hcd_tp, hbtp]
    rw [hcd_hd']
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj, hcd_tp']

end ContractExpansion
end Frontier
end Pnp4
