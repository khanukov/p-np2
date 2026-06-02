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

/-- Run-`K`-times correctness: with the intrinsic head/tape-preserving body hypothesis `hbody`, if a
unary counter of `K` ticks sits at and to the left of the head (cells `(head − K, head]` all `1`, and
`K ≤ head`), then after `K · (sB + 2)` steps the loop has run the body `K` times — control is back at
`B`'s start phase, the head has retreated `K` cells, and those `K` ticks are cleared to `0` (rest of
tape unchanged).  Proved by induction on `K`, peeling one iteration (`repeatBody_runConfig_one_iteration`)
per step via `TM.runConfig_add`.  This is the combinator's headline behaviour — the bounded loop runs a
data-dependent (`K`) number of iterations on a fixed machine. -/
theorem repeatBody_runConfig_iterate (B : ConstStatePhasedProgram Unit) {L : Nat} (sB : Nat)
    (hbody : ∀ d : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (d.state.fst : Nat) = B.startPhase.val →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).state.fst : Nat) = B.acceptPhase.val
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).head = d.head
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).tape = d.tape) :
    ∀ K : Nat, ∀ c : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (c.state.fst : Nat) = B.startPhase.val → K ≤ (c.head : Nat) →
      (∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L),
        (c.head : Nat) - K < (p : Nat) → (p : Nat) ≤ (c.head : Nat) → c.tape p = true) →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).state.fst : Nat)
          = B.startPhase.val
      ∧ ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).head : Nat)
          = (c.head : Nat) - K
      ∧ ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).tape p
            = (if (c.head : Nat) - K < (p : Nat) ∧ (p : Nat) ≤ (c.head : Nat)
                then false else c.tape p) := by
  intro K
  induction K with
  | zero =>
      intro c hstart _ _
      rw [Nat.zero_mul]
      have hrc : TM.runConfig (M := (repeatBody B).toPhased.toTM) c 0 = c := rfl
      rw [hrc]
      refine ⟨hstart, by omega, ?_⟩
      intro p
      rw [if_neg (show ¬ ((c.head : Nat) - 0 < (p : Nat) ∧ (p : Nat) ≤ (c.head : Nat)) by omega)]
  | succ K ih =>
      intro c hstart hK hones
      have hcell : c.tape c.head = true := hones c.head (by omega) (le_refl _)
      have hpos : (c.head : Nat) ≠ 0 := by omega
      obtain ⟨h1ph, h1hd, h1tp⟩ := repeatBody_runConfig_one_iteration B sB hbody c hstart hcell hpos
      set c' := TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2) with hc'
      have hc'K : K ≤ (c'.head : Nat) := by rw [h1hd]; omega
      have hc'ones : ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L),
          (c'.head : Nat) - K < (p : Nat) → (p : Nat) ≤ (c'.head : Nat) → c'.tape p = true := by
        intro p hp1 hp2
        rw [h1hd] at hp1 hp2
        have hpne : p ≠ c.head := Fin.ne_of_val_ne (by omega)
        rw [h1tp, Configuration.write_other c hpne false]
        exact hones p (by omega) (by omega)
      obtain ⟨hIph, hIhd, hItp⟩ := ih c' h1ph hc'K hc'ones
      have hsplit : (K + 1) * (sB + 2) = (sB + 2) + K * (sB + 2) := by rw [Nat.succ_mul]; omega
      rw [hsplit, TM.runConfig_add, ← hc']
      refine ⟨hIph, ?_, ?_⟩
      · rw [hIhd, h1hd]; omega
      · intro p
        rw [hItp p, h1hd]
        by_cases hpc : (p : Nat) = (c.head : Nat)
        · have hpfin : p = c.head := Fin.ext hpc
          subst hpfin
          rw [if_neg (by omega), h1tp, Configuration.write_self, if_pos (by omega)]
        · have hpfin : p ≠ c.head := Fin.ne_of_val_ne hpc
          rw [h1tp, Configuration.write_other c hpfin false]
          by_cases hcond : (c.head : Nat) - 1 - K < (p : Nat) ∧ (p : Nat) ≤ (c.head : Nat) - 1
          · rw [if_pos hcond, if_pos (by omega)]
          · rw [if_neg hcond, if_neg (by omega)]

/-! ### Writing-body generalization (counter-region-preserving body)

A *useful* loop body writes (e.g. a shift-accumulate `n`-register in scratch).  §6d pins the general
hypothesis: the body need only preserve the **counter region** (cells `≤ head`, where the countdown
consumes), writing freely above.  The conclusion then tracks only the counter region; the work region
(`> head`) holds the body's output and is the body's own concern (established when the per-instance
hypothesis is discharged).  This generalizes `repeatBody_runConfig_one_iteration` from a read-only to a
writing body. -/

/-- One loop iteration with a **writing** body that preserves the counter region (cells `≤ head`):
after `sB + 2` steps control is back at `B`'s start phase, the head has retreated one cell, and on the
counter region (`p ≤ c.head`) the tape is the consume of the original (cell `c.head` cleared, the rest
unchanged); the work region `p > c.head` is left to the body. -/
theorem repeatBody_runConfig_one_iteration' (B : ConstStatePhasedProgram Unit) {L : Nat} (sB : Nat)
    (hbody : ∀ d : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (d.state.fst : Nat) = B.startPhase.val →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).state.fst : Nat) = B.acceptPhase.val
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).head = d.head
      ∧ ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L), (p : Nat) ≤ (d.head : Nat) →
          (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).tape p = d.tape p)
    (c : Configuration (M := (repeatBody B).toPhased.toTM) L)
    (hstart : (c.state.fst : Nat) = B.startPhase.val)
    (hcell : c.tape c.head = true) (hpos : (c.head : Nat) ≠ 0) :
    ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).state.fst : Nat)
        = B.startPhase.val
      ∧ ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).head : Nat)
          = (c.head : Nat) - 1
      ∧ ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L), (p : Nat) ≤ (c.head : Nat) →
          (TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)).tape p
            = (if (p : Nat) = (c.head : Nat) then false else c.tape p) := by
  obtain ⟨hbph, hbhd, hbtp⟩ := hbody c hstart
  set cb := TM.runConfig (M := (repeatBody B).toPhased.toTM) c sB with hcb
  have hlt : (cb.state.fst : Nat) < B.numPhases := by rw [hbph]; exact B.acceptPhase.isLt
  have hcd_ph : ((TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).state.fst : Nat)
      = B.numPhases :=
    repeatBody_stepConfig_handoff_phase B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  have hcd_hd : (TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).head = cb.head :=
    repeatBody_stepConfig_handoff_head B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  have hcd_tp : (TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb).tape = cb.tape :=
    repeatBody_stepConfig_handoff_tape B cb (i := cb.state.fst) (s := cb.state.snd) hlt hbph rfl
  set cd := TM.stepConfig (M := (repeatBody B).toPhased.toTM) cb with hcd
  have hrun : TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2)
      = TM.stepConfig (M := (repeatBody B).toPhased.toTM) cd := by
    rw [hcd, hcb, show sB + 2 = (sB + 1) + 1 from rfl, TM.runConfig_succ, TM.runConfig_succ]
  have hcdhd' : cd.head = c.head := by rw [hcd, hcd_hd, hbhd]
  have hcd_bit : cd.tape cd.head = true := by
    rw [hcd, hcd_tp, hcdhd']
    rw [hbtp c.head (Nat.le_refl _)]; exact hcell
  rw [hrun]
  refine ⟨?_, ?_, ?_⟩
  · exact repeatBody_stepConfig_consume_phase B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit
  · rw [repeatBody_stepConfig_consume_head B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit]
    rw [Configuration.moveHead_left_val_of_pos cd (by rw [hcdhd']; omega), hcdhd']
  · intro p hp
    rw [repeatBody_stepConfig_consume_tape B cd
      (i := cd.state.fst) (s := cd.state.snd) (by rw [hcd, hcd_ph]) rfl hcd_bit, hcdhd']
    by_cases hpc : (p : Nat) = (c.head : Nat)
    · have hpfin : p = c.head := Fin.ext hpc
      subst hpfin
      rw [Configuration.write_self, if_pos rfl]
    · rw [Configuration.write_other cd (Fin.ne_of_val_ne hpc) false, if_neg hpc, hcd, hcd_tp]
      exact hbtp p hp

/-- Run-`K`-times correctness for a **writing** body (counter-region-preserving): a `K`-tick unary
counter drives exactly `K` body iterations, and the cells **strictly below the final head**
(`p ≤ c.head − K`) are preserved (`= c.tape`).  Those cells are never consumed and lie below every
iteration's head, so every (counter-region-preserving) body leaves them untouched.  The consumed window
and the work region above are the body's business (a writing body may overwrite already-consumed cells
in later iterations, so they are *not* claimed cleared — the honest invariant).  Generalizes
`repeatBody_runConfig_iterate` to writing bodies, via `repeatBody_runConfig_one_iteration'`. -/
theorem repeatBody_runConfig_iterate' (B : ConstStatePhasedProgram Unit) {L : Nat} (sB : Nat)
    (hbody : ∀ d : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (d.state.fst : Nat) = B.startPhase.val →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).state.fst : Nat) = B.acceptPhase.val
      ∧ (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).head = d.head
      ∧ ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L), (p : Nat) ≤ (d.head : Nat) →
          (TM.runConfig (M := (repeatBody B).toPhased.toTM) d sB).tape p = d.tape p) :
    ∀ K : Nat, ∀ c : Configuration (M := (repeatBody B).toPhased.toTM) L,
      (c.state.fst : Nat) = B.startPhase.val → K ≤ (c.head : Nat) →
      (∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L),
        (c.head : Nat) - K < (p : Nat) → (p : Nat) ≤ (c.head : Nat) → c.tape p = true) →
      ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).state.fst : Nat)
          = B.startPhase.val
      ∧ ((TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).head : Nat)
          = (c.head : Nat) - K
      ∧ ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L), (p : Nat) ≤ (c.head : Nat) - K →
          (TM.runConfig (M := (repeatBody B).toPhased.toTM) c (K * (sB + 2))).tape p = c.tape p := by
  intro K
  induction K with
  | zero =>
      intro c hstart _ _
      rw [Nat.zero_mul]
      have hrc : TM.runConfig (M := (repeatBody B).toPhased.toTM) c 0 = c := rfl
      rw [hrc]
      exact ⟨hstart, by omega, fun p _ => rfl⟩
  | succ K ih =>
      intro c hstart hK hones
      have hcell : c.tape c.head = true := hones c.head (by omega) (le_refl _)
      have hpos : (c.head : Nat) ≠ 0 := by omega
      obtain ⟨h1ph, h1hd, h1tp⟩ := repeatBody_runConfig_one_iteration' B sB hbody c hstart hcell hpos
      set c' := TM.runConfig (M := (repeatBody B).toPhased.toTM) c (sB + 2) with hc'
      have hc'K : K ≤ (c'.head : Nat) := by rw [h1hd]; omega
      have hc'ones : ∀ p : Fin ((repeatBody B).toPhased.toTM.tapeLength L),
          (c'.head : Nat) - K < (p : Nat) → (p : Nat) ≤ (c'.head : Nat) → c'.tape p = true := by
        intro p hp1 hp2
        rw [h1hd] at hp1 hp2
        have hple : (p : Nat) ≤ (c.head : Nat) := by omega
        have hpne : (p : Nat) ≠ (c.head : Nat) := by omega
        rw [h1tp p hple, if_neg hpne]
        exact hones p (by omega) (by omega)
      obtain ⟨hIph, hIhd, hItp⟩ := ih c' h1ph hc'K hc'ones
      have hsplit : (K + 1) * (sB + 2) = (sB + 2) + K * (sB + 2) := by rw [Nat.succ_mul]; omega
      rw [hsplit, TM.runConfig_add, ← hc']
      refine ⟨hIph, ?_, ?_⟩
      · rw [hIhd, h1hd]; omega
      · intro p hp
        have hple : (p : Nat) ≤ (c'.head : Nat) - K := by rw [h1hd]; omega
        have hple2 : (p : Nat) ≤ (c.head : Nat) := by omega
        have hpne : (p : Nat) ≠ (c.head : Nat) := by omega
        rw [hItp p hple, h1tp p hple2, if_neg hpne]

end ContractExpansion
end Frontier
end Pnp4
