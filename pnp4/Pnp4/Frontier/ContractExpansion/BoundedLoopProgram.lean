import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v
variable {S : Type v} [Fintype S] [DecidableEq S] [Inhabited S]

/-!
# Bounded loop for uniform-state phased programs

NP-verifier track (Phase 6 → 5/6): the missing control-flow primitive identified in
`TM_VERIFIER_STRATEGY.md`.

The Turing-machine model runs a program for a *fixed* number of steps (`runTime n`) and the toolkit's
`seq` / `seqList` are straight-line (no back-edges).  Iterating a body `k` times for a **symbolic** `k`
(e.g. `k = 2 ^ n`, the number of truth-table rows) is nonetheless expressible: `seqList` of
`List.replicate k body` is a well-typed `ConstStatePhasedProgram` for any `k : Nat`, and its
`timeBound` / run behaviour follow from the existing `seqList` recurrences by induction on `k`.  No new
back-edge machinery is needed — this is the verifier's row-iteration loop.
-/

/-- Run `body` sequentially `k` times (straight-line repetition, valid for symbolic `k`). -/
def repeatProgram (body : ConstStatePhasedProgram S) (k : Nat) : ConstStatePhasedProgram S :=
  seqList (List.replicate k body)

@[simp] theorem repeatProgram_zero (body : ConstStatePhasedProgram S) :
    repeatProgram body 0 = idleCS := rfl

/-- One iteration peels off the front (this is `rfl`, since `List.replicate (k+1)` is a cons). -/
theorem repeatProgram_succ (body : ConstStatePhasedProgram S) (k : Nat) :
    repeatProgram body (k + 1) = seq body (repeatProgram body k) := rfl

/-- Closed-form `timeBound`: `k` copies of the body plus one handoff per copy. -/
theorem repeatProgram_timeBound (body : ConstStatePhasedProgram S) (k n : Nat) :
    (repeatProgram body k).timeBound n = k * body.timeBound n + k := by
  induction k with
  | zero => simp [repeatProgram_zero]
  | succ k ih =>
      rw [repeatProgram_succ, seq_timeBound, ih]
      have hmul : (k + 1) * body.timeBound n = k * body.timeBound n + body.timeBound n :=
        Nat.succ_mul k (body.timeBound n)
      omega

/-- Uniform polynomial bound for the bounded loop: if the body runs within `B` steps, `k` iterations
run within `k * (B + 1)` steps.  This is the row loop's runtime-accounting shape — with `k = 2 ^ n`
and `B = poly n` it gives `2 ^ n * (poly n + 1) = poly L`, the form the eventual `runTime_poly`
obligation is discharged against. -/
theorem repeatProgram_timeBound_le (body : ConstStatePhasedProgram S) (k n B : Nat)
    (hB : body.timeBound n ≤ B) :
    (repeatProgram body k).timeBound n ≤ k * (B + 1) := by
  have hmul : k * body.timeBound n ≤ k * B := Nat.mul_le_mul (Nat.le_refl k) hB
  rw [repeatProgram_timeBound, Nat.mul_succ]
  omega

/--
Per-iteration run decomposition: running `repeatProgram body (k+1)` for its full `timeBound`
equals running the body once (its own `timeBound` steps) and then running the remaining `k` copies
(for `(repeatProgram body k).timeBound + 1` steps).  Inherited from `seqList_run_decomp`; this is the
inductive backbone for the eventual loop invariant.
-/
theorem repeatProgram_run_succ (body : ConstStatePhasedProgram S) (k : Nat) {n : Nat}
    (c : Configuration (M := (repeatProgram body (k + 1)).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c
        ((repeatProgram body (k + 1)).timeBound n)
      = TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM)
          (TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c (body.timeBound n))
          ((repeatProgram body k).timeBound n + 1) := by
  simp only [repeatProgram, List.replicate_succ] at c ⊢
  exact seqList_run_decomp body (List.replicate k body) c

/-- Base case: zero iterations leave the configuration unchanged.  Together with
`repeatProgram_run_succ` this is the base/step pair for a loop invariant by induction on `k`. -/
theorem repeatProgram_run_zero (body : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (repeatProgram body 0).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body 0).toPhased.toTM) c
        ((repeatProgram body 0).timeBound n) = c := by
  have h0 : (repeatProgram body 0).timeBound n = 0 := by
    rw [repeatProgram_timeBound]; simp
  rw [h0]
  rfl

/--
General closed form for the `timeBound` of a sequential composition: the sum of the components'
time bounds plus one handoff per component.  The verifier TM is assembled as a `seqList` of phase
programs, so this is the shape its polynomial `runTime` bound is proved against (generalizing the
toolkit's explicit `seqList_timeBound_singleton`/`_two`/`_three`).
-/
theorem seqList_timeBound_sum (ps : List (ConstStatePhasedProgram S)) (n : Nat) :
    (seqList ps).timeBound n = (ps.map (fun p => p.timeBound n)).sum + ps.length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      rw [seqList_timeBound_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/--
Uniform polynomial bound for a sequential composition: if every phase runs within `B` steps, the
whole `seqList` runs within `ps.length * (B + 1)` steps.  The verifier's `runTime_poly` obligation
instantiates this with `B` a polynomial bound common to its (constantly many) phases.
-/
theorem seqList_timeBound_le (ps : List (ConstStatePhasedProgram S)) (n B : Nat)
    (hB : ∀ p ∈ ps, p.timeBound n ≤ B) :
    (seqList ps).timeBound n ≤ ps.length * (B + 1) := by
  have hsum : ∀ (qs : List (ConstStatePhasedProgram S)),
      (∀ p ∈ qs, p.timeBound n ≤ B) →
      (qs.map (fun p => p.timeBound n)).sum ≤ qs.length * B := by
    intro qs
    induction qs with
    | nil => intro _; simp
    | cons p rest ih =>
        intro h
        have hp : p.timeBound n ≤ B := h p (List.mem_cons.mpr (Or.inl rfl))
        have hrest := ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))
        have e1 : (rest.length + 1) * B = rest.length * B + B := Nat.succ_mul rest.length B
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have hs := hsum ps hB
  have e2 : ps.length * (B + 1) = ps.length * B + ps.length := Nat.mul_succ ps.length B
  rw [seqList_timeBound_sum]
  omega

/-!
## Compositional `TMNeverMovesLeft`

The assembled verifier is a `seqList` of phase programs, and head-position tracking (offsets staying
within `tapeLength`) relies on the machine never moving left.  Rather than re-prove `neverMovesLeft`
monolithically for each composed program, these lemmas thread it through `seq` / `seqList`: a
composition of right-only/stay programs is itself right-only/stay.  The compiled-TM step's move is
definitionally the transition's move, and the toolkit's `seq_transition_*_move` lemmas characterize
each region (P1-normal mirrors P1, the P1-accept handoff is `Move.stay`, P2-region mirrors P2).
-/

omit [Inhabited S] in
/-- Transition-level never-left for `seq`: if both components' transition functions never move left,
neither does `seq P1 P2`'s. -/
theorem seq_transition_neverLeft (P1 P2 : ConstStatePhasedProgram S)
    (hP1 : ∀ (i : Fin P1.numPhases) (q : S) (b : Bool), (P1.transition i q b).2.2.2 ≠ Move.left)
    (hP2 : ∀ (i : Fin P2.numPhases) (q : S) (b : Bool), (P2.transition i q b).2.2.2 ≠ Move.left)
    (i : Fin (seq P1 P2).numPhases) (q : S) (b : Bool) :
    ((seq P1 P2).transition i q b).2.2.2 ≠ Move.left := by
  by_cases h1 : i.val < P1.numPhases
  · by_cases hacc : i.val = P1.acceptPhase.val
    · rw [seq_transition_P1_accept_move P1 P2 h1 hacc q b]; simp
    · rw [seq_transition_P1_normal_move P1 P2 h1 hacc q b]; exact hP1 ⟨i.val, h1⟩ q b
  · have h2 : P1.numPhases ≤ i.val := Nat.le_of_not_lt h1
    have hiLt : i.val < P1.numPhases + P2.numPhases := i.isLt
    have hlt : i.val - P1.numPhases < P2.numPhases := by omega
    rw [seq_transition_P2_move P1 P2 h2 hlt q b]; exact hP2 ⟨i.val - P1.numPhases, hlt⟩ q b

omit [Inhabited S] in
/-- `seq` preserves `TMNeverMovesLeft` (lifts `seq_transition_neverLeft` through `toPhased`/`toTM`). -/
theorem seq_neverMovesLeft (P1 P2 : ConstStatePhasedProgram S)
    (hP1 : TMNeverMovesLeft (P1.toPhased.toTM))
    (hP2 : TMNeverMovesLeft (P2.toPhased.toTM)) :
    TMNeverMovesLeft ((seq P1 P2).toPhased.toTM) := by
  intro st b
  obtain ⟨i, q⟩ := st
  exact seq_transition_neverLeft P1 P2
    (fun i q b => hP1 ⟨i, q⟩ b) (fun i q b => hP2 ⟨i, q⟩ b) i q b

/-- The idle program never moves left (it always stays). -/
theorem idleCS_neverMovesLeft : TMNeverMovesLeft ((idleCS (S := S)).toPhased.toTM) := by
  intro st b
  obtain ⟨i, q⟩ := st
  show ((idleCS (S := S)).transition i q b).2.2.2 ≠ Move.left
  simp [idleCS]

/-- `seqList` preserves `TMNeverMovesLeft`: if every component is right-only/stay, so is their
sequential composition.  Induction on the list (`seq_neverMovesLeft` at each cons,
`idleCS_neverMovesLeft` at the base).  This is the head-bound-tracking ingredient for the assembled
verifier, which is a `seqList` of phase programs. -/
theorem seqList_neverMovesLeft (ps : List (ConstStatePhasedProgram S))
    (h : ∀ p ∈ ps, TMNeverMovesLeft (p.toPhased.toTM)) :
    TMNeverMovesLeft ((seqList ps).toPhased.toTM) := by
  induction ps with
  | nil => exact idleCS_neverMovesLeft
  | cons p rest ih =>
      rw [seqList_cons]
      exact seq_neverMovesLeft p (seqList rest)
        (h p (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))))

/-- Head confinement for a composed run: if every component of a `seqList` is right-only/stay, then
running it for `j` steps from `c` keeps the head in `[c.head, c.head + j]`.  The lower bound is
head-monotonicity (via `seqList_neverMovesLeft`); the upper bound is the generic one-cell-per-step
fact.  This is the offset-validity ingredient for the assembled verifier (scratch offsets stay
within the `tapeLength = inputLen + runTime + 1` budget). -/
theorem seqList_runConfig_head_bounds (ps : List (ConstStatePhasedProgram S))
    (hmoves : ∀ p ∈ ps, TMNeverMovesLeft (p.toPhased.toTM)) {L : Nat}
    (c : Configuration (M := (seqList ps).toPhased.toTM) L) (j : Nat) :
    (c.head : ℕ) ≤ ((TM.runConfig (M := (seqList ps).toPhased.toTM) c j).head : ℕ)
      ∧ ((TM.runConfig (M := (seqList ps).toPhased.toTM) c j).head : ℕ) ≤ (c.head : ℕ) + j :=
  ⟨runConfig_head_val_ge_of_never_left c j (seqList_neverMovesLeft ps hmoves),
   runConfig_head_val_le c j⟩

/-!
## Single-step simulation of `seq` in the P1 region

These lemmas characterize one `stepConfig` of `(seq P1 P2).toTM` when the control phase lies in P1's
normal region (`< P1.numPhases`, not at P1's accept phase) entirely in terms of P1's transition
function — the phase index, accumulated local state, written bit (tape), and head move all follow
P1.  They are the single-step backbone for a run-level simulation of the first component inside a
composition (the analogue, for generic `seq`, of the tag-check program's `stepConfig` lemmas), built
from the toolkit's per-transition `seq_transition_P1_normal_*` characterizations.
-/

omit [Inhabited S] in
/-- One step in P1's normal region advances the phase exactly as P1's transition does. -/
theorem seq_stepConfig_P1_normal_phase (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hne : i.val ≠ P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).fst.val
      = (P1.transition ⟨i.val, h1⟩ q (c.tape c.head)).fst.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_normal_phase P1 P2 h1 hne q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in P1's normal region updates the local state exactly as P1's transition does. -/
theorem seq_stepConfig_P1_normal_state (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hne : i.val ≠ P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).snd
      = (P1.transition ⟨i.val, h1⟩ q (c.tape c.head)).snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_normal_state P1 P2 h1 hne q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in P1's normal region writes the bit P1's transition would write. -/
theorem seq_stepConfig_P1_normal_tape (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hne : i.val ≠ P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape
      = c.write c.head (P1.transition ⟨i.val, h1⟩ q (c.tape c.head)).snd.snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_normal_bit P1 P2 h1 hne q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in P1's normal region moves the head as P1's transition directs. -/
theorem seq_stepConfig_P1_normal_head (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hne : i.val ≠ P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head
      = c.moveHead (P1.transition ⟨i.val, h1⟩ q (c.tape c.head)).snd.snd.snd := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_normal_move P1 P2 h1 hne q (c.tape c.head)]

/-!
## Single-step simulation of `seq`: the P1→P2 handoff

When the control phase reaches P1's accept phase, one step performs the handoff: the phase jumps to
P2's start (shifted by `P1.numPhases`), the local state is (re)initialized to `P2.startState`, and —
since the handoff writes back the scanned bit and stays put — the tape and head are unchanged.  These
are the single-step lemmas for that distinguished boundary step.
-/

omit [Inhabited S] in
/-- The handoff step jumps the phase to P2's (shifted) start phase. -/
theorem seq_stepConfig_P1_accept_phase (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hacc : i.val = P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).fst.val
      = P1.numPhases + P2.startPhase.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_accept_phase P1 P2 h1 hacc q (c.tape c.head)]

omit [Inhabited S] in
/-- The handoff step (re)initializes the local state to `P2.startState`. -/
theorem seq_stepConfig_P1_accept_state (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hacc : i.val = P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).snd = P2.startState := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_accept_state P1 P2 h1 hacc q (c.tape c.head)]

omit [Inhabited S] in
/-- The handoff step leaves the tape unchanged (it writes back the scanned bit). -/
theorem seq_stepConfig_P1_accept_tape (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hacc : i.val = P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape = c.tape := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_accept_bit P1 P2 h1 hacc q (c.tape c.head)]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

omit [Inhabited S] in
/-- The handoff step leaves the head unchanged (it stays). -/
theorem seq_stepConfig_P1_accept_head (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h1 : i.val < P1.numPhases) (hacc : i.val = P1.acceptPhase.val)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P1_accept_move P1 P2 h1 hacc q (c.tape c.head)]
  simp [Configuration.moveHead]

/-!
## Single-step simulation of `seq` in the P2 region

Once the phase has crossed into P2's block (`≥ P1.numPhases`), each step follows P2's transition
function on the shifted phase index `i.val - P1.numPhases` — phase (shifted up by `P1.numPhases`),
local state, written bit, and head move.  Together with the P1-normal and handoff lemmas these give a
complete single-step characterization of `seq P1 P2` across all three regions.
-/

omit [Inhabited S] in
/-- One step in the P2 region advances the phase as P2's transition does (shifted up). -/
theorem seq_stepConfig_P2_phase (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h2 : P1.numPhases ≤ i.val) (hlt : i.val - P1.numPhases < P2.numPhases)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).fst.val
      = P1.numPhases + (P2.transition ⟨i.val - P1.numPhases, hlt⟩ q (c.tape c.head)).fst.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P2_phase P1 P2 h2 hlt q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in the P2 region updates the local state as P2's transition does. -/
theorem seq_stepConfig_P2_state (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h2 : P1.numPhases ≤ i.val) (hlt : i.val - P1.numPhases < P2.numPhases)
    (hstate : c.state = ⟨i, q⟩) :
    ((TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).state).snd
      = (P2.transition ⟨i.val - P1.numPhases, hlt⟩ q (c.tape c.head)).snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P2_state P1 P2 h2 hlt q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in the P2 region writes the bit P2's transition would write. -/
theorem seq_stepConfig_P2_tape (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h2 : P1.numPhases ≤ i.val) (hlt : i.val - P1.numPhases < P2.numPhases)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).tape
      = c.write c.head (P2.transition ⟨i.val - P1.numPhases, hlt⟩ q (c.tape c.head)).snd.snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P2_bit P1 P2 h2 hlt q (c.tape c.head)]

omit [Inhabited S] in
/-- One step in the P2 region moves the head as P2's transition directs. -/
theorem seq_stepConfig_P2_head (P1 P2 : ConstStatePhasedProgram S) {L : Nat}
    (c : Configuration (M := (seq P1 P2).toPhased.toTM) L)
    {i : Fin (seq P1 P2).numPhases} {q : S}
    (h2 : P1.numPhases ≤ i.val) (hlt : i.val - P1.numPhases < P2.numPhases)
    (hstate : c.state = ⟨i, q⟩) :
    (TM.stepConfig (M := (seq P1 P2).toPhased.toTM) c).head
      = c.moveHead (P2.transition ⟨i.val - P1.numPhases, hlt⟩ q (c.tape c.head)).snd.snd.snd := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  rw [seq_transition_P2_move P1 P2 h2 hlt q (c.tape c.head)]

/-!
## State lifting for heterogeneous-state assembly

`seq`/`seqList` require a *single* state type `S` shared by all components, but the assembled verifier
`M` mixes phases of different state types — e.g. the tag check is `ConstStatePhasedProgram Bool` (it
accumulates "prefix matches tag so far") while the self-loops are `ConstStatePhasedProgram Unit`.
Since the self-loops *ignore* their state component (`transition := fun i _ b => …`), a `Unit`-state
program can be reinterpreted over any inhabited `S`, carrying the `S` component inertly.

`liftUnitProgram` does exactly that.  This is the first step of the state-uniformity resolution
recorded in `TM_VERIFIER_STRATEGY.md` §6a: the structural facts (phase count, time bound, never-left)
transfer immediately, so a `seqList` mixing a lifted self-loop with a genuine `S`-state phase is
well-typed and inherits the polynomial-`timeBound`/never-left guarantees.  The *run-behaviour*
correspondence (a bisimulation on the inert state component, transferring the proven counter/scan run
invariants to the lifted versions) is the documented follow-up.
-/

/-- Reinterpret a state-agnostic `Unit`-state phased program over any inhabited state type `S`,
carrying the `S` component through each transition unchanged.  Phase index, written bit, and head move
are inherited verbatim from the `Unit` program. -/
def liftUnitProgram (P : ConstStatePhasedProgram Unit) : ConstStatePhasedProgram S where
  numPhases := P.numPhases
  startPhase := P.startPhase
  startState := default
  acceptPhase := P.acceptPhase
  acceptState := default
  transition := fun i s b =>
    let r := P.transition i () b
    (r.1, s, r.2.2.1, r.2.2.2)
  timeBound := P.timeBound

@[simp] theorem liftUnitProgram_numPhases (P : ConstStatePhasedProgram Unit) :
    (liftUnitProgram (S := S) P).numPhases = P.numPhases := rfl

@[simp] theorem liftUnitProgram_timeBound (P : ConstStatePhasedProgram Unit) (n : Nat) :
    (liftUnitProgram (S := S) P).timeBound n = P.timeBound n := rfl

@[simp] theorem liftUnitProgram_startPhase (P : ConstStatePhasedProgram Unit) :
    (liftUnitProgram (S := S) P).startPhase = P.startPhase := rfl

@[simp] theorem liftUnitProgram_acceptPhase (P : ConstStatePhasedProgram Unit) :
    (liftUnitProgram (S := S) P).acceptPhase = P.acceptPhase := rfl

/-- The lifted program inherits the `Unit` program's head moves verbatim, so it never moves left
whenever the original does — letting a lifted self-loop sit in a `seqList` with the head-tracking
guarantees intact. -/
theorem liftUnitProgram_neverMovesLeft (P : ConstStatePhasedProgram Unit)
    (hP : TMNeverMovesLeft (P.toPhased.toTM)) :
    TMNeverMovesLeft ((liftUnitProgram (S := S) P).toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact hP ⟨i, ()⟩ b

/-! ### Single-step characterization of `liftUnitProgram`

One `stepConfig` of `(liftUnitProgram P).toTM`, entirely in terms of `P`'s transition (on the unit
state `()`): the phase index, written bit, and head move are exactly `P`'s, while the lifted state
component is carried through **unchanged**.  These are the backbone for transferring the run behaviour
of a lifted self-loop across `liftUnitProgram` (the state-component bisimulation). -/

/-- A lifted step advances the phase exactly as `P`'s transition does. -/
theorem liftUnitProgram_stepConfig_phase (P : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (liftUnitProgram (S := S) P).toPhased.toTM) L)
    {i : Fin (liftUnitProgram (S := S) P).numPhases} {s : S} (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (liftUnitProgram (S := S) P).toPhased.toTM) c).state).fst.val
      = (P.transition i () (c.tape c.head)).fst.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, liftUnitProgram]

/-- A lifted step carries the state component through unchanged (the program is state-agnostic). -/
theorem liftUnitProgram_stepConfig_state (P : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (liftUnitProgram (S := S) P).toPhased.toTM) L)
    {i : Fin (liftUnitProgram (S := S) P).numPhases} {s : S} (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (liftUnitProgram (S := S) P).toPhased.toTM) c).state).snd = s := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, liftUnitProgram]

/-- A lifted step moves the head exactly as `P`'s transition directs. -/
theorem liftUnitProgram_stepConfig_head (P : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (liftUnitProgram (S := S) P).toPhased.toTM) L)
    {i : Fin (liftUnitProgram (S := S) P).numPhases} {s : S} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (liftUnitProgram (S := S) P).toPhased.toTM) c).head
      = c.moveHead (P.transition i () (c.tape c.head)).2.2.2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, liftUnitProgram]

/-- A lifted step writes exactly the bit `P`'s transition would write. -/
theorem liftUnitProgram_stepConfig_tape (P : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (liftUnitProgram (S := S) P).toPhased.toTM) L)
    {i : Fin (liftUnitProgram (S := S) P).numPhases} {s : S} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (liftUnitProgram (S := S) P).toPhased.toTM) c).tape
      = c.write c.head (P.transition i () (c.tape c.head)).2.2.1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, liftUnitProgram]

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
