import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.BinaryCounter

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-!
# Self-loop binary increment & decrement (NP-verifier track, brick 0 — variable-width counter machinery)

The verifier's loops (notably the `2^m`-row loop) iterate a data-dependent number of times and so need
a **variable-width** counter on the tape — but the toolkit's `incrementProgram k` is fixed-`k`, and a
single fixed verifier `M` cannot pick `k` per input (see `TM_VERIFIER_STRATEGY.md` §6's correction).
The fix is the same back-edge idea proven for the gamma scan: a **self-loop** binary increment.

`selfLoopIncrement` adds `1` to a little-endian counter starting at the head (LSB first, carry toward
the right/MSB).  Phase `0` is the *carry* phase: while it reads a `1` it writes a `0` and advances
(the carry propagates), re-entering itself (the back-edge); on reading a `0` it writes a `1` and stops
(phase `1`).  This stops at the first `0` **regardless of the counter's width**, so it has a fixed
2-phase structure yet operates on a data-dependent-width counter — exactly what `M` requires.

This module builds the program and its structural facts (`timeBound`, never-moves-left, single-step
lemmas).  The semantic correctness (`counterValue` increases by one, with overflow handling) reuses
the toolkit's `counterValue` and is the next brick.  This builds no verifier and proves no separation.
-/

/-- Self-loop binary increment of a little-endian tape counter at the head.  Carry phase `0`
re-enters itself (writing `0`, advancing) while reading `1`; on reading `0` it writes `1` and stops
(phase `1`).  Fixed 2-phase structure, variable-width operation. -/
def selfLoopIncrement : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), false, Move.right)
      else (⟨1, by omega⟩, (), true, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopIncrement_timeBound (n : Nat) :
    selfLoopIncrement.timeBound n = n := rfl

@[simp] theorem selfLoopIncrement_numPhases : selfLoopIncrement.numPhases = 2 := rfl

@[simp] theorem selfLoopIncrement_acceptPhase_val : selfLoopIncrement.acceptPhase.val = 1 := rfl

@[simp] theorem selfLoopIncrement_startPhase_val : selfLoopIncrement.startPhase.val = 0 := rfl

/-- The increment never moves the head left: the carry advances right, otherwise stays. -/
theorem selfLoopIncrement_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopIncrement.transition i s b).2.2.2 ≠ Move.left := by
  unfold selfLoopIncrement
  dsimp only
  split_ifs <;> simp

/-- The compiled increment TM never moves its head left (lifts the transition fact through
`toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem selfLoopIncrement_neverMovesLeft :
    TMNeverMovesLeft (selfLoopIncrement.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact selfLoopIncrement_transition_move i s b

/-! ### Single-step lemmas

The carry step (phase `0` reading `1`): write `0`, advance right, stay in phase `0` (the back-edge).
The stop step (phase `0` reading `0`): write `1`, stay, go to the done phase `1`. -/

/-- Carry step (phase `0`, bit `1`): the phase stays `0` (the self-loop re-entry). -/
theorem selfLoopIncrement_stepConfig_carry_phase {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry step (phase `0`, bit `1`): the head advances right (carry propagates). -/
theorem selfLoopIncrement_stepConfig_carry_head {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry step (phase `0`, bit `1`): the read `1` is flipped to `0` at the head. -/
theorem selfLoopIncrement_stepConfig_carry_tape {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape = c.write c.head false := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the phase becomes the done phase `1`. -/
theorem selfLoopIncrement_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopIncrement_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit, Configuration.moveHead]

/-- Stop step (phase `0`, bit `0`): the read `0` is flipped to `1` at the head. -/
theorem selfLoopIncrement_stepConfig_stop_tape {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry-ripple invariant (structural backbone of the increment): if the first `k` counter cells are
all `1`, then after `k ≤ L` steps from the initial configuration the carry is still propagating —
phase `0`, head at `k`, and the tape has exactly cells `[0, k)` flipped to `0` (the rest unchanged).
Proved by induction with the carry single-step lemmas; the back-edge fires because every read so far
was a `1`.  This tracks the *evolving* tape (unlike the tape-preserving gamma scan), and is the step
toward the `counterValue + 1` correctness. -/
theorem selfLoopIncrement_runConfig_carry {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true) →
      (((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
            (selfLoopIncrement.toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then false
                else (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨rfl, rfl, ?_⟩
      intro p; simp
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp => h1 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < selfLoopIncrement.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + L + 1; omega
      have hbit : c.tape c.head = true := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h1 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopIncrement_stepConfig_carry_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopIncrement_stepConfig_carry_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopIncrement_stepConfig_carry_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

/-- After-increment configuration: if the first `j` counter cells are `1` and cell `j` is `0`
(`j ≤ L`), then after `j + 1` steps the increment is done — phase `1`, head on cell `j`, and the tape
has cells `[0, j)` cleared to `0`, cell `j` set to `1`, and everything beyond unchanged.  Combines
the carry-ripple invariant at `j` with one terminating "stop" step (the read `0` is flipped to `1`).
This is the increment's result configuration, feeding the `counterValue + 1` correctness. -/
theorem selfLoopIncrement_runConfig_stop {L : Nat} (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_ones : ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < selfLoopIncrement.toPhased.toTM.tapeLength L,
      (selfLoopIncrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    (((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
            (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) < j then false
                else if (p : Nat) = j then true
                else (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopIncrement_runConfig_carry x j hj h_ones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
    (selfLoopIncrement.toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = false := by
    rw [htp, if_neg (show ¬ (c.head : Nat) < j by rw [hhd]; omega), hhead_eq]
    exact h_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopIncrement_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopIncrement_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopIncrement_stepConfig_stop_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      simp [hhd]
    · rw [Configuration.write_other c hp true, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      split_ifs <;> rfl

/-- Semantic correctness of the self-loop increment: if the counter window `[0, k)` has its first `j`
cells `1` and cell `j` is `0` (`j < k ≤ L`), then after `j + 1` steps its little-endian value has
increased by exactly one.  A direct plug-in of the after-stop tape characterization
(`selfLoopIncrement_runConfig_stop`) into the toolkit's generic bit-flip arithmetic
(`counterValue_first_zero_diff`).  This is the variable-width counter's payoff — the structure the
single fixed verifier `M` needs to drive its data-dependent loops. -/
theorem selfLoopIncrement_runConfig_counterValue {L : Nat} (x : Boolcube.Point L) (j k : Nat)
    (hjk : j < k) (hk : k ≤ L)
    (h_ones : ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < selfLoopIncrement.toPhased.toTM.tapeLength L,
      (selfLoopIncrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    counterValue (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)) 0 k
      = counterValue (selfLoopIncrement.toPhased.toTM.initialConfig x) 0 k + 1 := by
  obtain ⟨_, _, htp⟩ := selfLoopIncrement_runConfig_stop x j (by omega) h_ones h_zero
  refine counterValue_first_zero_diff
    (selfLoopIncrement.toPhased.toTM.initialConfig x)
    (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
      (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)) 0 j k hjk
    (by show (0 : Nat) + k ≤ L + L + 1; omega) ?_ ?_ ?_ ?_ ?_
  · intro i hij hb
    simp only [Nat.zero_add] at hb ⊢
    exact h_ones ⟨i, hb⟩ hij
  · intro hb
    simp only [Nat.zero_add] at hb ⊢
    exact h_zero hb
  · intro i hij hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨i, hb⟩, if_pos hij]
  · intro hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨j, hb⟩, if_neg (Nat.lt_irrefl j), if_pos rfl]
  · intro i hji hik hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨i, hb⟩, if_neg (show ¬ i < j by omega), if_neg (show ¬ i = j by omega)]

/-! ### Done-phase stability (idle after the increment)

Once the increment reaches the done phase (`1`), every further step preserves the entire
configuration (the done-phase transition writes the scanned bit back and stays).  This pins the
counter's configuration after its full allotted runtime — needed when the increment is composed into
`M` and idles until the next phase begins. -/

/-- A single step from the done phase (`1`) preserves the phase, head, and tape. -/
theorem selfLoopIncrement_stepConfig_done {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- Iterated done-phase stability: from a done configuration (phase `1`), running any number of steps
keeps the phase at `1`, the head fixed, and the tape unchanged. -/
theorem selfLoopIncrement_runConfig_done {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    (hdone : (c.state.fst : Nat) = 1) (j : Nat) :
    ((TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j).state.fst : Nat) = 1
    ∧ (TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j).head = c.head
    ∧ (TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j).tape = c.tape := by
  induction j with
  | zero => exact ⟨hdone, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨hph, hhd, htp⟩ := ih
      rw [TM.runConfig_succ]
      obtain ⟨hph2, hhd2, htp2⟩ :=
        selfLoopIncrement_stepConfig_done
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j)
          (i := (TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j).state.fst)
          (s := (TM.runConfig (M := selfLoopIncrement.toPhased.toTM) c j).state.snd) hph rfl
      exact ⟨hph2, by rw [hhd2, hhd], by rw [htp2, htp]⟩

/-- Full-runtime correctness of the self-loop increment: running it for its entire declared runtime
(`TM.run`, `= L` steps) on a counter window `[0, k)` with first-zero at `j` (`j < k ≤ L`) increases
the little-endian value by exactly one.  Combines the `counterValue + 1` result at step `j + 1` with
done-phase idle stability (which preserves the tape, hence the counter value) for the remaining
`L − (j+1)` steps, via `runConfig_add` and `counterValue_eq_of_tape_eq`.  This is the variable-width
counter's headline theorem — a single fixed-`M`-compatible increment correct over its whole run. -/
theorem selfLoopIncrement_run_counterValue {L : Nat} (x : Boolcube.Point L) (j k : Nat)
    (hjk : j < k) (hk : k ≤ L)
    (h_ones : ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < selfLoopIncrement.toPhased.toTM.tapeLength L,
      (selfLoopIncrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    counterValue (TM.run (M := selfLoopIncrement.toPhased.toTM) (n := L) x) 0 k
      = counterValue (selfLoopIncrement.toPhased.toTM.initialConfig x) 0 k + 1 := by
  obtain ⟨hph_stop, _, _⟩ := selfLoopIncrement_runConfig_stop x j (by omega) h_ones h_zero
  have hrun : TM.run (M := selfLoopIncrement.toPhased.toTM) (n := L) x
      = TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) L := rfl
  have hadd : TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) L
      = TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
            (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)) (L - (j + 1)) := by
    rw [← TM.runConfig_add]; congr 1; omega
  obtain ⟨_, _, htp_idle⟩ := selfLoopIncrement_runConfig_done
    (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
      (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)) hph_stop (L - (j + 1))
  rw [hrun, hadd,
    counterValue_eq_of_tape_eq _
      (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)) 0 k
      (fun p _ _ => congrFun htp_idle p)]
  exact selfLoopIncrement_runConfig_counterValue x j k hjk hk h_ones h_zero

/-! ## Self-loop binary decrement (dual down-counter step)

The bounded loops the verifier `M` must run terminate by counting — and counters run in *both*
directions: an up-counter (`selfLoopIncrement`) for "row `0 … 2^m − 1`" style indices, and a
**down-counter** for "repeat `K` times, decrementing each pass" style termination.  `selfLoopDecrement`
is the exact dual of the increment: phase `0` is the *borrow* phase; while it reads a `0` it writes a
`1` and advances (the borrow propagates), re-entering itself (the back-edge); on reading the first `1`
it writes a `0` and stops (phase `1`).  Like the increment this stops at the first `1` **regardless of
the counter's width**, so it is a fixed 2-phase program operating on a data-dependent-width counter,
and is correct whenever the counter value is positive (`value ≥ 1`, i.e. some bit is set).

The semantic payoff (`counterValue` decreases by exactly one) rests on a *dual* of the toolkit's
`counterValue_first_zero_diff`: the bit-flip arithmetic for a borrow (first `j` cells `0 → 1`, cell `j`
`1 → 0`).  The toolkit ships only the increment direction, so we prove the dual
`counterValue_first_one_diff` locally (reusing the toolkit's `counterValue_of_all_true` /
`counterValue_of_all_false`).  This adds no axioms beyond the standard execution triple and builds no
verifier and no separation. -/

/-- Generic bit-flip arithmetic for a binary **decrement** (dual of the toolkit's
`counterValue_first_zero_diff`): if tape `c'` is obtained from tape `c` by flipping the first `j` bits
of the counter window from `0` to `1` (the borrow), the bit at position `j` from `1` to `0`
(terminating), and leaving everything beyond `j` unchanged, then `counterValue c = counterValue c' + 1`
(the borrow form `before = after + 1`, avoiding `Nat` truncation).  Proof mirrors the toolkit's
increment lemma with the `true`/`false` roles swapped. -/
theorem counterValue_first_one_diff {M : TM.{0}} {n : Nat}
    (c c' : Configuration (M := M) n) (start j : Nat) :
    ∀ k, j < k → start + k ≤ M.tapeLength n →
    (∀ i, i < j → ∀ (hb : start + i < M.tapeLength n),
       c.tape ⟨start + i, hb⟩ = false) →
    (∀ (hb : start + j < M.tapeLength n),
       c.tape ⟨start + j, hb⟩ = true) →
    (∀ i, i < j → ∀ (hb : start + i < M.tapeLength n),
       c'.tape ⟨start + i, hb⟩ = true) →
    (∀ (hb : start + j < M.tapeLength n),
       c'.tape ⟨start + j, hb⟩ = false) →
    (∀ i, j < i → i < k → ∀ (hb : start + i < M.tapeLength n),
       c'.tape ⟨start + i, hb⟩ = c.tape ⟨start + i, hb⟩) →
    counterValue c start k = counterValue c' start k + 1 := by
  intro k hjk h_bound h_zeros_old h_bit_old h_ones_new h_bit_new h_beyond
  induction k with
  | zero => omega
  | succ k' ih =>
    rw [counterValue_succ, counterValue_succ]
    by_cases hcase : k' = j
    · -- Base of the decomposition: k' = j, so the added bit IS the flipped one.
      rw [hcase]
      have h_bound_j : start + j < M.tapeLength n := by omega
      have h_bound_j_le : start + j ≤ M.tapeLength n := by omega
      -- Compute `counterValue c start j` (all false ⇒ 0) and
      -- `counterValue c' start j` (all true ⇒ 2^j − 1).
      have h_old_lo : counterValue c start j = 0 :=
        counterValue_of_all_false c start j h_zeros_old
      have h_new_lo : counterValue c' start j = 2 ^ j - 1 :=
        counterValue_of_all_true c' start j h_bound_j_le h_ones_new
      rw [h_old_lo, h_new_lo, dif_pos h_bound_j, dif_pos h_bound_j]
      simp [h_bit_old h_bound_j, h_bit_new h_bound_j]
      have hpow : (1 : Nat) ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    · -- Inductive case: k' > j.
      have hk'_gt_j : k' > j := by omega
      have hjk' : j < k' := hk'_gt_j
      have h_bound' : start + k' ≤ M.tapeLength n := by omega
      have h_beyond' : ∀ i, j < i → i < k' →
          ∀ (hb : start + i < M.tapeLength n),
          c'.tape ⟨start + i, hb⟩ = c.tape ⟨start + i, hb⟩ :=
        fun i hi hik' => h_beyond i hi (by omega)
      have ih_applied := ih hjk' h_bound' h_beyond'
      -- Beyond position j the contribution terms are equal.
      have h_term_eq :
          (if hi : start + k' < M.tapeLength n then
            (if c'.tape ⟨start + k', hi⟩ then 2 ^ k' else 0)
          else 0) =
          (if hi : start + k' < M.tapeLength n then
            (if c.tape ⟨start + k', hi⟩ then 2 ^ k' else 0)
          else 0) := by
        by_cases hbound : start + k' < M.tapeLength n
        · simp only [dif_pos hbound]
          rw [h_beyond k' hk'_gt_j (by omega) hbound]
        · simp only [dif_neg hbound]
      rw [h_term_eq, ih_applied]
      omega

/-- Self-loop binary decrement of a little-endian tape counter at the head (dual of
`selfLoopIncrement`).  Borrow phase `0` re-enters itself (writing `1`, advancing) while reading `0`;
on reading the first `1` it writes `0` and stops (phase `1`).  Fixed 2-phase structure, variable-width
operation; correct when the counter value is positive. -/
def selfLoopDecrement : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨1, by omega⟩, (), false, Move.stay)
      else (⟨0, by omega⟩, (), true, Move.right)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopDecrement_timeBound (n : Nat) :
    selfLoopDecrement.timeBound n = n := rfl

@[simp] theorem selfLoopDecrement_numPhases : selfLoopDecrement.numPhases = 2 := rfl

@[simp] theorem selfLoopDecrement_acceptPhase_val : selfLoopDecrement.acceptPhase.val = 1 := rfl

@[simp] theorem selfLoopDecrement_startPhase_val : selfLoopDecrement.startPhase.val = 0 := rfl

/-- The decrement never moves the head left: the borrow advances right, otherwise stays. -/
theorem selfLoopDecrement_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopDecrement.transition i s b).2.2.2 ≠ Move.left := by
  unfold selfLoopDecrement
  dsimp only
  split_ifs <;> simp

/-- The compiled decrement TM never moves its head left. -/
theorem selfLoopDecrement_neverMovesLeft :
    TMNeverMovesLeft (selfLoopDecrement.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact selfLoopDecrement_transition_move i s b

/-! ### Single-step lemmas

The borrow step (phase `0` reading `0`): write `1`, advance right, stay in phase `0` (the back-edge).
The stop step (phase `0` reading `1`): write `0`, stay, go to the done phase `1`. -/

/-- Borrow step (phase `0`, bit `0`): the phase stays `0` (the self-loop re-entry). -/
theorem selfLoopDecrement_stepConfig_borrow_phase {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit]

/-- Borrow step (phase `0`, bit `0`): the head advances right (borrow propagates). -/
theorem selfLoopDecrement_stepConfig_borrow_head {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit]

/-- Borrow step (phase `0`, bit `0`): the read `0` is flipped to `1` at the head. -/
theorem selfLoopDecrement_stepConfig_borrow_tape {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit]

/-- Stop step (phase `0`, bit `1`): the phase becomes the done phase `1`. -/
theorem selfLoopDecrement_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit]

/-- Stop step (phase `0`, bit `1`): the head stays put. -/
theorem selfLoopDecrement_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit, Configuration.moveHead]

/-- Stop step (phase `0`, bit `1`): the read `1` is flipped to `0` at the head. -/
theorem selfLoopDecrement_stepConfig_stop_tape {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).tape = c.write c.head false := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, hbit]

/-- Borrow-ripple invariant (structural backbone of the decrement): if the first `k` counter cells are
all `0`, then after `k ≤ L` steps from the initial configuration the borrow is still propagating —
phase `0`, head at `k`, and the tape has exactly cells `[0, k)` flipped to `1` (the rest unchanged).
Dual of `selfLoopIncrement_runConfig_carry`. -/
theorem selfLoopDecrement_runConfig_borrow {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p = false) →
      (((TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (selfLoopDecrement.toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (selfLoopDecrement.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
            (selfLoopDecrement.toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then true
                else (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨rfl, rfl, ?_⟩
      intro p; simp
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp => h0 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
        (selfLoopDecrement.toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < selfLoopDecrement.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + L + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h0 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopDecrement_stepConfig_borrow_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopDecrement_stepConfig_borrow_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopDecrement_stepConfig_borrow_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp true, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

/-- After-decrement configuration: if the first `j` counter cells are `0` and cell `j` is `1`
(`j ≤ L`), then after `j + 1` steps the decrement is done — phase `1`, head on cell `j`, and the tape
has cells `[0, j)` set to `1`, cell `j` cleared to `0`, and everything beyond unchanged.  Dual of
`selfLoopIncrement_runConfig_stop`. -/
theorem selfLoopDecrement_runConfig_stop {L : Nat} (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_zeros : ∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p = false)
    (h_one : ∀ hb : j < selfLoopDecrement.toPhased.toTM.tapeLength L,
      (selfLoopDecrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = true) :
    (((TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
        (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
            (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) < j then true
                else if (p : Nat) = j then false
                else (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopDecrement_runConfig_borrow x j hj h_zeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
    (selfLoopDecrement.toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = true := by
    rw [htp, if_neg (show ¬ (c.head : Nat) < j by rw [hhd]; omega), hhead_eq]
    exact h_one _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopDecrement_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopDecrement_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopDecrement_stepConfig_stop_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      simp [hhd]
    · rw [Configuration.write_other c hp false, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      split_ifs <;> rfl

/-- Semantic correctness of the self-loop decrement: if the counter window `[0, k)` has its first `j`
cells `0` and cell `j` is `1` (`j < k ≤ L`, so the value is positive), then after `j + 1` steps its
little-endian value has decreased by exactly one (stated as `before = after + 1` to avoid `Nat`
truncation).  A direct plug-in of the after-stop tape characterization into the dual bit-flip
arithmetic `counterValue_first_one_diff`. -/
theorem selfLoopDecrement_runConfig_counterValue {L : Nat} (x : Boolcube.Point L) (j k : Nat)
    (hjk : j < k) (hk : k ≤ L)
    (h_zeros : ∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p = false)
    (h_one : ∀ hb : j < selfLoopDecrement.toPhased.toTM.tapeLength L,
      (selfLoopDecrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = true) :
    counterValue (selfLoopDecrement.toPhased.toTM.initialConfig x) 0 k
      = counterValue (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)) 0 k + 1 := by
  obtain ⟨_, _, htp⟩ := selfLoopDecrement_runConfig_stop x j (by omega) h_zeros h_one
  refine counterValue_first_one_diff
    (selfLoopDecrement.toPhased.toTM.initialConfig x)
    (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
      (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)) 0 j k hjk
    (by show (0 : Nat) + k ≤ L + L + 1; omega) ?_ ?_ ?_ ?_ ?_
  · intro i hij hb
    simp only [Nat.zero_add] at hb ⊢
    exact h_zeros ⟨i, hb⟩ hij
  · intro hb
    simp only [Nat.zero_add] at hb ⊢
    exact h_one hb
  · intro i hij hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨i, hb⟩, if_pos hij]
  · intro hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨j, hb⟩, if_neg (Nat.lt_irrefl j), if_pos rfl]
  · intro i hji hik hb
    simp only [Nat.zero_add] at hb ⊢
    rw [htp ⟨i, hb⟩, if_neg (show ¬ i < j by omega), if_neg (show ¬ i = j by omega)]

/-! ### Done-phase stability (idle after the decrement)

Dual of the increment's done-phase stability: once the decrement reaches the done phase (`1`), every
further step preserves the entire configuration, pinning the counter after its full allotted runtime. -/

/-- A single step from the done phase (`1`) preserves the phase, head, and tape. -/
theorem selfLoopDecrement_stepConfig_done {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := selfLoopDecrement.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, selfLoopDecrement, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- Iterated done-phase stability: from a done configuration (phase `1`), running any number of steps
keeps the phase at `1`, the head fixed, and the tape unchanged. -/
theorem selfLoopDecrement_runConfig_done {L : Nat}
    (c : Configuration (M := selfLoopDecrement.toPhased.toTM) L)
    (hdone : (c.state.fst : Nat) = 1) (j : Nat) :
    ((TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j).state.fst : Nat) = 1
    ∧ (TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j).head = c.head
    ∧ (TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j).tape = c.tape := by
  induction j with
  | zero => exact ⟨hdone, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨hph, hhd, htp⟩ := ih
      rw [TM.runConfig_succ]
      obtain ⟨hph2, hhd2, htp2⟩ :=
        selfLoopDecrement_stepConfig_done
          (TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j)
          (i := (TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j).state.fst)
          (s := (TM.runConfig (M := selfLoopDecrement.toPhased.toTM) c j).state.snd) hph rfl
      exact ⟨hph2, by rw [hhd2, hhd], by rw [htp2, htp]⟩

/-- Full-runtime correctness of the self-loop decrement: running it for its entire declared runtime
(`TM.run`, `= L` steps) on a positive counter window `[0, k)` with first-one at `j` (`j < k ≤ L`)
decreases the little-endian value by exactly one (`before = after + 1`).  Combines the
`counterValue` result at step `j + 1` with done-phase idle stability for the remaining steps, via
`runConfig_add` and `counterValue_eq_of_tape_eq`.  Dual headline to
`selfLoopIncrement_run_counterValue`. -/
theorem selfLoopDecrement_run_counterValue {L : Nat} (x : Boolcube.Point L) (j k : Nat)
    (hjk : j < k) (hk : k ≤ L)
    (h_zeros : ∀ p : Fin (selfLoopDecrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopDecrement.toPhased.toTM.initialConfig x).tape p = false)
    (h_one : ∀ hb : j < selfLoopDecrement.toPhased.toTM.tapeLength L,
      (selfLoopDecrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = true) :
    counterValue (selfLoopDecrement.toPhased.toTM.initialConfig x) 0 k
      = counterValue (TM.run (M := selfLoopDecrement.toPhased.toTM) (n := L) x) 0 k + 1 := by
  obtain ⟨hph_stop, _, _⟩ := selfLoopDecrement_runConfig_stop x j (by omega) h_zeros h_one
  have hrun : TM.run (M := selfLoopDecrement.toPhased.toTM) (n := L) x
      = TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (selfLoopDecrement.toPhased.toTM.initialConfig x) L := rfl
  have hadd : TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
        (selfLoopDecrement.toPhased.toTM.initialConfig x) L
      = TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
          (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
            (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)) (L - (j + 1)) := by
    rw [← TM.runConfig_add]; congr 1; omega
  obtain ⟨_, _, htp_idle⟩ := selfLoopDecrement_runConfig_done
    (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
      (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)) hph_stop (L - (j + 1))
  rw [hrun, hadd,
    counterValue_eq_of_tape_eq _
      (TM.runConfig (M := selfLoopDecrement.toPhased.toTM)
        (selfLoopDecrement.toPhased.toTM.initialConfig x) (j + 1)) 0 k
      (fun p _ _ => congrFun htp_idle p)]
  exact selfLoopDecrement_runConfig_counterValue x j k hjk hk h_zeros h_one

end ContractExpansion
end Frontier
end Pnp4
