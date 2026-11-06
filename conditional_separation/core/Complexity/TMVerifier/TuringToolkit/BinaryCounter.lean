import Complexity.TMVerifier.TuringToolkit.Foundation

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace BinaryCounter

/-- `k`-bit binary counter increment, as a `PhasedProgram`.  The head
must start at the counter's LSB cell; after `k+1` steps the counter
has been incremented modulo `2^k` and the machine sits in its
accepting phase. -/
def incrementProgram (k : Nat) : PhasedProgram.{0} where
  numPhases := k + 2
  phaseState := fun _ => Unit
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨k + 1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if hi : i.val < k then
      if b then
        -- bit = 1: carry.  Write 0, advance to phase `i+1`, move right.
        (⟨⟨i.val + 1, by omega⟩, ()⟩, false, Move.right)
      else
        -- bit = 0: increment complete.  Write 1, jump to accepting.
        (⟨⟨k + 1, by omega⟩, ()⟩, true, Move.stay)
    else
      -- `i.val ≥ k`: overflow phase or accepting phase.  Preserve bit,
      -- jump to accepting phase, no head movement.
      (⟨⟨k + 1, by omega⟩, ()⟩, b, Move.stay)
  timeBound := fun _ => k + 1

/-! ### Transparent structural projections -/

@[simp] theorem incrementProgram_numPhases (k : Nat) :
    (incrementProgram k).numPhases = k + 2 := rfl

@[simp] theorem incrementProgram_startPhase (k : Nat) :
    ((incrementProgram k).startPhase : Fin (k + 2)).val = 0 := rfl

@[simp] theorem incrementProgram_acceptPhase (k : Nat) :
    ((incrementProgram k).acceptPhase : Fin (k + 2)).val = k + 1 := rfl

@[simp] theorem incrementProgram_timeBound (k n : Nat) :
    (incrementProgram k).timeBound n = k + 1 := rfl

@[simp] theorem incrementProgram_phaseState (k : Nat) (i : Fin (k + 2)) :
    (incrementProgram k).phaseState i = Unit := rfl

/-!
### Head-position invariants for `incrementProgram`

The transition function of `incrementProgram k` only returns
`Move.right` or `Move.stay` — never `Move.left`.  Lifting this to the
compiled TM gives `TMNeverMovesLeft` and, via Session 6c generic
lemmas, head-monotonicity.  Combined with Session 6b's upper bound
and Session 5's tape-invariant lemmas, we obtain full tape
preservation outside `[initial_head, initial_head + k + 1)` — the
counter's working window.
-/

/-- `incrementProgram k`'s transition function never issues
`Move.left`. -/
theorem incrementProgram_transition_never_left (k : Nat)
    (i : Fin ((incrementProgram k).numPhases))
    (q : (incrementProgram k).phaseState i) (b : Bool) :
    ((incrementProgram k).transition i q b).snd.snd ≠ Move.left := by
  -- The transition splits on `i.val < k` and (inside) `b`.  Each of
  -- the three resulting branches emits `Move.right` or `Move.stay`.
  by_cases hi : i.val < k
  · by_cases hb : b = true
    · -- `i.val < k ∧ b = true` → `Move.right`.
      simp [incrementProgram, hi, hb]
    · -- `i.val < k ∧ b = false` → `Move.stay`.
      simp [incrementProgram, hi, hb]
  · -- `¬ (i.val < k)` → `Move.stay`.
    simp [incrementProgram, hi]

/-- Lift to the compiled TM: `(incrementProgram k).toTM` is
never-left. -/
theorem incrementProgram_toTM_never_moves_left (k : Nat) :
    TMNeverMovesLeft (incrementProgram k).toTM := by
  intro s b
  rcases s with ⟨i, q⟩
  -- `.toTM.step ⟨i, q⟩ b`'s third component equals
  -- `(transition i q b).snd.snd`.
  show ((incrementProgram k).transition i q b).snd.snd ≠ Move.left
  exact incrementProgram_transition_never_left k i q b

/-- Tape-preservation corollary: after running `incrementProgram k`
for its full `k + 1`-step budget, every tape cell *outside*
`[c.head, c.head + k + 1)` keeps its original value. -/
theorem incrementProgram_tape_preserved_outside {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (i : Fin ((incrementProgram k).toTM.tapeLength n))
    (hout : (i : ℕ) < (c.head : ℕ) ∨ (c.head : ℕ) + (k + 1) ≤ (i : ℕ)) :
    (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).tape i =
      c.tape i := by
  refine runConfig_tape_eq_outside_range
    (c := c) (k := k + 1)
    (a := (c.head : ℕ)) (b := (c.head : ℕ) + (k + 1))
    ?_ i hout
  intro j hj
  refine ⟨?_, ?_⟩
  · exact runConfig_head_val_ge_of_never_left c j
      (incrementProgram_toTM_never_moves_left k)
  · have := runConfig_head_val_le (M := (incrementProgram k).toTM) c j
    omega

/-!
### Session 7: Counter value semantics

`counterValue c start k` interprets the `k` tape cells starting at
position `start` as a little-endian binary number (LSB at position
`start`).  Cells outside the tape contribute `0`, so the function is
total.

The recursive shape (base case `k = 0`, step adding the `k`-th bit's
contribution `2^k`) makes induction-on-`k` the natural proof strategy
for all downstream correctness statements.

Session 7 delivers only the *definition* and a handful of structural
and bound lemmas.  The full `incrementProgram_correct` theorem —
"after `k+1` steps the counter value is `(prev + 1) mod 2^k`" — is
reserved for Session 7b, where case analysis on the first-zero bit
position discharges both the ripple-carry and overflow branches.
-/

/-- Little-endian binary interpretation of `k` tape cells starting at
position `start`.  Cells outside the tape contribute `0`. -/
def counterValue {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    counterValue c start k +
      (if hi : start + k < M.tapeLength n then
        (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
      else 0)

@[simp] theorem counterValue_zero {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    counterValue c start 0 = 0 := rfl

theorem counterValue_succ {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    counterValue c start (k + 1) =
      counterValue c start k +
        (if hi : start + k < M.tapeLength n then
          (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
        else 0) := rfl

/-- Each bit contributes at most `2^i` to the counter value, so the
total is strictly less than `2^k`.  Proved by straight induction on
`k`; the "cell out of range" branch contributes `0` (trivially
bounded) and the "cell in range" branch contributes `0` or `2^k`. -/
theorem counterValue_lt_two_pow {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    counterValue c start k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [counterValue_succ]
    -- Abstract the added term: the bit's contribution at position
    -- `start + k`, which is either `0` or `2^k`.
    set added : Nat :=
      (if hi : start + k < M.tapeLength n then
        (if c.tape ⟨start + k, hi⟩ then 2 ^ k else 0)
      else 0) with hadded
    have hadd_le : added ≤ 2 ^ k := by
      simp only [hadded]
      split_ifs
      · exact le_refl _
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [pow_succ]
      omega
    -- `counterValue + added < 2^k + added ≤ 2^k + 2^k = 2^(k+1)`.
    -- Combined in a single `omega` on the abstract terms.
    rw [hpow]
    omega

/-- The counter value is always non-negative (trivially, since it is
a `Nat`).  Stated explicitly for readability when combined with
`counterValue_lt_two_pow` as a range `[0, 2^k)`. -/
theorem counterValue_nonneg {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start k : Nat) :
    0 ≤ counterValue c start k := Nat.zero_le _

/-!
### Session 7b: Tape agreement ⇒ counter agreement

Bridge lemma between tape-level equality (Session 5) and
semantic-level equality (Session 7).  If two configurations have
identical tape contents in the counter region `[start, start + k)`,
they have identical counter values.

Combined with `runConfig_tape_eq_on_region`, this lets us prove
`counterValue` is preserved across any execution whose head avoids
the counter region.
-/

/-- If two configurations agree on every tape cell in the region
`[start, start + k)`, they have the same `counterValue` there.

The hypothesis is stated on `p : Fin (M.tapeLength n)` rather than raw
`Nat` offsets so that out-of-range indices are simply never mentioned
— they are handled by the "cell out of tape bounds" branch of
`counterValue` (contributing `0` uniformly). -/
theorem counterValue_eq_of_tape_eq {M : TM.{u}} {n : Nat}
    (c1 c2 : Configuration (M := M) n) (start : Nat) :
    ∀ k : Nat,
      (∀ p : Fin (M.tapeLength n),
         start ≤ (p : ℕ) → (p : ℕ) < start + k →
         c1.tape p = c2.tape p) →
      counterValue c1 start k = counterValue c2 start k
  | 0, _ => rfl
  | k + 1, h => by
    rw [counterValue_succ, counterValue_succ]
    have h_prefix : ∀ p : Fin (M.tapeLength n),
        start ≤ (p : ℕ) → (p : ℕ) < start + k →
        c1.tape p = c2.tape p :=
      fun p h1 h2 => h p h1 (by omega)
    rw [counterValue_eq_of_tape_eq c1 c2 start k h_prefix]
    -- Inner added-bit contributions: case on whether cell in range.
    by_cases hbound : start + k < M.tapeLength n
    · simp only [dif_pos hbound]
      have hval : ((⟨start + k, hbound⟩ : Fin (M.tapeLength n)) : ℕ)
          = start + k := rfl
      rw [h ⟨start + k, hbound⟩ (by rw [hval]; omega) (by rw [hval]; omega)]
    · simp only [dif_neg hbound]

/-- Specialisation: if the head never enters the counter region
`[start, start + width)` during `runConfig c steps`, the counter
value at `start` is preserved. -/
theorem counterValue_runConfig_eq_of_head_avoids_region
    {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (steps start width : Nat)
    (h : ∀ i, i < steps →
         ¬ (start ≤ ((TM.runConfig (M := M) c i).head : ℕ) ∧
            ((TM.runConfig (M := M) c i).head : ℕ) < start + width)) :
    counterValue (TM.runConfig (M := M) c steps) start width =
      counterValue c start width := by
  apply counterValue_eq_of_tape_eq
  intro p hge hlt
  -- `p` lies in the counter region; by the hypothesis, the head
  -- never equals `p` during any of the `steps` iterations, so
  -- Session 5's `runConfig_tape_eq_on_region` preserves the cell.
  apply runConfig_tape_eq_on_region
    (R := fun q => start ≤ (q : ℕ) ∧ (q : ℕ) < start + width)
  · intro i hi hR
    exact h i hi hR
  · exact ⟨hge, hlt⟩

/-!
### Base case: `incrementProgram 0` correctness

The `k = 0` counter is degenerate — it has zero cells, so
`counterValue _ _ 0 = 0` unconditionally.  The increment is therefore
a no-op on the semantic level, and the correctness statement reduces
to `0 = (0 + 1) % 1 = 0`.

This is the first concrete instance of the general correctness
theorem `incrementProgram_correct`; Session 7c will prove the
general case via case analysis on the first-zero bit position.
-/

/-- `incrementProgram 0` trivially satisfies the correctness
equation: both sides are `0`. -/
theorem incrementProgram_correct_zero {n : Nat}
    (c : Configuration (M := (incrementProgram 0).toTM) n) :
    counterValue
        (TM.runConfig (M := (incrementProgram 0).toTM) c 1)
        (c.head : ℕ) 0 =
      (counterValue c (c.head : ℕ) 0 + 1) % 2 ^ 0 := by
  simp [counterValue_zero]

/-!
### Session 7c: Stability of the accepting phase

Once `incrementProgram k` reaches phase `k + 1` (the accepting
phase), subsequent `stepConfig` calls preserve the entire
configuration — state, head, and tape.  Reason: the transition
function's `else` branch (`i.val ≥ k`) writes the scanned bit back
unchanged, emits `Move.stay`, and jumps to phase `k + 1`.

This stability is the "post-termination" behaviour essential for
combining incrementProgram with downstream phases (once the counter
has been incremented, the machine does nothing harmful while waiting
for the budget to expire).
-/

/-- Writing the current tape bit back at the head position is a
no-op: the resulting tape function is equal to the original. -/
theorem write_self_eq {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (i : Fin (M.tapeLength n)) :
    c.write i (c.tape i) = c.tape := by
  funext j
  unfold Configuration.write
  split_ifs with h
  · rw [h]
  · rfl

/-- In phase `i` with `k ≤ i.val`, the transition produces
`(⟨k+1, ...⟩, same-bit, Move.stay)`.  Specifically the outer
`if hi : i.val < k` takes the `else` branch. -/
theorem incrementProgram_transition_phase_ge_k (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : k ≤ i.val)
    (q : (incrementProgram k).phaseState i) (b : Bool) :
    ((incrementProgram k).transition i q b).snd.snd = Move.stay ∧
    ((incrementProgram k).transition i q b).snd.fst = b ∧
    ((incrementProgram k).transition i q b).fst.fst.val = k + 1 := by
  have hi_ge : ¬ i.val < k := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi_ge]

/-- `stepConfig` from a configuration whose phase is `≥ k` leaves
the tape and head fixed and forces the state's phase to `k + 1`.
This covers both the "overflow" transition (phase `= k`) and the
"idle in accepting" case (phase `= k + 1`).

* the tape is unchanged (the scanned bit is written back),
* the head is unchanged (`Move.stay`),
* the state's phase component becomes `k + 1`.
-/
theorem incrementProgram_stepConfig_phase_ge_k {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hge : k ≤ c.state.fst.val) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape = c.tape ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 := by
  -- `(toTM.step c.state b).snd.{snd, fst}` definitionally equals
  -- `(transition ...).snd.{snd, fst}`, so the transition-level
  -- hypotheses transfer to the step-level goals by rfl coercion.
  obtain ⟨hmove, hbit, hphase⟩ :=
    incrementProgram_transition_phase_ge_k k (i := c.state.fst) hge
      c.state.snd (c.tape c.head)
  -- Lift each of the transition-level facts to a step-level fact.
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = c.tape c.head := hbit
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = k + 1 := hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
    exact write_self_eq c c.head
  · rw [stepConfig_head, hmove_step]
    simp
  · rw [stepConfig_state]
    exact hphase_step

/-- Specialisation at `c.state.fst.val = k + 1` — the "already in
accepting phase" entry point.  Proof: apply
`incrementProgram_stepConfig_phase_ge_k` with `k ≤ k + 1`. -/
theorem incrementProgram_stepConfig_in_accepting {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape = c.tape ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 :=
  incrementProgram_stepConfig_phase_ge_k c (by rw [h]; omega)

/-- Iterated version: starting from an accepting configuration,
`runConfig` for any number of steps leaves the tape and head fixed
and keeps the state's phase at `k + 1`. -/
theorem incrementProgram_runConfig_in_accepting {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) (j : Nat) :
    (TM.runConfig (M := (incrementProgram k).toTM) c j).tape = c.tape ∧
    (TM.runConfig (M := (incrementProgram k).toTM) c j).head = c.head ∧
    (TM.runConfig (M := (incrementProgram k).toTM) c j).state.fst.val = k + 1 := by
  induction j with
  | zero =>
    refine ⟨rfl, rfl, h⟩
  | succ j ih =>
    obtain ⟨hTape, hHead, hPhase⟩ := ih
    rw [runConfig_succ]
    -- Apply single-step preservation at `runConfig c j`.
    obtain ⟨hT2, hH2, hP2⟩ :=
      incrementProgram_stepConfig_in_accepting
        (TM.runConfig (M := (incrementProgram k).toTM) c j) hPhase
    refine ⟨?_, ?_, ?_⟩
    · rw [hT2, hTape]
    · rw [hH2, hHead]
    · exact hP2

/-- Counter value is preserved once the machine enters the
accepting phase. -/
theorem incrementProgram_counterValue_stable_from_accepting
    {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h : c.state.fst.val = k + 1) (j : Nat) (start width : Nat) :
    counterValue (TM.runConfig (M := (incrementProgram k).toTM) c j)
        start width =
      counterValue c start width := by
  obtain ⟨hTape, _, _⟩ :=
    incrementProgram_runConfig_in_accepting c h j
  -- Two configurations with identical tapes produce the same
  -- counterValue.
  apply counterValue_eq_of_tape_eq
  intro p _ _
  rw [hTape]

/-!
### Session 7d: Active-phase step behaviour

In any active phase (`i.val < k`), the transition splits on the
scanned bit:

* `bit = false` (the counter cell is `0`) — write `1`, jump to the
  accepting phase, `Move.stay`.  This is the "increment complete"
  branch.

* `bit = true` (the counter cell is `1`) — write `0`, advance to
  phase `i + 1`, `Move.right`.  This is the ripple-carry branch.

Both branches are characterised at the transition level and at the
`stepConfig` level.  Together with Session 7c's accepting-phase
stability, these four lemmas describe every possible single-step
transition of `incrementProgram k`.
-/

/-- Transition in an active phase with bit `0`: write `1`, jump to
phase `k + 1`, `Move.stay`. -/
theorem incrementProgram_transition_phase_lt_k_bit_false (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : i.val < k)
    (q : (incrementProgram k).phaseState i) :
    ((incrementProgram k).transition i q false).snd.snd = Move.stay ∧
    ((incrementProgram k).transition i q false).snd.fst = true ∧
    ((incrementProgram k).transition i q false).fst.fst.val = k + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi]

/-- Transition in an active phase with bit `1`: write `0`, advance
to phase `i + 1`, `Move.right`. -/
theorem incrementProgram_transition_phase_lt_k_bit_true (k : Nat)
    {i : Fin ((incrementProgram k).numPhases)} (hi : i.val < k)
    (q : (incrementProgram k).phaseState i) :
    ((incrementProgram k).transition i q true).snd.snd = Move.right ∧
    ((incrementProgram k).transition i q true).snd.fst = false ∧
    ((incrementProgram k).transition i q true).fst.fst.val = i.val + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [incrementProgram, hi]

/-- `stepConfig` in an active phase when the scanned bit is `0`:
the cell is flipped `0 → 1`, the head stays, and the machine jumps
to the accepting phase. -/
theorem incrementProgram_stepConfig_phase_lt_k_bit_false {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hi : c.state.fst.val < k) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape =
        c.write c.head true ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 := by
  obtain ⟨hmove, hbit_out, hphase⟩ :=
    incrementProgram_transition_phase_lt_k_bit_false k
      (i := c.state.fst) hi c.state.snd
  -- Lift transition-level facts to step-level via defeq, using
  -- `hbit` to rewrite `c.tape c.head` in the goal to `false`.
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.stay := by rw [hbit]; exact hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = true := by rw [hbit]; exact hbit_out
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = k + 1 := by rw [hbit]; exact hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
  · rw [stepConfig_head, hmove_step]; simp
  · rw [stepConfig_state]; exact hphase_step

/-- `stepConfig` in an active phase when the scanned bit is `1`:
the cell is flipped `1 → 0`, the head moves right, and the machine
advances to phase `i + 1`. -/
theorem incrementProgram_stepConfig_phase_lt_k_bit_true {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (hi : c.state.fst.val < k) (hbit : c.tape c.head = true)
    (hhead_bound : (c.head : ℕ) + 1 < (incrementProgram k).toTM.tapeLength n) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).tape =
        c.write c.head false ∧
    ((TM.stepConfig (M := (incrementProgram k).toTM) c).head : ℕ) =
        (c.head : ℕ) + 1 ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val =
        c.state.fst.val + 1 := by
  obtain ⟨hmove, hbit_out, hphase⟩ :=
    incrementProgram_transition_phase_lt_k_bit_true k
      (i := c.state.fst) hi c.state.snd
  have hmove_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.snd : Move)
        = Move.right := by rw [hbit]; exact hmove
  have hbit_step :
      (((incrementProgram k).toTM.step c.state (c.tape c.head)).snd.fst : Bool)
        = false := by rw [hbit]; exact hbit_out
  have hphase_step :
      ((((incrementProgram k).toTM.step c.state (c.tape c.head)).fst).fst.val : Nat)
        = c.state.fst.val + 1 := by rw [hbit]; exact hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_tape, hbit_step]
  · rw [stepConfig_head, hmove_step,
        Configuration.moveHead_right_lt (c := c) hhead_bound]
  · rw [stepConfig_state]; exact hphase_step

/-!
### Session 7e: Correctness for `k = 1`

The first fully worked-out instance of `incrementProgram_correct`.
For a one-bit counter, the correctness equation is

  `counterValue (runConfig c 2) c.head.val 1 = (counterValue c c.head.val 1 + 1) % 2`.

The proof proceeds by case analysis on the scanned bit:

* `c.tape c.head = false` (counter = 0): step 0 flips the cell to
  `true` (via `stepConfig_phase_lt_k_bit_false`) and enters the
  accepting phase; step 1 is stable (via `stepConfig_phase_ge_k`).
  Final tape at the head reads `true`, so `counterValue = 1 =
  (0 + 1) % 2`.

* `c.tape c.head = true` (counter = 1): step 0 flips the cell to
  `false` and advances the head one cell to the right (phase
  becomes `k = 1`, the overflow phase); step 1 stays put in the
  overflow branch, yielding phase `k + 1 = 2`.  Final tape at the
  head reads `false`, so `counterValue = 0 = (1 + 1) % 2`.

The hypothesis `h_phase` expresses that the caller invokes the
program at phase `0` (the standard entry point), and `h_head`
ensures the tape has room for the right-move in the ripple branch.

This theorem validates the end-to-end machinery built across
Sessions 1–7d.  The general case (`k ≥ 2`) follows the same
structure but requires a parameterised induction on the position
of the first zero bit — deferred.
-/

/-- Auxiliary rewrite: `counterValue` for width `1` is the bit at
`start`, coerced to `Nat`. -/
theorem counterValue_one_eq {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n)
    (p : Fin (M.tapeLength n)) :
    counterValue c (p : ℕ) 1 = (if c.tape p then 1 else 0) := by
  show 0 + (if hi : (p : ℕ) + 0 < M.tapeLength n then
              (if c.tape ⟨(p : ℕ) + 0, hi⟩ then 2 ^ 0 else 0)
            else 0)
        = (if c.tape p then 1 else 0)
  have hp : (p : ℕ) + 0 < M.tapeLength n := by
    have := p.isLt; omega
  have hmk : (⟨(p : ℕ) + 0, hp⟩ : Fin (M.tapeLength n)) = p := by
    apply Fin.ext; simp
  simp [pow_zero]

/-- Correctness of `incrementProgram` for `k = 1`. -/
theorem incrementProgram_correct_one {n : Nat}
    (c : Configuration (M := (incrementProgram 1).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_head : (c.head : ℕ) + 1 < (incrementProgram 1).toTM.tapeLength n) :
    counterValue
        (TM.runConfig (M := (incrementProgram 1).toTM) c 2)
        (c.head : ℕ) 1 =
      (counterValue c (c.head : ℕ) 1 + 1) % 2 ^ 1 := by
  -- `runConfig c 2 = stepConfig (stepConfig c)`.
  rw [show (2 : Nat) = 1 + 1 from rfl, runConfig_succ, runConfig_one]
  set c0 := TM.stepConfig (M := (incrementProgram 1).toTM) c with hc0_def
  have h_phase_lt : c.state.fst.val < 1 := by rw [h_phase]; omega
  -- Case on the initial bit.
  by_cases hbit : c.tape c.head = true
  · -- bit = true path: counter was 1, after increment it's 0.
    -- Step 0: flip to false, move right, phase 1.
    obtain ⟨ht0, hh0, hp0⟩ :=
      incrementProgram_stepConfig_phase_lt_k_bit_true c h_phase_lt hbit h_head
    -- Step 1: we are in phase 1 ≥ k = 1, so stepConfig is idle.
    have hc0_ge : 1 ≤ c0.state.fst.val := by
      rw [hc0_def, hp0, h_phase]
    obtain ⟨ht1, hh1, hp1⟩ :=
      incrementProgram_stepConfig_phase_ge_k c0 hc0_ge
    -- Final tape at head equals c.write c.head false at head = false.
    have h_counter_new :
        counterValue
            (TM.stepConfig (M := (incrementProgram 1).toTM) c0)
            (c.head : ℕ) 1 = 0 := by
      rw [counterValue_one_eq]
      have htape_at_head :
          (TM.stepConfig (M := (incrementProgram 1).toTM) c0).tape c.head
            = false := by
        rw [ht1, hc0_def, ht0]
        exact Configuration.write_self c c.head false
      rw [htape_at_head]; decide
    have h_counter_old : counterValue c (c.head : ℕ) 1 = 1 := by
      rw [counterValue_one_eq, hbit]; decide
    rw [h_counter_new, h_counter_old]
    decide
  · -- bit = false path: counter was 0, after increment it's 1.
    have hbit_false : c.tape c.head = false := by
      cases hval : c.tape c.head with
      | true => exact absurd hval hbit
      | false => rfl
    obtain ⟨ht0, hh0, hp0⟩ :=
      incrementProgram_stepConfig_phase_lt_k_bit_false c h_phase_lt hbit_false
    -- After step 0: phase = k + 1 = 2 ≥ 1. Step 1 is idle.
    have hc0_ge : 1 ≤ c0.state.fst.val := by
      rw [hc0_def, hp0]; omega
    obtain ⟨ht1, hh1, hp1⟩ :=
      incrementProgram_stepConfig_phase_ge_k c0 hc0_ge
    have h_counter_new :
        counterValue
            (TM.stepConfig (M := (incrementProgram 1).toTM) c0)
            (c.head : ℕ) 1 = 1 := by
      rw [counterValue_one_eq]
      have htape_at_head :
          (TM.stepConfig (M := (incrementProgram 1).toTM) c0).tape c.head
            = true := by
        rw [ht1, hc0_def, ht0]
        exact Configuration.write_self c c.head true
      rw [htape_at_head]; decide
    have h_counter_old : counterValue c (c.head : ℕ) 1 = 0 := by
      rw [counterValue_one_eq, hbit_false]
      decide
    rw [h_counter_new, h_counter_old]
    decide

/-!
### Session 7f: First-bit-zero correctness for arbitrary `k`

When the scanned cell (`c.tape c.head`) is `0`, the ripple logic
never triggers — step 0 flips the cell to `1` and jumps straight
to the accepting phase, and the remaining `k` steps are idle.

Under this hypothesis, the counter arithmetic is clean:
* the new counter value differs from the old one only in the LSB
  (the cell at `c.head` itself);
* the LSB was `0`, so `counterValue_old` is even, bounded by
  `2^k - 2`;
* adding `1` does not overflow, so `(old + 1) mod 2^k = old + 1`.

The general `k` case (first-zero bit at arbitrary position + the
all-ones overflow) requires tracking the ripple step-by-step; it
is the largest remaining piece of the counter correctness proof
and is reserved for Session 7g.
-/

/-- If only one position's bit differs between two tape functions,
`counterValue` differs by exactly the signed contribution of that
position.  Specialised to LSB flip `0 → 1`: new value = old + 1. -/
theorem counterValue_of_write_head_true {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (k : Nat)
    (h_old : c.tape c.head = false) :
    ∀ (c' : Configuration (M := M) n),
      c'.tape = c.write c.head true →
      c'.head = c.head →
      counterValue c' (c.head : ℕ) k =
        counterValue c (c.head : ℕ) k +
          (if (c.head : ℕ) < (c.head : ℕ) + k then 1 else 0) := by
  induction k with
  | zero =>
    intro c' htape hhead
    simp
  | succ k ih =>
    intro c' htape hhead
    rw [counterValue_succ, counterValue_succ]
    -- Inductive hypothesis at width `k`.
    have ih_applied :=
      ih c' htape hhead
    -- Split on whether `c.head + k` is the LSB position (`k = 0`).
    by_cases hk0 : k = 0
    · subst hk0
      -- width-1 case: direct computation.
      simp only [counterValue_zero, Nat.zero_add]
      have hp : (c.head : ℕ) + 0 < M.tapeLength n := by
        have := c.head.isLt; omega
      have hmk : (⟨(c.head : ℕ) + 0, hp⟩ : Fin (M.tapeLength n)) = c.head := by
        apply Fin.ext; simp
      simp [htape, h_old]
    · -- `k ≥ 1`.  Use IH on the prefix; the last contribution at
      -- position `c.head + k` is unchanged because `c.head + k
      -- ≠ c.head` (since `k ≥ 1`).
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hne_kpos : (c.head : ℕ) + k ≠ (c.head : ℕ) := by omega
      have hne_fin_pos :
          ∀ (hi : (c.head : ℕ) + k < M.tapeLength n),
            (⟨(c.head : ℕ) + k, hi⟩ : Fin (M.tapeLength n)) ≠ c.head := by
        intro hi hfin_eq
        apply hne_kpos
        exact congrArg Fin.val hfin_eq
      -- IH rewrites the prefix; the `if (c.head < c.head + k)`
      -- branch is taken since `k ≥ 1`.
      have h_lt : (c.head : ℕ) < (c.head : ℕ) + k := by omega
      rw [ih_applied, if_pos h_lt]
      -- Now relate the added-bit terms at position `c.head + k`.
      have h_added_eq :
          (if hi : (c.head : ℕ) + k < M.tapeLength n then
            (if c'.tape ⟨(c.head : ℕ) + k, hi⟩ then 2 ^ k else 0)
          else 0) =
          (if hi : (c.head : ℕ) + k < M.tapeLength n then
            (if c.tape ⟨(c.head : ℕ) + k, hi⟩ then 2 ^ k else 0)
          else 0) := by
        by_cases hbound : (c.head : ℕ) + k < M.tapeLength n
        · simp only [dif_pos hbound]
          rw [htape,
              Configuration.write_other c (hne_fin_pos hbound) true]
        · simp only [dif_neg hbound]
      have h_lt' : (c.head : ℕ) < (c.head : ℕ) + (k + 1) := by omega
      rw [h_added_eq, if_pos h_lt']
      omega

/-!
### Session 7g (opening): ripple-invariant infrastructure

The general `incrementProgram_correct` theorem — handling any
starting bit pattern including the all-ones overflow — requires
tracking the ripple phase-by-phase.  The key lemma is the
**ripple invariant**: starting from phase 0 with the first `j`
bits all `1`, after `j` steps of `incrementProgram k`:

* state phase advances to `j`,
* head moves to `c.head + j`,
* the `j` cells at `[c.head, c.head + j)` are all flipped to `0`,
* all other cells are preserved.

Session 7g-a establishes the invariant for *one* ripple step —
the atomic engine that Session 7g-b will iterate inductively.
-/

/-- One ripple step: if we are in phase `j < k` at head position
`c.head = p + j`, bits `[p, p + j)` are all `0` (already
flipped), bit at head is `1`, and head-bound allows advancing,
then after `stepConfig` we are in phase `j + 1`, head `p + j + 1`,
and bits `[p, p + j + 1)` are all `0`. -/
theorem incrementProgram_ripple_step {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (j : Nat) (hj : j < k)
    (h_phase : c.state.fst.val = j)
    (h_bit : c.tape c.head = true)
    (h_head_bound : (c.head : ℕ) + 1 <
        (incrementProgram k).toTM.tapeLength n) :
    let c' := TM.stepConfig (M := (incrementProgram k).toTM) c
    (c'.state.fst.val = j + 1) ∧
    ((c'.head : ℕ) = (c.head : ℕ) + 1) ∧
    (c'.tape c.head = false) ∧
    (∀ (p : Fin ((incrementProgram k).toTM.tapeLength n)),
       p ≠ c.head → c'.tape p = c.tape p) := by
  have h_phase_lt : c.state.fst.val < k := by rw [h_phase]; exact hj
  obtain ⟨htape_step, hhead_step, hphase_step⟩ :=
    incrementProgram_stepConfig_phase_lt_k_bit_true c h_phase_lt h_bit h_head_bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hphase_step, h_phase]
  · exact hhead_step
  · rw [htape_step]
    exact Configuration.write_self c c.head false
  · intro p hne
    rw [htape_step]
    exact Configuration.write_other c hne false

/-!
### Session 7g-b: iterated ripple invariant

The single-step lemma `incrementProgram_ripple_step` is iterated `j`
times to obtain a full ripple invariant over `[0, j]`.  The
statement captures four simultaneous facts after `j` steps when
the first `j` bits at the counter start are all `1`:

1. `state.fst.val = j`,
2. `head.val = c.head + j`,
3. cells outside `[c.head, c.head + j)` are preserved,
4. cells at `[c.head, c.head + j)` are flipped to `false`.
-/

theorem incrementProgram_ripple_after_j_steps {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + k + 1 ≤
        (incrementProgram k).toTM.tapeLength n) :
    ∀ j, j ≤ k →
    (∀ (i : Nat), i < j →
       ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
       c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true) →
    ((TM.runConfig (M := (incrementProgram k).toTM) c j).state.fst.val = j) ∧
    (((TM.runConfig (M := (incrementProgram k).toTM) c j).head : ℕ) =
        (c.head : ℕ) + j) ∧
    (∀ (p : Fin ((incrementProgram k).toTM.tapeLength n)),
       ((p : ℕ) < (c.head : ℕ) ∨ (c.head : ℕ) + j ≤ (p : ℕ)) →
       (TM.runConfig (M := (incrementProgram k).toTM) c j).tape p = c.tape p) ∧
    (∀ (i : Nat), i < j →
       ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
       (TM.runConfig (M := (incrementProgram k).toTM) c j).tape
           ⟨(c.head : ℕ) + i, hbi⟩ = false) := by
  intro j hjk hones
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show c.state.fst.val = 0; exact h_phase
    · show (c.head : ℕ) = _; omega
    · intros; rfl
    · intros i h; exact absurd h (by omega)
  | succ j' ih =>
    have hj'_le_k : j' ≤ k := by omega
    have hj'_lt_k : j' < k := by omega
    have hones_prev : ∀ (i : Nat), i < j' →
        ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
        c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true := by
      intro i hi hbi; exact hones i (by omega) hbi
    obtain ⟨ihs_phase, ihs_head, ihs_preserve, ihs_zeros⟩ :=
      ih hj'_le_k hones_prev
    -- Set up `c_j` = runConfig c j'.
    set cj' := TM.runConfig (M := (incrementProgram k).toTM) c j' with hcj'
    -- Apply one more step via ripple_step.
    have h_phase_cj' : cj'.state.fst.val = j' := ihs_phase
    have h_head_cj' : (cj'.head : ℕ) = (c.head : ℕ) + j' := ihs_head
    -- Bit at cj'.head is true (from hones at i = j').
    have h_bit_bound : (c.head : ℕ) + j' < (incrementProgram k).toTM.tapeLength n :=
      by omega
    have h_bit_orig : c.tape ⟨(c.head : ℕ) + j', h_bit_bound⟩ = true :=
      hones j' (by omega) h_bit_bound
    -- cj'.head as a Fin equals ⟨c.head + j', _⟩.
    have h_head_fin_eq :
        cj'.head = (⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) := by
      apply Fin.ext; exact h_head_cj'
    -- Thus cj'.tape at its head is true (via preserve on outside region).
    have h_bit_cj' : cj'.tape cj'.head = true := by
      rw [h_head_fin_eq]
      have hout :
          ((⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) : ℕ) < (c.head : ℕ) ∨
          (c.head : ℕ) + j' ≤ ((⟨(c.head : ℕ) + j', h_bit_bound⟩ : Fin _) : ℕ) :=
        Or.inr (by omega)
      rw [ihs_preserve _ hout]; exact h_bit_orig
    have h_head_advance_bound :
        (cj'.head : ℕ) + 1 < (incrementProgram k).toTM.tapeLength n := by
      rw [h_head_cj']; omega
    obtain ⟨rip_phase, rip_head, rip_bit, rip_preserve⟩ :=
      incrementProgram_ripple_step cj' j' hj'_lt_k h_phase_cj'
        h_bit_cj' h_head_advance_bound
    -- Now (runConfig c (j'+1)) = stepConfig cj' by runConfig_succ.
    have hrw : TM.runConfig (M := (incrementProgram k).toTM) c (j' + 1) =
        TM.stepConfig (M := (incrementProgram k).toTM) cj' := by
      rw [runConfig_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrw]; exact rip_phase
    · rw [hrw, rip_head, h_head_cj']; omega
    · intro p hout
      rw [hrw]
      -- Outside region check: p is not cj'.head.
      have hne : p ≠ cj'.head := by
        rw [h_head_fin_eq]
        intro heq
        rcases hout with h1 | h2
        · exact absurd (show ((p : ℕ)) < (c.head : ℕ) from h1)
            (by rw [show (p : ℕ) = (c.head : ℕ) + j' from
                by rw [heq]]; omega)
        · exact absurd (show (c.head : ℕ) + (j' + 1) ≤ (p : ℕ) from h2)
            (by rw [show (p : ℕ) = (c.head : ℕ) + j' from
                by rw [heq]]; omega)
      rw [rip_preserve p hne]
      -- Apply IH's preservation.
      apply ihs_preserve
      rcases hout with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by omega)
    · intro i hi hbi
      rw [hrw]
      -- Case i = j' or i < j'.
      by_cases hij' : i = j'
      · -- i = j': after step, cell at c.head+j' = cj'.head was flipped to false.
        subst hij'
        have hpeq : (⟨(c.head : ℕ) + i, hbi⟩ : Fin _) = cj'.head := by
          apply Fin.ext
          show (c.head : ℕ) + i = _
          rw [h_head_cj']
        rw [hpeq]; exact rip_bit
      · -- i < j': unchanged by the extra step (since position ≠ cj'.head).
        have hij'_lt : i < j' := by omega
        have hne : (⟨(c.head : ℕ) + i, hbi⟩ : Fin _) ≠ cj'.head := by
          rw [h_head_fin_eq]
          intro heq
          apply hij'
          have : (c.head : ℕ) + i = (c.head : ℕ) + j' := congrArg Fin.val heq
          omega
        rw [rip_preserve _ hne]
        exact ihs_zeros i hij'_lt hbi

/-!
### Session 7g-c: Overflow (all-ones) correctness

For the overflow case, all `k` bits in `[c.head, c.head + k)` are
`1`.  After the ripple invariant at `j = k`, phase is `k`, head
is `c.head + k`, and all counter bits are `0`.  One more step at
phase `k` goes straight to phase `k + 1` (accepting) without
touching the counter bits.

The counter value computation:
* before: `counterValue c c.head k = 2^k - 1` (sum of 2^i for i ∈ [0, k))
* after: `counterValue (runConfig c (k+1)) c.head k = 0`
* `(2^k - 1 + 1) mod 2^k = 2^k mod 2^k = 0` ✓
-/

/-- If all `k` tape cells in `[start, start + k)` are `true`, the
`counterValue` at that position is `2^k - 1`. -/
theorem counterValue_of_all_true {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ k, start + k ≤ M.tapeLength n →
    (∀ i, i < k → ∀ (hb : start + i < M.tapeLength n),
       c.tape ⟨start + i, hb⟩ = true) →
    counterValue c start k = 2 ^ k - 1
  | 0, _, _ => by simp
  | k + 1, hbk, h => by
    rw [counterValue_succ]
    have hbk' : start + k ≤ M.tapeLength n := by omega
    have h_prev : ∀ i, i < k → ∀ (hb : start + i < M.tapeLength n),
        c.tape ⟨start + i, hb⟩ = true :=
      fun i hi hb => h i (by omega) hb
    rw [counterValue_of_all_true c start k hbk' h_prev]
    have h_bound_k : start + k < M.tapeLength n := by omega
    rw [dif_pos h_bound_k, h k (by omega) h_bound_k]
    simp only [if_true]
    have hpow : (2:Nat)^(k+1) = 2^k + 2^k := by rw [pow_succ]; omega
    have hpow_pos : (1:Nat) ≤ 2^k := Nat.one_le_two_pow
    omega

/-- If all tape cells in `[start, start + k)` are `false`, the
`counterValue` is `0`. -/
theorem counterValue_of_all_false {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ k,
    (∀ i, i < k → ∀ (hb : start + i < M.tapeLength n),
       c.tape ⟨start + i, hb⟩ = false) →
    counterValue c start k = 0
  | 0, _ => by simp
  | k + 1, h => by
    rw [counterValue_succ]
    have h_prev : ∀ i, i < k → ∀ (hb : start + i < M.tapeLength n),
        c.tape ⟨start + i, hb⟩ = false :=
      fun i hi hb => h i (by omega) hb
    rw [counterValue_of_all_false c start k h_prev]
    by_cases h_bound_k : start + k < M.tapeLength n
    · rw [dif_pos h_bound_k, h k (by omega) h_bound_k]
      simp
    · rw [dif_neg h_bound_k]

/-- Step in the overflow phase `j = k`: the machine writes the bit
back unchanged, head stays, phase advances to `k + 1`. -/
theorem incrementProgram_stepConfig_phase_eq_k {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = k) :
    (TM.stepConfig (M := (incrementProgram k).toTM) c).state.fst.val = k + 1 ∧
    (TM.stepConfig (M := (incrementProgram k).toTM) c).head = c.head ∧
    ∀ (p : Fin ((incrementProgram k).toTM.tapeLength n)),
      p ≠ c.head →
      (TM.stepConfig (M := (incrementProgram k).toTM) c).tape p = c.tape p := by
  have h_phase_ge : c.state.fst.val ≥ k := by omega
  -- The `phase_ge_k` step: preserves tape at `p ≠ c.head`, writes bit
  -- back at c.head, jumps to phase k+1, head stays.
  obtain ⟨htape, hhead, hphase⟩ :=
    incrementProgram_stepConfig_phase_ge_k c h_phase_ge
  refine ⟨hphase, hhead, ?_⟩
  intro p _hne
  rw [htape]

/-- Overflow correctness: starting from phase 0 with all k bits
`true`, after `k + 1` steps the counter value is 0 (i.e.
`(2^k - 1 + 1) mod 2^k`). -/
theorem incrementProgram_correct_all_ones {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + k + 1 ≤
        (incrementProgram k).toTM.tapeLength n)
    (h_ones : ∀ i, i < k →
       ∀ (hb : (c.head : ℕ) + i <
           (incrementProgram k).toTM.tapeLength n),
       c.tape ⟨(c.head : ℕ) + i, hb⟩ = true) :
    counterValue
        (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
        (c.head : ℕ) k =
      (counterValue c (c.head : ℕ) k + 1) % 2 ^ k := by
  -- Step 1: after k steps (ripple through all 1s) we are at phase k,
  -- head c.head + k, and bits [c.head, c.head + k) are all false.
  obtain ⟨rip_phase, rip_head, _rip_preserve, rip_zeros⟩ :=
    incrementProgram_ripple_after_j_steps c h_phase h_bound k le_rfl h_ones
  set ck := TM.runConfig (M := (incrementProgram k).toTM) c k with hck
  -- Step 2: one more step advances phase k → k + 1 without touching
  -- the counter bits.
  obtain ⟨over_phase, over_head, over_preserve⟩ :=
    incrementProgram_stepConfig_phase_eq_k ck rip_phase
  have hrw : TM.runConfig (M := (incrementProgram k).toTM) c (k + 1) =
      TM.stepConfig (M := (incrementProgram k).toTM) ck := by
    rw [runConfig_succ]
  -- The final tape still has all k counter bits = 0.
  have h_final_zeros : ∀ i, i < k →
      ∀ (hb : (c.head : ℕ) + i <
          (incrementProgram k).toTM.tapeLength n),
      (TM.stepConfig (M := (incrementProgram k).toTM) ck).tape
          ⟨(c.head : ℕ) + i, hb⟩ = false := by
    intro i hi hb
    have hne : (⟨(c.head : ℕ) + i, hb⟩ : Fin _) ≠ ck.head := by
      intro heq
      have hval : (c.head : ℕ) + i = (ck.head : ℕ) := congrArg Fin.val heq
      rw [rip_head] at hval
      omega
    rw [over_preserve _ hne]; exact rip_zeros i hi hb
  rw [hrw]
  -- Now compute the counter values.
  have h_old : counterValue c (c.head : ℕ) k = 2 ^ k - 1 :=
    counterValue_of_all_true c (c.head : ℕ) k (by omega) h_ones
  have h_new : counterValue
      (TM.stepConfig (M := (incrementProgram k).toTM) ck) (c.head : ℕ) k = 0 :=
    counterValue_of_all_false _ (c.head : ℕ) k h_final_zeros
  rw [h_old, h_new]
  -- Final arithmetic: (2^k - 1 + 1) % 2^k = 2^k % 2^k = 0.
  have hpow_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have : (2 ^ k - 1 + 1) % 2 ^ k = 0 := by
    have : (2 ^ k - 1 + 1) = 2 ^ k := by omega
    rw [this, Nat.mod_self]
  exact this.symm

/-!
### Session 7g-d: First-zero correctness

For the first-zero case at position `j < k`, the before/after
tapes differ as follows:
* cells `[c.head, c.head + j)`: `1 → 0` (first `j` ripple flips),
* cell `c.head + j`: `0 → 1` (terminating write),
* cells `[c.head + j + 1, c.head + k)`: unchanged.

The arithmetic: before has value `(2^j - 1) + R` and after has
`2^j + R`, where `R` is the contribution of cells above `j`.  The
difference is exactly `+1`, and `after < 2^k` gives
`(before + 1) mod 2^k = before + 1 = after`.

The `counterValue_first_zero_diff` lemma packages this arithmetic
generically — no reference to `incrementProgram` — making the
final correctness theorem a straight plug-in.
-/

/-- Generic bit-flip arithmetic: if tape `T'` is obtained from tape `T`
by flipping the first `j` bits of the counter window from 1 to 0,
the bit at position `j` from 0 to 1, and leaving everything beyond
`j` unchanged, then `counterValue T' = counterValue T + 1`. -/
theorem counterValue_first_zero_diff {M : TM.{u}} {n : Nat}
    (c c' : Configuration (M := M) n) (start j : Nat) :
    ∀ k, j < k → start + k ≤ M.tapeLength n →
    (∀ i, i < j → ∀ (hb : start + i < M.tapeLength n),
       c.tape ⟨start + i, hb⟩ = true) →
    (∀ (hb : start + j < M.tapeLength n),
       c.tape ⟨start + j, hb⟩ = false) →
    (∀ i, i < j → ∀ (hb : start + i < M.tapeLength n),
       c'.tape ⟨start + i, hb⟩ = false) →
    (∀ (hb : start + j < M.tapeLength n),
       c'.tape ⟨start + j, hb⟩ = true) →
    (∀ i, j < i → i < k → ∀ (hb : start + i < M.tapeLength n),
       c'.tape ⟨start + i, hb⟩ = c.tape ⟨start + i, hb⟩) →
    counterValue c' start k = counterValue c start k + 1 := by
  intro k hjk h_bound h_ones h_bit_old h_zeros h_bit_new h_beyond
  induction k with
  | zero => omega
  | succ k' ih =>
    rw [counterValue_succ, counterValue_succ]
    by_cases hcase : k' = j
    · -- Base of the decomposition: k' = j, so the added bit IS the flipped one.
      rw [hcase]
      have h_bound_j : start + j < M.tapeLength n := by omega
      have h_bound_j_le : start + j ≤ M.tapeLength n := by omega
      -- Compute `counterValue c start j` and `counterValue c' start j`.
      have h_old_lo : counterValue c start j = 2 ^ j - 1 :=
        counterValue_of_all_true c start j h_bound_j_le h_ones
      have h_new_lo : counterValue c' start j = 0 :=
        counterValue_of_all_false c' start j h_zeros
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

/-- First-zero correctness of `incrementProgram` at arbitrary `k`:
when the first zero-bit lies at position `j < k` (so the counter
is NOT all ones), after the full k+1-step execution the counter
value increases by exactly 1 (no mod truncation). -/
theorem incrementProgram_correct_first_zero_at {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + k + 1 ≤
        (incrementProgram k).toTM.tapeLength n)
    (j : Nat) (hjk : j < k)
    (h_ones : ∀ i, i < j →
       ∀ (hb : (c.head : ℕ) + i <
           (incrementProgram k).toTM.tapeLength n),
       c.tape ⟨(c.head : ℕ) + i, hb⟩ = true)
    (h_zero_at_j : ∀ (hb : (c.head : ℕ) + j <
        (incrementProgram k).toTM.tapeLength n),
      c.tape ⟨(c.head : ℕ) + j, hb⟩ = false) :
    counterValue
        (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
        (c.head : ℕ) k =
      (counterValue c (c.head : ℕ) k + 1) % 2 ^ k := by
  -- Step 1: after j ripple steps, phase = j, head = c.head + j, first j
  -- bits flipped to 0.
  have h_ones_for_ripple : ∀ (i : Nat), i < j →
      ∀ (hbi : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
      c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true := h_ones
  have hj_le_k : j ≤ k := le_of_lt hjk
  obtain ⟨rip_phase, rip_head, rip_preserve, rip_zeros⟩ :=
    incrementProgram_ripple_after_j_steps c h_phase h_bound j hj_le_k
      h_ones_for_ripple
  set cj := TM.runConfig (M := (incrementProgram k).toTM) c j with hcj
  -- Step 2: at cj, bit at head is false (same as bit at c.head+j in c).
  have h_bit_bound : (c.head : ℕ) + j < (incrementProgram k).toTM.tapeLength n :=
    by omega
  have h_bit_orig : c.tape ⟨(c.head : ℕ) + j, h_bit_bound⟩ = false :=
    h_zero_at_j h_bit_bound
  have h_head_fin_eq :
      cj.head = (⟨(c.head : ℕ) + j, h_bit_bound⟩ : Fin _) := by
    apply Fin.ext; exact rip_head
  have h_bit_cj : cj.tape cj.head = false := by
    rw [h_head_fin_eq]
    have hout :
        ((⟨(c.head : ℕ) + j, h_bit_bound⟩ : Fin _) : ℕ) < (c.head : ℕ) ∨
        (c.head : ℕ) + j ≤ ((⟨(c.head : ℕ) + j, h_bit_bound⟩ : Fin _) : ℕ) :=
      Or.inr (by omega)
    rw [rip_preserve _ hout]; exact h_bit_orig
  -- Step 3: one more step at cj — phase j < k, bit false → writes 1,
  -- jumps to phase k+1, head stays.
  have h_phase_lt_k : cj.state.fst.val < k := by rw [rip_phase]; exact hjk
  obtain ⟨fin_tape, fin_head, fin_phase⟩ :=
    incrementProgram_stepConfig_phase_lt_k_bit_false cj h_phase_lt_k h_bit_cj
  set cj1 := TM.stepConfig (M := (incrementProgram k).toTM) cj with hcj1
  -- Step 4: runConfig c (j+1) = cj1.
  have h_j1_eq : TM.runConfig (M := (incrementProgram k).toTM) c (j + 1) = cj1 := by
    rw [runConfig_succ]
  -- Step 5: remaining k - j steps idle (phase k+1 accepting).
  have h_phase_cj1 : cj1.state.fst.val = k + 1 := fin_phase
  -- Steps j+1..k+1: from cj1, run k - j more steps.
  have h_k1_eq : k + 1 = (j + 1) + (k - j) := by omega
  have h_runConfig_split :
      TM.runConfig (M := (incrementProgram k).toTM) c (k + 1) =
        TM.runConfig (M := (incrementProgram k).toTM) cj1 (k - j) := by
    rw [h_k1_eq, runConfig_add, ← h_j1_eq]
  obtain ⟨final_tape, final_head, _⟩ :=
    incrementProgram_runConfig_in_accepting cj1 h_phase_cj1 (k - j)
  have h_final_tape : (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).tape =
      cj1.tape := by
    rw [h_runConfig_split]; exact final_tape
  -- Step 6: compute cj1.tape at each position via ripple zeros + write.
  -- First j bits in cj1: same as in cj (the step at cj wrote only at cj.head).
  have h_cj1_first_j_zero : ∀ i, i < j →
      ∀ (hb : (c.head : ℕ) + i <
          (incrementProgram k).toTM.tapeLength n),
      cj1.tape ⟨(c.head : ℕ) + i, hb⟩ = false := by
    intro i hi hb
    rw [hcj1, fin_tape]
    have hne : (⟨(c.head : ℕ) + i, hb⟩ : Fin _) ≠ cj.head := by
      rw [h_head_fin_eq]; intro heq
      have : (c.head : ℕ) + i = (c.head : ℕ) + j := congrArg Fin.val heq
      omega
    rw [Configuration.write_other cj hne]
    exact rip_zeros i hi hb
  -- Bit at position j in cj1: `true` (just written).
  have h_cj1_bit_at_j : ∀ (hb : (c.head : ℕ) + j <
      (incrementProgram k).toTM.tapeLength n),
      cj1.tape ⟨(c.head : ℕ) + j, hb⟩ = true := by
    intro hb
    rw [hcj1, fin_tape]
    have heq : (⟨(c.head : ℕ) + j, hb⟩ : Fin _) = cj.head := by
      apply Fin.ext; rw [rip_head]
    rw [heq]; exact Configuration.write_self cj cj.head true
  -- Beyond position j: cj1.tape = c.tape (via rip_preserve + write_other).
  have h_cj1_beyond : ∀ i, j < i → i < k →
      ∀ (hb : (c.head : ℕ) + i <
          (incrementProgram k).toTM.tapeLength n),
      cj1.tape ⟨(c.head : ℕ) + i, hb⟩ = c.tape ⟨(c.head : ℕ) + i, hb⟩ := by
    intro i hi hik hb
    rw [hcj1, fin_tape]
    have hne : (⟨(c.head : ℕ) + i, hb⟩ : Fin _) ≠ cj.head := by
      rw [h_head_fin_eq]; intro heq
      have : (c.head : ℕ) + i = (c.head : ℕ) + j := congrArg Fin.val heq
      omega
    rw [Configuration.write_other cj hne]
    have hout :
        ((⟨(c.head : ℕ) + i, hb⟩ : Fin _) : ℕ) < (c.head : ℕ) ∨
        (c.head : ℕ) + j ≤ ((⟨(c.head : ℕ) + i, hb⟩ : Fin _) : ℕ) := by
      right
      show (c.head : ℕ) + j ≤ (c.head : ℕ) + i
      omega
    exact rip_preserve _ hout
  -- Step 7: apply the generic bit-flip arithmetic.
  have h_cv_eq : counterValue
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)) (c.head : ℕ) k =
    counterValue cj1 (c.head : ℕ) k := by
    apply counterValue_eq_of_tape_eq
    intro p _ _
    rw [h_final_tape]
  rw [h_cv_eq]
  have h_diff := counterValue_first_zero_diff c cj1 (c.head : ℕ) j k hjk
    (by omega) h_ones h_zero_at_j h_cj1_first_j_zero h_cj1_bit_at_j h_cj1_beyond
  rw [h_diff]
  -- Step 8: mod doesn't truncate — counterValue c + 1 < 2^k since
  -- counterValue cj1 < 2^k.
  have h_new_lt := counterValue_lt_two_pow cj1 (c.head : ℕ) k
  rw [h_diff] at h_new_lt
  exact (Nat.mod_eq_of_lt h_new_lt).symm

/-- First-bit-zero correctness for arbitrary `k ≥ 1`: when the
scanned cell is `0`, running `incrementProgram k` for its full
budget adds exactly `1` to the counter value (without mod
truncation, because the LSB was `0`, so the value was even and
`≤ 2^k - 2`). -/
theorem incrementProgram_correct_first_bit_zero {k : Nat} (hk : 0 < k)
    {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bit : c.tape c.head = false) :
    counterValue
        (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
        (c.head : ℕ) k =
      (counterValue c (c.head : ℕ) k + 1) % 2 ^ k := by
  -- Step 0: flips the head cell to `true`, enters accepting phase.
  have h_phase_lt : c.state.fst.val < k := by rw [h_phase]; exact hk
  obtain ⟨ht0, hh0, hp0⟩ :=
    incrementProgram_stepConfig_phase_lt_k_bit_false c h_phase_lt h_bit
  -- Steps 1..k: idle in accepting phase.
  set c0 := TM.stepConfig (M := (incrementProgram k).toTM) c with hc0_def
  -- `runConfig c (k+1) = runConfig c0 k` via `runConfig_add`.
  have h_rewrite :
      TM.runConfig (M := (incrementProgram k).toTM) c (k + 1) =
        TM.runConfig (M := (incrementProgram k).toTM) c0 k := by
    rw [show k + 1 = 1 + k from by omega, runConfig_add, runConfig_one]
  have h_phase_accept : c0.state.fst.val = k + 1 := by rw [hc0_def]; exact hp0
  obtain ⟨ht_final, hh_final, _⟩ :=
    incrementProgram_runConfig_in_accepting c0 h_phase_accept k
  -- Combine: the final tape equals `c.write c.head true`.
  have h_final_tape :
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).tape =
        c.write c.head true := by
    rw [h_rewrite, ht_final, hc0_def, ht0]
  have h_final_head :
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1)).head = c.head := by
    rw [h_rewrite, hh_final, hc0_def, hh0]
  -- Apply the bit-flip arithmetic lemma.
  have h_counter_new :
      counterValue
          (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
          (c.head : ℕ) k =
        counterValue c (c.head : ℕ) k + 1 := by
    have := counterValue_of_write_head_true c k h_bit
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
      h_final_tape h_final_head
    rw [this]
    have h_lt : (c.head : ℕ) < (c.head : ℕ) + k := by omega
    simp [h_lt]
  -- Prove the mod doesn't truncate:
  -- since `c.tape c.head = false`, the LSB contribution to
  -- `counterValue c start k` is 0, so the old value is bounded by
  -- `2^k - 2`, hence `old + 1 < 2^k`.
  have h_old_lt_pow : counterValue c (c.head : ℕ) k + 1 < 2 ^ k := by
    -- Use counterValue_lt_two_pow, plus the fact that the LSB (k ≥ 1)
    -- contributes 0, so the sum is strictly less than 2^k - 1.
    -- Concretely: counterValue c head k - (LSB_contribution) ≤ 2^k - 2.
    -- But this argument is subtle.  A simpler direct route:
    -- counterValue c head k < 2^k  →  since we can bound it away from
    -- the max by the 0-LSB observation.
    --
    -- For a clean proof we use: for k ≥ 1, at position `head + 0` the
    -- bit is `false`, contributing 0 to the sum.  All other terms
    -- together give ≤ `∑_{i=1}^{k-1} 2^i = 2^k - 2`.
    --
    -- We defer that tighter bound: instead, observe that
    -- counterValue c head k has bit-0 contribution 0, so it is even
    -- (or we note `counterValue (new) < 2^k` and conclude mod =
    -- counterValue (new)).
    have h_new_lt := counterValue_lt_two_pow
      (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
      (c.head : ℕ) k
    rw [h_counter_new] at h_new_lt
    exact h_new_lt
  rw [h_counter_new, Nat.mod_eq_of_lt h_old_lt_pow]

/-!
### Session 7g-e: Full `incrementProgram_correct`

Combines the overflow case (`incrementProgram_correct_all_ones`)
and the first-zero case (`incrementProgram_correct_first_zero_at`)
via classical case analysis.  When the counter is NOT all 1s,
`Nat.find` extracts the smallest position `j < k` with a 0 bit,
and the first-zero lemma discharges the arithmetic.

This theorem is the milestone closing Session 7 fully: for any
`k`, any starting configuration with phase 0 and valid tape
bounds, `incrementProgram k` run for `k + 1` steps increments
the counter modulo `2^k`.
-/

theorem incrementProgram_correct {k : Nat} {n : Nat}
    (c : Configuration (M := (incrementProgram k).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_bound : (c.head : ℕ) + k + 1 ≤
        (incrementProgram k).toTM.tapeLength n) :
    counterValue
        (TM.runConfig (M := (incrementProgram k).toTM) c (k + 1))
        (c.head : ℕ) k =
      (counterValue c (c.head : ℕ) k + 1) % 2 ^ k := by
  classical
  by_cases hall : ∀ (i : Nat), i < k →
      ∀ (hb : (c.head : ℕ) + i < (incrementProgram k).toTM.tapeLength n),
      c.tape ⟨(c.head : ℕ) + i, hb⟩ = true
  · exact incrementProgram_correct_all_ones c h_phase h_bound hall
  · -- Not all ones → there exists a zero.  Find the smallest.
    push_neg at hall
    obtain ⟨i₀, hi₀lt, hb_i₀, hne₀⟩ := hall
    have h_bit_false₀ : c.tape ⟨(c.head : ℕ) + i₀, hb_i₀⟩ = false :=
      Bool.not_eq_true _ |>.mp hne₀
    -- Classical Nat.find
    let P : Nat → Prop := fun i =>
      i < k ∧ ∃ hb : (c.head : ℕ) + i <
          (incrementProgram k).toTM.tapeLength n,
        c.tape ⟨(c.head : ℕ) + i, hb⟩ = false
    have hP : ∃ i, P i := ⟨i₀, hi₀lt, hb_i₀, h_bit_false₀⟩
    let j := Nat.find hP
    have hj_spec : P j := Nat.find_spec hP
    have hj_min : ∀ m, m < j → ¬ P m := fun m hm => Nat.find_min hP hm
    obtain ⟨hjk, hj_bnd, hj_false⟩ := hj_spec
    -- All bits before `j` are 1.
    have h_ones : ∀ i, i < j →
        ∀ (hbi : (c.head : ℕ) + i <
            (incrementProgram k).toTM.tapeLength n),
        c.tape ⟨(c.head : ℕ) + i, hbi⟩ = true := by
      intro i hij hbi
      have hik : i < k := by omega
      have not_P := hj_min i hij
      by_contra h_not_true
      apply not_P
      refine ⟨hik, hbi, ?_⟩
      cases hv : c.tape ⟨(c.head : ℕ) + i, hbi⟩
      case true => exact absurd hv h_not_true
      case false => rfl
    -- Bit at position `j` is 0 for any bounds proof (Fin proof
    -- irrelevance).
    have h_zero_at_j : ∀ (hb : (c.head : ℕ) + j <
        (incrementProgram k).toTM.tapeLength n),
        c.tape ⟨(c.head : ℕ) + j, hb⟩ = false := by
      intro hb
      have : (⟨(c.head : ℕ) + j, hb⟩ : Fin _) =
          ⟨(c.head : ℕ) + j, hj_bnd⟩ := Fin.ext rfl
      rw [this]; exact hj_false
    exact incrementProgram_correct_first_zero_at c h_phase h_bound
      j hjk h_ones h_zero_at_j

end BinaryCounter

/-!
## Second-order pilot: read the first input bit

`readFirstBit` is a one-step `PhasedProgram` whose local state is
`Bool`.  It starts in state `false`, reads the bit under the head (the
first input bit, since the initial head is at position `0`), and
transitions to the state equal to that bit.  Acceptance is assigned to
state `true`.

Correctness (`readFirstBit_accepts`) shows:

* for `n ≥ 1`, the compiled TM accepts on `x` iff `x ⟨0, _⟩ = true`,
* for `n = 0`, it rejects (the head reads a blank `false`).

This pilot is the smallest non-trivial demonstration that the
`PhasedProgram` pipeline scales to runtimes beyond `0`.  Its proof
relies solely on the `runConfig_*` lemmas and the `@[simp]`
`initialConfig` lemmas from `TuringEncoding.lean`; no new axioms or
proof holes are introduced.
-/

namespace Pilot

/-- One-step program that copies the first input bit into the control
state and accepts iff that bit is `true`. -/
def readFirstBit : PhasedProgram.{0} where
  numPhases := 1
  phaseState := fun _ => Bool
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := false
  acceptPhase := 0
  acceptState := true
  transition := fun _ _ b => (⟨0, b⟩, b, Move.stay)
  timeBound := fun _ => 1

/-- On `n ≥ 1`, `readFirstBit` accepts iff the first input bit is `true`. -/
theorem readFirstBit_accepts_pos (n : Nat) (hn : 0 < n) (x : Boolcube.Point n) :
    TM.accepts (M := readFirstBit.toTM) n x = x ⟨0, hn⟩ := by
  unfold TM.accepts TM.run
  rw [show readFirstBit.toTM.runTime n = 1 from rfl, runConfig_one]
  simp [TM.stepConfig, readFirstBit, PhasedProgram.toTM, TM.initialConfig, hn]

/-- On `n = 0` the machine has no input bit to read; the head cell is
blank (`false`), so the step moves to state `⟨0, false⟩` and rejects. -/
theorem readFirstBit_accepts_zero (x : Boolcube.Point 0) :
    TM.accepts (M := readFirstBit.toTM) 0 x = false := by
  unfold TM.accepts TM.run
  rw [show readFirstBit.toTM.runTime 0 = 1 from rfl, runConfig_one]
  simp [TM.stepConfig, readFirstBit, PhasedProgram.toTM, TM.initialConfig]

end Pilot

/-!
## Session 8: Bit-level encoding primitives

The MCSP verifier feeds circuit descriptions to its TM phases via
the witness tape.  Before tackling full circuit encoding, we fix a
general-purpose bit-level primitive: `Fin (2^w)` ↔ `List Bool` of
length `w`, in little-endian order (LSB first).

This primitive is independent of any MCSP-specific content and is
reusable for encoding gate indices, input positions, and any other
bounded-range index that the verifier needs to read off the tape.
-/


end TM

end PsubsetPpoly
end Internal
end Pnp3
