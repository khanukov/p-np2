import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-!
# Lifting the self-loop counter into a composition (NP-verifier track, assembly milestone)

The verifier `M` is assembled as a `seqList` of phase programs, so a proven self-loop primitive only
helps if its behaviour survives composition.  Per `TM_VERIFIER_STRATEGY.md` §6's cross-type caveat,
`(seq P1 P2).toTM` and `P1.toTM` have *different* `runTime`/`tapeLength`/`Configuration` types, so the
standalone `selfLoopIncrement_*` lemmas do **not** transfer for free — each composition must re-derive
the phase's intrinsic run behaviour on the composed machine, consuming the toolkit's single-step
`seq_stepConfig_P1_normal_*` lemmas (the tag-check program is the worked template).

This module does exactly that for the **increment as the first component** of a composition
`seq selfLoopIncrement P2` (generic `P2`).  It re-establishes, on the composed machine:

* the single-step carry/stop lemmas (phase `0` is P1-*normal*, since `selfLoopIncrement`'s accept phase
  is `1 ≠ 0`), and
* the carry-ripple run invariant — the structural backbone showing the counter's increment runs
  identically once embedded as `seq`'s first phase.

This builds no verifier and proves no separation; it is the composition-survival evidence for one
proven primitive, and the reusable template for the remaining phases.  All surfaces carry only the
standard `[propext, Classical.choice, Quot.sound]` execution triple.
-/

/-! ### Single-step carry lemmas on `seq selfLoopIncrement P2`

Phase `0` of `selfLoopIncrement` is a normal (non-accept) P1 phase inside `seq`, so one step there is
governed by `seq_stepConfig_P1_normal_*` applied to `selfLoopIncrement`'s transition. -/

/-- Carry step inside the composition (phase `0`, bit `1`): the phase stays `0` (the self-loop
re-entry survives composition). -/
theorem selfLoopIncrement_seq_stepConfig_carry_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).state).fst.val = 0 := by
  rw [seq_stepConfig_P1_normal_phase selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit]

/-- Carry step inside the composition (phase `0`, bit `1`): the head advances right. -/
theorem selfLoopIncrement_seq_stepConfig_carry_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  rw [seq_stepConfig_P1_normal_head selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit]

/-- Carry step inside the composition (phase `0`, bit `1`): the read `1` is flipped to `0`. -/
theorem selfLoopIncrement_seq_stepConfig_carry_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).tape
      = c.write c.head false := by
  rw [seq_stepConfig_P1_normal_tape selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit]

/-! ### Single-step stop lemmas on `seq selfLoopIncrement P2`

The terminating step (phase `0`, bit `0`) still follows P1's transition (phase `0` is normal); it
moves the phase to `selfLoopIncrement`'s accept phase `1` — at which the *next* step would be `seq`'s
P1→P2 handoff. -/

/-- Stop step inside the composition (phase `0`, bit `0`): the phase becomes `1` (P1's accept phase). -/
theorem selfLoopIncrement_seq_stepConfig_stop_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit]

/-- Stop step inside the composition (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopIncrement_seq_stepConfig_stop_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_normal_head selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit, Configuration.moveHead]

/-- Stop step inside the composition (phase `0`, bit `0`): the read `0` is flipped to `1`. -/
theorem selfLoopIncrement_seq_stepConfig_stop_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).tape
      = c.write c.head true := by
  rw [seq_stepConfig_P1_normal_tape selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopIncrement, hi, hbit]

/-! ### Carry-ripple run invariant on the composed machine

The structural payoff: the increment's carry-ripple — proven standalone as
`selfLoopIncrement_runConfig_carry` — re-establishes verbatim on the composed machine
`seq selfLoopIncrement P2`, using the composition single-step lemmas above.  This certifies that the
counter's increment runs identically when embedded as `seq`'s first phase (its accept phase `1`, where
the P1→P2 handoff fires, is only reached *after* the ripple completes), so composing a counter before
any continuation `P2` does not disturb the increment.  Same induction as the standalone; only the
single-step lemmas and the (now `P2`-dependent) `tapeLength` arithmetic differ. -/
theorem selfLoopIncrement_seq_runConfig_carry (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p = true) →
      (((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
          ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
          ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
            ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then false
                else ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p) := by
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
      set c := TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
        ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < (seq selfLoopIncrement P2).toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + (L + P2.timeBound L + 1) + 1; omega
      have hbit : c.tape c.head = true := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h1 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopIncrement_seq_stepConfig_carry_phase P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopIncrement_seq_stepConfig_carry_head P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopIncrement_seq_stepConfig_carry_tape P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

/-- After-increment configuration on the composed machine: if the first `j` counter cells are `1` and
cell `j` is `0` (`j ≤ L`), then after `j + 1` steps of `seq selfLoopIncrement P2` the increment is done
— phase `1` (`selfLoopIncrement`'s accept phase, where the next step would hand off to `P2`), head on
cell `j`, cells `[0, j)` cleared, cell `j` set, the rest unchanged.  Mirrors the standalone
`selfLoopIncrement_runConfig_stop` with the composition single-steps. -/
theorem selfLoopIncrement_seq_runConfig_stop (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_ones : ∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
      (p : Nat) < j → ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < (seq selfLoopIncrement P2).toPhased.toTM.tapeLength L,
      ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    (((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
        ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
          ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
            ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) < j then false
                else if (p : Nat) = j then true
                else ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopIncrement_seq_runConfig_carry P2 x j hj h_ones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
    ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = false := by
    rw [htp, if_neg (show ¬ (c.head : Nat) < j by rw [hhd]; omega), hhead_eq]
    exact h_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopIncrement_seq_stepConfig_stop_phase P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopIncrement_seq_stepConfig_stop_head P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopIncrement_seq_stepConfig_stop_tape P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      simp [hhd]
    · rw [Configuration.write_other c hp true, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      split_ifs <;> rfl

/-- Semantic correctness of the increment **inside the composition**: on the composed machine
`seq selfLoopIncrement P2`, if the counter window `[0, k)` has first-zero at `j` (`j < k ≤ L`), then
after `j + 1` steps — the point at which the increment completes and `seq` is poised to hand off to
`P2` — the little-endian counter value has increased by exactly one.  Plugs the composed after-stop
tape characterization into the toolkit's generic `counterValue_first_zero_diff`.  This is the headline
composition-survival fact: a proven counter step retains its semantics as `seq`'s first phase. -/
theorem selfLoopIncrement_seq_runConfig_counterValue (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (j k : Nat) (hjk : j < k) (hk : k ≤ L)
    (h_ones : ∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
      (p : Nat) < j → ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < (seq selfLoopIncrement P2).toPhased.toTM.tapeLength L,
      ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    counterValue (TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
        ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1)) 0 k
      = counterValue ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) 0 k + 1 := by
  obtain ⟨_, _, htp⟩ := selfLoopIncrement_seq_runConfig_stop P2 x j (by omega) h_ones h_zero
  refine counterValue_first_zero_diff
    ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x)
    (TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
      ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1)) 0 j k hjk
    (by show (0 : Nat) + k ≤ L + (L + P2.timeBound L + 1) + 1; omega) ?_ ?_ ?_ ?_ ?_
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

/-! ### The P1→P2 handoff after the increment

Once the increment reaches its accept phase `1`, the *next* step of `seq selfLoopIncrement P2` is the
distinguished handoff: the phase jumps to `P2`'s (shifted) start phase, while the tape and head are
preserved (the handoff writes back the scanned bit and stays).  These lemmas specialize the toolkit's
`seq_stepConfig_P1_accept_*` to `selfLoopIncrement` at phase `1`, then chain them into the run-level
"increment, then hand off to `P2`" fact — the glue that lets the next phase begin with the counter
already incremented. -/

/-- Handoff step (phase `1`): the phase jumps to `P2`'s shifted start. -/
theorem selfLoopIncrement_seq_stepConfig_handoff_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).state).fst.val
      = 2 + P2.startPhase.val := by
  rw [seq_stepConfig_P1_accept_phase selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate,
    selfLoopIncrement_numPhases]

/-- Handoff step (phase `1`): the head is unchanged. -/
theorem selfLoopIncrement_seq_stepConfig_handoff_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_accept_head selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]

/-- Handoff step (phase `1`): the tape is unchanged. -/
theorem selfLoopIncrement_seq_stepConfig_handoff_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopIncrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopIncrement P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c).tape = c.tape := by
  rw [seq_stepConfig_P1_accept_tape selfLoopIncrement P2 c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]

/-- Increment-then-handoff on the composed machine: after `j + 2` steps of `seq selfLoopIncrement P2`
(`j + 1` for the increment, one for the handoff), control sits at `P2`'s shifted start phase, the head
is back on cell `j`, and the counter value over the window `[0, k)` has increased by exactly one
(preserved across the tape-stable handoff).  This is the complete "first phase done, next phase begins
with the counter incremented" composition unit. -/
theorem selfLoopIncrement_seq_runConfig_handoff (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (j k : Nat) (hjk : j < k) (hk : k ≤ L)
    (h_ones : ∀ p : Fin ((seq selfLoopIncrement P2).toPhased.toTM.tapeLength L),
      (p : Nat) < j → ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < (seq selfLoopIncrement P2).toPhased.toTM.tapeLength L,
      ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    (((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
        ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 2)).state).fst : Nat)
        = 2 + P2.startPhase.val
      ∧ ((TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
          ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 2)).head : Nat) = j
      ∧ counterValue (TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
          ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 2)) 0 k
        = counterValue ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) 0 k + 1 := by
  obtain ⟨hph1, hhd1, _⟩ := selfLoopIncrement_seq_runConfig_stop P2 x j (by omega) h_ones h_zero
  have hcv1 := selfLoopIncrement_seq_runConfig_counterValue P2 x j k hjk hk h_ones h_zero
  have hsucc : j + 2 = (j + 1) + 1 := by omega
  rw [hsucc, TM.runConfig_succ]
  set c1 := TM.runConfig (M := (seq selfLoopIncrement P2).toPhased.toTM)
    ((seq selfLoopIncrement P2).toPhased.toTM.initialConfig x) (j + 1) with hc1
  have htape : (TM.stepConfig (M := (seq selfLoopIncrement P2).toPhased.toTM) c1).tape = c1.tape :=
    selfLoopIncrement_seq_stepConfig_handoff_tape P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopIncrement_seq_stepConfig_handoff_phase P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl
  · rw [selfLoopIncrement_seq_stepConfig_handoff_head P2 c1
      (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact hhd1
  · rw [counterValue_eq_of_tape_eq _ c1 0 k (fun p _ _ => congrFun htape p)]
    exact hcv1

/-! ## Lifting the self-loop decrement into a composition

The down-counter (`selfLoopDecrement`) is the loop-*termination* primitive (countdown to zero), so its
composition-survival matters most for the eventual bounded loop.  Same template as the increment, with
the borrow/stop roles and the dual `counterValue` arithmetic (`counterValue_first_one_diff`). -/

/-- Borrow step inside the composition (phase `0`, bit `0`): the phase stays `0`. -/
theorem selfLoopDecrement_seq_stepConfig_borrow_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).state).fst.val = 0 := by
  rw [seq_stepConfig_P1_normal_phase selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit]

/-- Borrow step inside the composition (phase `0`, bit `0`): the head advances right. -/
theorem selfLoopDecrement_seq_stepConfig_borrow_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  rw [seq_stepConfig_P1_normal_head selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit]

/-- Borrow step inside the composition (phase `0`, bit `0`): the read `0` is flipped to `1`. -/
theorem selfLoopDecrement_seq_stepConfig_borrow_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).tape
      = c.write c.head true := by
  rw [seq_stepConfig_P1_normal_tape selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit]

/-- Stop step inside the composition (phase `0`, bit `1`): the phase becomes `1`. -/
theorem selfLoopDecrement_seq_stepConfig_stop_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit]

/-- Stop step inside the composition (phase `0`, bit `1`): the head stays put. -/
theorem selfLoopDecrement_seq_stepConfig_stop_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).head = c.head := by
  rw [seq_stepConfig_P1_normal_head selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit, Configuration.moveHead]

/-- Stop step inside the composition (phase `0`, bit `1`): the read `1` is flipped to `0`. -/
theorem selfLoopDecrement_seq_stepConfig_stop_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq selfLoopDecrement P2).toPhased.toTM) L)
    {i : Fin (seq selfLoopDecrement P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq selfLoopDecrement P2).toPhased.toTM) c).tape
      = c.write c.head false := by
  rw [seq_stepConfig_P1_normal_tape selfLoopDecrement P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [selfLoopDecrement, hi, hbit]

/-- Borrow-ripple invariant on the composed machine: if the first `k` counter cells are `0`, then
after `k ≤ L` steps of `seq selfLoopDecrement P2` the machine is in phase `0`, head at `k`, cells
`[0, k)` flipped to `1`.  Mirrors `selfLoopDecrement_runConfig_borrow`. -/
theorem selfLoopDecrement_seq_runConfig_borrow (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin ((seq selfLoopDecrement P2).toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape p = false) →
      (((TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
          ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
          ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin ((seq selfLoopDecrement P2).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
            ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then true
                else ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape p) := by
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
      set c := TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
        ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < (seq selfLoopDecrement P2).toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + (L + P2.timeBound L + 1) + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h0 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopDecrement_seq_stepConfig_borrow_phase P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopDecrement_seq_stepConfig_borrow_head P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopDecrement_seq_stepConfig_borrow_tape P2 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp true, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

/-- After-decrement configuration on the composed machine.  Mirrors
`selfLoopDecrement_runConfig_stop`. -/
theorem selfLoopDecrement_seq_runConfig_stop (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_zeros : ∀ p : Fin ((seq selfLoopDecrement P2).toPhased.toTM.tapeLength L),
      (p : Nat) < j → ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape p = false)
    (h_one : ∀ hb : j < (seq selfLoopDecrement P2).toPhased.toTM.tapeLength L,
      ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = true) :
    (((TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
        ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
          ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin ((seq selfLoopDecrement P2).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
            ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) < j then true
                else if (p : Nat) = j then false
                else ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopDecrement_seq_runConfig_borrow P2 x j hj h_zeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
    ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = true := by
    rw [htp, if_neg (show ¬ (c.head : Nat) < j by rw [hhd]; omega), hhead_eq]
    exact h_one _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopDecrement_seq_stepConfig_stop_phase P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopDecrement_seq_stepConfig_stop_head P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopDecrement_seq_stepConfig_stop_tape P2 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      simp [hhd]
    · rw [Configuration.write_other c hp false, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      split_ifs <;> rfl

/-- Decrement `counterValue − 1` survives composition: on `seq selfLoopDecrement P2`, if the window
`[0, k)` has first-one at `j` (`j < k ≤ L`, positive value), then after `j + 1` steps the value has
decreased by exactly one (`before = after + 1`).  Plugs the composed after-stop tape characterization
into the dual bit-flip arithmetic `counterValue_first_one_diff`. -/
theorem selfLoopDecrement_seq_runConfig_counterValue (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (j k : Nat) (hjk : j < k) (hk : k ≤ L)
    (h_zeros : ∀ p : Fin ((seq selfLoopDecrement P2).toPhased.toTM.tapeLength L),
      (p : Nat) < j → ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape p = false)
    (h_one : ∀ hb : j < (seq selfLoopDecrement P2).toPhased.toTM.tapeLength L,
      ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = true) :
    counterValue ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) 0 k
      = counterValue (TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
          ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) (j + 1)) 0 k + 1 := by
  obtain ⟨_, _, htp⟩ := selfLoopDecrement_seq_runConfig_stop P2 x j (by omega) h_zeros h_one
  refine counterValue_first_one_diff
    ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x)
    (TM.runConfig (M := (seq selfLoopDecrement P2).toPhased.toTM)
      ((seq selfLoopDecrement P2).toPhased.toTM.initialConfig x) (j + 1)) 0 j k hjk
    (by show (0 : Nat) + k ≤ L + (L + P2.timeBound L + 1) + 1; omega) ?_ ?_ ?_ ?_ ?_
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

/-! ## Lifting the increment into the P2 region (a non-first phase)

In `seqList [p₁, p₂, …] = seq p₁ (seq p₂ …)` every phase but the first runs in a **P2-region** (control
phase `≥ P1.numPhases`).  These lemmas re-derive the increment's carry/stop steps when it is the second
component `seq P1 selfLoopIncrement` (generic `P1`), via the toolkit's `seq_stepConfig_P2_*` (phase
shifted up by `P1.numPhases`).  Together with the P1-region lemmas above, the increment is now
single-step characterized in *either* `seq` position — the backbone for composing a counter as a
non-first phase of the assembled `M`. -/

/-- Carry step as a non-first phase (composition phase `P1.numPhases`, bit `1`): the phase stays at
`P1.numPhases` (the self-loop re-entry, shifted into P2's block). -/
theorem selfLoopIncrement_seqP2_stepConfig_carry_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit]

/-- Carry step as a non-first phase (bit `1`): the head advances right. -/
theorem selfLoopIncrement_seqP2_stepConfig_carry_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit]

/-- Carry step as a non-first phase (bit `1`): the read `1` is flipped to `0`. -/
theorem selfLoopIncrement_seqP2_stepConfig_carry_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).tape
      = c.write c.head false := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit]

/-- Stop step as a non-first phase (bit `0`): the phase becomes `P1.numPhases + 1` (the increment's
accept phase, shifted — which for `seq P1 selfLoopIncrement` is the composition's own accept phase). -/
theorem selfLoopIncrement_seqP2_stepConfig_stop_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit]

/-- Stop step as a non-first phase (bit `0`): the head stays put. -/
theorem selfLoopIncrement_seqP2_stepConfig_stop_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit, Configuration.moveHead]

/-- Stop step as a non-first phase (bit `0`): the read `0` is flipped to `1`. -/
theorem selfLoopIncrement_seqP2_stepConfig_stop_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopIncrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c).tape
      = c.write c.head true := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopIncrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopIncrement, hsub, hbit]

/-- Carry-ripple as a non-first phase, **from an arbitrary start configuration**.  When the increment
runs as `P2` it begins not at `initialConfig` but wherever the preceding phase(s) left control — at
composition phase `P1.numPhases`, with the head at some `c0.head`.  So the invariant is stated from a
generic `c0`: if `c0` is at phase `P1.numPhases` and the counter window `[c0.head, c0.head + k)` is all
`1`, then after `k` steps the phase still rests at `P1.numPhases`, the head has advanced to
`c0.head + k`, and exactly those `k` cells have been cleared to `0`.  This is the offset-aware,
non-first-phase analogue of `selfLoopIncrement_seq_runConfig_carry`, and the form needed to chain a
counter after an earlier phase. -/
theorem selfLoopIncrement_seqP2_runConfig_carry (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k ≤ L →
      (∀ p : Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ ∀ p : Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 k).tape p
            = (if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + k
                then false else c0.tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨hphase, by simp, ?_⟩
      intro p
      have hfalse : ¬ ((c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 0) := by omega
      show c0.tape p
          = if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 0 then false else c0.tape p
      rw [if_neg hfalse]
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 k with hc
      have hbnd : (c.head : Nat) + 1 < (seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L := by
        rw [hhd]; show (c0.head : Nat) + k + 1 < L + (P1.timeBound L + L + 1) + 1; omega
      have hbit : c.tape c.head = true := by
        rw [htp]
        rw [if_neg (by rw [hhd]; omega)]
        exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopIncrement_seqP2_stepConfig_carry_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopIncrement_seqP2_stepConfig_carry_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopIncrement_seqP2_stepConfig_carry_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (by constructor <;> (rw [hhd]; omega))]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ (c0.head : Nat) + k := by
            intro h; exact hp (Fin.ext (by rw [hhd]; exact h))
          by_cases hin : (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + k
          · rw [if_pos hin, if_pos ⟨hin.1, by omega⟩]
          · rw [if_neg hin, if_neg (by
              intro hcon; exact hin ⟨hcon.1, by omega⟩)]

/-- After-increment configuration as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`, head `c0.head`): if the window `[c0.head, c0.head + j)` is all `1` and cell
`c0.head + j` is `0`, then after `j + 1` steps the phase is `P1.numPhases + 1` (the shifted accept
phase), head `c0.head + j`, cells `[c0.head, c0.head + j)` cleared and cell `c0.head + j` set.
Offset/non-first-phase analogue of `selfLoopIncrement_seq_runConfig_stop`. -/
theorem selfLoopIncrement_seqP2_runConfig_stop (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (j : Nat) (hj : (c0.head : Nat) + j ≤ L)
    (h_ones : ∀ p : Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true)
    (h_zero : ∀ hb : (c0.head : Nat) + j < (seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + j, hb⟩ = false) :
    (((TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 (j + 1)).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 (j + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ ∀ p : Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 (j + 1)).tape p
            = (if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + j then false
                else if (p : Nat) = (c0.head : Nat) + j then true
                else c0.tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopIncrement_seqP2_runConfig_carry P1 c0 hphase j hj h_ones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 j with hc
  have hhead_eq : c.head = ⟨(c0.head : Nat) + j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = false := by
    rw [htp, if_neg (by rw [hhd]; omega), hhead_eq]
    exact h_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopIncrement_seqP2_stepConfig_stop_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopIncrement_seqP2_stepConfig_stop_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopIncrement_seqP2_stepConfig_stop_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      have h1 : ¬ ((c0.head : Nat) ≤ (c.head : Nat) ∧ (c.head : Nat) < (c0.head : Nat) + j) := by
        rw [hhd]; omega
      rw [if_neg h1, if_pos (by rw [hhd])]
    · rw [Configuration.write_other c hp true, htp p]
      have hpc : (p : Nat) ≠ (c0.head : Nat) + j := by
        intro h; exact hp (Fin.ext (by rw [hhd]; exact h))
      by_cases hin : (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + j
      · rw [if_pos hin, if_pos hin]
      · rw [if_neg hin, if_neg hin, if_neg hpc]

/-- Increment `counterValue + 1` survives composition **as a non-first phase**: on
`seq P1 selfLoopIncrement` from an arbitrary start `c0` (phase `P1.numPhases`), if the window
`[c0.head, c0.head + k)` has first-zero at offset `j` (`j < k`, `c0.head + k ≤ L`), then after `j + 1`
steps the little-endian value over that window has increased by exactly one.  Offset analogue of
`selfLoopIncrement_seq_runConfig_counterValue`, via the toolkit's `counterValue_first_zero_diff` at
`start := c0.head`. -/
theorem selfLoopIncrement_seqP2_runConfig_counterValue (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopIncrement).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (j k : Nat) (hjk : j < k)
    (hk : (c0.head : Nat) + k ≤ L)
    (h_ones : ∀ p : Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true)
    (h_zero : ∀ hb : (c0.head : Nat) + j < (seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + j, hb⟩ = false) :
    counterValue (TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 (j + 1))
        (c0.head : Nat) k
      = counterValue c0 (c0.head : Nat) k + 1 := by
  obtain ⟨_, _, htp⟩ := selfLoopIncrement_seqP2_runConfig_stop P1 c0 hphase j (by omega) h_ones h_zero
  refine counterValue_first_zero_diff c0
    (TM.runConfig (M := (seq P1 selfLoopIncrement).toPhased.toTM) c0 (j + 1))
    (c0.head : Nat) j k hjk (by
      show (c0.head : Nat) + k ≤ L + (P1.timeBound L + L + 1) + 1; omega) ?_ ?_ ?_ ?_ ?_
  · intro i hij hb
    exact h_ones ⟨(c0.head : Nat) + i, hb⟩ (Nat.le_add_right _ _) (Nat.add_lt_add_left hij _)
  · intro hb
    exact h_zero hb
  · intro i hij hb
    have hv : ((⟨(c0.head : Nat) + i, hb⟩ :
        Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L)) : Nat) = (c0.head : Nat) + i :=
      rfl
    rw [htp ⟨(c0.head : Nat) + i, hb⟩, hv, if_pos (by omega)]
  · intro hb
    have hv : ((⟨(c0.head : Nat) + j, hb⟩ :
        Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L)) : Nat) = (c0.head : Nat) + j :=
      rfl
    rw [htp ⟨(c0.head : Nat) + j, hb⟩, hv, if_neg (by omega), if_pos rfl]
  · intro i hji hik hb
    have hv : ((⟨(c0.head : Nat) + i, hb⟩ :
        Fin ((seq P1 selfLoopIncrement).toPhased.toTM.tapeLength L)) : Nat) = (c0.head : Nat) + i :=
      rfl
    rw [htp ⟨(c0.head : Nat) + i, hb⟩, hv, if_neg (by omega), if_neg (by omega)]

/-! ## Lifting the decrement into the P2 region (a non-first phase)

Mirrors the increment's P2-region lift for the down-counter `selfLoopDecrement` (borrow/stop roles
swapped).  Completes the self-loop counter family's coverage: both directions now compose in *either*
`seq` position. -/

/-- Borrow step as a non-first phase (composition phase `P1.numPhases`, bit `0`): the phase stays. -/
theorem selfLoopDecrement_seqP2_stepConfig_borrow_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit]

/-- Borrow step as a non-first phase (bit `0`): the head advances right. -/
theorem selfLoopDecrement_seqP2_stepConfig_borrow_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit]

/-- Borrow step as a non-first phase (bit `0`): the read `0` is flipped to `1`. -/
theorem selfLoopDecrement_seqP2_stepConfig_borrow_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).tape
      = c.write c.head true := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit]

/-- Stop step as a non-first phase (bit `1`): the phase becomes `P1.numPhases + 1`. -/
theorem selfLoopDecrement_seqP2_stepConfig_stop_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit]

/-- Stop step as a non-first phase (bit `1`): the head stays put. -/
theorem selfLoopDecrement_seqP2_stepConfig_stop_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit, Configuration.moveHead]

/-- Stop step as a non-first phase (bit `1`): the read `1` is flipped to `0`. -/
theorem selfLoopDecrement_seqP2_stepConfig_stop_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopDecrement).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c).tape
      = c.write c.head false := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopDecrement c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopDecrement, hsub, hbit]

/-- Borrow-ripple as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`): if the
window `[c0.head, c0.head + k)` is all `0`, then after `k` steps the phase still rests at
`P1.numPhases`, the head has advanced to `c0.head + k`, and exactly those `k` cells have been set to
`1`.  Offset/non-first-phase analogue of `selfLoopDecrement_seq_runConfig_borrow`. -/
theorem selfLoopDecrement_seqP2_runConfig_borrow (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopDecrement).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k ≤ L →
      (∀ p : Fin ((seq P1 selfLoopDecrement).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ ∀ p : Fin ((seq P1 selfLoopDecrement).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c0 k).tape p
            = (if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + k
                then true else c0.tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨hphase, by simp, ?_⟩
      intro p
      have hfalse : ¬ ((c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 0) := by omega
      show c0.tape p
          = if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 0 then true else c0.tape p
      rw [if_neg hfalse]
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopDecrement).toPhased.toTM) c0 k with hc
      have hbnd : (c.head : Nat) + 1 < (seq P1 selfLoopDecrement).toPhased.toTM.tapeLength L := by
        rw [hhd]; show (c0.head : Nat) + k + 1 < L + (P1.timeBound L + L + 1) + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]
        rw [if_neg (by rw [hhd]; omega)]
        exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopDecrement_seqP2_stepConfig_borrow_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopDecrement_seqP2_stepConfig_borrow_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopDecrement_seqP2_stepConfig_borrow_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (by constructor <;> (rw [hhd]; omega))]
        · rw [Configuration.write_other c hp true, htp p]
          have hpc : (p : Nat) ≠ (c0.head : Nat) + k := by
            intro h; exact hp (Fin.ext (by rw [hhd]; exact h))
          by_cases hin : (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + k
          · rw [if_pos hin, if_pos ⟨hin.1, by omega⟩]
          · rw [if_neg hin, if_neg (by
              intro hcon; exact hin ⟨hcon.1, by omega⟩)]

end ContractExpansion
end Frontier
end Pnp4
