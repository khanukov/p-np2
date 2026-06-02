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

end ContractExpansion
end Frontier
end Pnp4
