import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Gamma loop-counter materialization: fill the leading zeros with ones (NP-verifier track)

§6d's gamma-payload read needs the `z` leading gamma zeros turned into a consumable unary counter (a
block of `1`s) so the `repeatBody` combinator can drive a `z`-iteration read.  `gammaSelfLoopFill` does
exactly that **in place**, rightward: in scan phase `0` reading a `0` it writes a `1` and advances;
reading a `1` (the gamma terminator) it stops.  Run from the tag/gamma boundary (the constant `tagLen`,
where the tag check ends), it fills `[tagLen, p_term)` with `1`s and stops on the terminator — **never
touching the tag below** (it moves right, away from the tag), so it sidesteps the marker-free
left-overrun problem (the tag's trailing `0`) entirely.

It is the consuming/writing dual of `gammaSelfLoopScan` (which reads the same `0`-prefix without
writing): identical 2-phase shape, but the back-edge step writes `1` instead of the scanned `0`, so the
tape *evolves* (as in the increment carry-ripple).  This brick ships the standalone program + its
fill run-invariant; the composition (P2-region) lift mirrors the other self-loops and is the follow-up.
Builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` execution triple. -/

/-- Self-loop that fills a `0`-block with `1`s rightward: phase `0` reading a `0` writes a `1`, advances
right, and re-enters (the back-edge); reading a `1` stops (phase `1`).  Fixed 2-phase, variable-width;
the writing dual of `gammaSelfLoopScan`. -/
def gammaSelfLoopFill : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨1, by omega⟩, (), b, Move.stay)
      else (⟨0, by omega⟩, (), true, Move.right)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem gammaSelfLoopFill_timeBound (n : Nat) : gammaSelfLoopFill.timeBound n = n := rfl

@[simp] theorem gammaSelfLoopFill_numPhases : gammaSelfLoopFill.numPhases = 2 := rfl

@[simp] theorem gammaSelfLoopFill_startPhase_val : (gammaSelfLoopFill.startPhase : Nat) = 0 := rfl

@[simp] theorem gammaSelfLoopFill_acceptPhase_val : (gammaSelfLoopFill.acceptPhase : Nat) = 1 := rfl

/-- The fill never moves its head left: it advances right while filling, otherwise stays. -/
theorem gammaSelfLoopFill_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (gammaSelfLoopFill.transition i s b).2.2.2 ≠ Move.left := by
  unfold gammaSelfLoopFill
  dsimp only
  split_ifs <;> simp

/-- The compiled fill TM never moves its head left. -/
theorem gammaSelfLoopFill_neverMovesLeft : TMNeverMovesLeft (gammaSelfLoopFill.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact gammaSelfLoopFill_transition_move i s b

/-! ### Single-step lemmas (the filling back-edge step) -/

/-- Fill step on a `0`: the phase stays `0` (the self-loop / back-edge). -/
theorem gammaSelfLoopFill_stepConfig_fill_zero_phase {L : Nat}
    (c : Configuration (M := gammaSelfLoopFill.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := gammaSelfLoopFill.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, gammaSelfLoopFill, hi, hbit]

/-- Fill step on a `0`: the head advances right. -/
theorem gammaSelfLoopFill_stepConfig_fill_zero_head {L : Nat}
    (c : Configuration (M := gammaSelfLoopFill.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := gammaSelfLoopFill.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, gammaSelfLoopFill, hi, hbit]

/-- Fill step on a `0`: the scanned `0` is overwritten with `1`. -/
theorem gammaSelfLoopFill_stepConfig_fill_zero_tape {L : Nat}
    (c : Configuration (M := gammaSelfLoopFill.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := gammaSelfLoopFill.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, gammaSelfLoopFill, hi, hbit]

/-- Terminator step on a `1`: jump to the done phase `1`. -/
theorem gammaSelfLoopFill_stepConfig_stop_one_phase {L : Nat}
    (c : Configuration (M := gammaSelfLoopFill.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gammaSelfLoopFill.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, gammaSelfLoopFill, hi, hbit]

/-! ### Fill run-invariant -/

/-- Fill invariant: if the first `k` cells are `0`, then after `k ≤ L` steps from the initial
configuration the machine is still in scan phase `0`, the head has advanced to `k`, and cells `[0, k)`
have been filled with `1` (the rest of the tape unchanged).  This materializes a length-`k` unary
counter in place.  Tracks the *evolving* tape (as the increment carry-ripple does); the dual of
`gammaSelfLoopScan_runConfig_scanning` (which leaves the tape unchanged). -/
theorem gammaSelfLoopFill_runConfig_fill {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin (gammaSelfLoopFill.toPhased.toTM.tapeLength L),
        (p : Nat) < k → (gammaSelfLoopFill.toPhased.toTM.initialConfig x).tape p = false) →
      (((TM.runConfig (M := gammaSelfLoopFill.toPhased.toTM)
          (gammaSelfLoopFill.toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := gammaSelfLoopFill.toPhased.toTM)
          (gammaSelfLoopFill.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin (gammaSelfLoopFill.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := gammaSelfLoopFill.toPhased.toTM)
            (gammaSelfLoopFill.toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then true
                else (gammaSelfLoopFill.toPhased.toTM.initialConfig x).tape p) := by
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
      set c := TM.runConfig (M := gammaSelfLoopFill.toPhased.toTM)
        (gammaSelfLoopFill.toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < gammaSelfLoopFill.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + L + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h0 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopFill_stepConfig_fill_zero_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopFill_stepConfig_fill_zero_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaSelfLoopFill_stepConfig_fill_zero_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp true, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

end ContractExpansion
end Frontier
end Pnp4
