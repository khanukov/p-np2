import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaFillProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Gamma fill as a non-first (P2-region) phase (NP-verifier track)

The gamma loop-counter materialization (`gammaSelfLoopFill`) runs in `M` *after* the tag check, so it
must work as a `seq` component.  Per the cross-instance caveat, we re-derive its fill behaviour on
`seq P1 gammaSelfLoopFill` (the fill in the P2 region, governed by `seq_stepConfig_P2_*`).  Mirrors the
gamma-scan P2-region lift, but the tape **evolves** (each scanned `0` becomes a `1`), so the run
invariant carries the conditional-tape (fill-window) clause.  All surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple. -/

/-- Fill step as a non-first phase (bit `0`): the phase stays at `P1.numPhases`. -/
theorem gammaSelfLoopFill_seqP2_stepConfig_fill_zero_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopFill).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 gammaSelfLoopFill c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopFill, hsub, hbit]

/-- Fill step as a non-first phase (bit `0`): the head advances right. -/
theorem gammaSelfLoopFill_seqP2_stepConfig_fill_zero_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopFill).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 gammaSelfLoopFill c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopFill, hsub, hbit]

/-- Fill step as a non-first phase (bit `0`): the scanned `0` is overwritten with `1`. -/
theorem gammaSelfLoopFill_seqP2_stepConfig_fill_zero_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) L)
    {i : Fin (seq P1 gammaSelfLoopFill).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c).tape = c.write c.head true := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 gammaSelfLoopFill c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [gammaSelfLoopFill, hsub, hbit]

/-- Fill invariant as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`): if the
window `[c0.head, c0.head + k)` is all `0`, then after `k` steps the phase still rests at `P1.numPhases`,
the head has advanced to `c0.head + k`, and exactly that window has been filled with `1` (rest of tape
unchanged).  Materializes a length-`k` unary counter at the head offset — the offset/non-first analogue
of `gammaSelfLoopFill_runConfig_fill`, for the fill running after the tag check. -/
theorem gammaSelfLoopFill_seqP2_runConfig_fill (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k ≤ L →
      (∀ p : Fin ((seq P1 gammaSelfLoopFill).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ ∀ p : Fin ((seq P1 gammaSelfLoopFill).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c0 k).tape p
            = (if (c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + k
                then true else c0.tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨hphase, by simp, ?_⟩
      intro p
      have h0 : TM.runConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c0 0 = c0 := rfl
      rw [h0, if_neg (show ¬ ((c0.head : Nat) ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 0) by omega)]
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 gammaSelfLoopFill).toPhased.toTM) c0 k with hc
      have hbnd : (c.head : Nat) + 1 < (seq P1 gammaSelfLoopFill).toPhased.toTM.tapeLength L := by
        rw [hhd]; show (c0.head : Nat) + k + 1 < L + (P1.timeBound L + L + 1) + 1; omega
      have hbit : c.tape c.head = false := by
        rw [htp]
        rw [if_neg (show ¬ ((c0.head : Nat) ≤ (c.head : Nat) ∧ (c.head : Nat) < (c0.head : Nat) + k)
          by rw [hhd]; omega)]
        exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact gammaSelfLoopFill_seqP2_stepConfig_fill_zero_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [gammaSelfLoopFill_seqP2_stepConfig_fill_zero_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaSelfLoopFill_seqP2_stepConfig_fill_zero_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self, if_pos (by rw [hhd]; constructor <;> omega)]
        · rw [Configuration.write_other c hp true, htp p]
          have hpc : (p : Nat) ≠ (c.head : Nat) := fun h => hp (Fin.ext h)
          rw [hhd] at hpc
          split_ifs <;> first | rfl | (exfalso; omega)

end ContractExpansion
end Frontier
end Pnp4
