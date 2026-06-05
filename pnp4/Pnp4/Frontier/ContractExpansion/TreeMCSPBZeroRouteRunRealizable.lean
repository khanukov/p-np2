import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRouteRunCompose

/-!
# Realizability of the `bZeroRouteProgram` run-through decision (NP-verifier track — D2t-3 routing)

`TreeMCSPBZeroRouteRunCompose.lean` proves the composed run-through *routing-agnostically* (the
`spread + double marker` layout enters as hypotheses).  This module exhibits **concrete inputs** that
satisfy those hypotheses, so the end-to-end decision is **non-vacuously instantiable** (the analogue of
`bZeroRoute_*_realizable` for the full run-through):

* `bZeroRouteProgram_decide_true_realizable` — the input with the double marker at cells `w`, `w + 1`
  (all else `0`) drives `bZeroRouteProgram` to composed phase `4` after `w + 4` steps (`B = 0` → sink);
* `bZeroRouteProgram_decide_false_realizable` — the input with a single set bit at `j` (all else `0`, so
  cell `j + 1` is its own `0` separator) drives it to composed phase `5` after `j + 4` steps
  (`B > 0` → body-entry).

These are existence witnesses (validation), not the converter's real layout.  They confirm the run-through
decision proved in `decide_true`/`decide_false` is realizable from `initialConfig`.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The composed `B = 0` decision is realizable: a concrete double-marker input reaches phase `4`. -/
theorem bZeroRouteProgram_decide_true_realizable {L : Nat} (w : Nat) (hwL : w + 1 < L)
    (hwt : w + 1 < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
          (w + 1 + 1 + 1 + 1)).state).fst : Nat) = 4 := by
  refine ⟨fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1), ?_⟩
  apply bZeroRouteProgram_runConfig_decide_true _ w hwt
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega

/-- The composed `B > 0` decision is realizable: a concrete single-set-bit input reaches phase `5`. -/
theorem bZeroRouteProgram_decide_false_realizable {L : Nat} (j : Nat) (hjL : j + 1 < L)
    (hjt : j + 1 < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
          (j + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  refine ⟨fun q => decide ((q : Nat) = j), ?_⟩
  apply bZeroRouteProgram_runConfig_decide_false _ j hjt
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega

end ContractExpansion
end Frontier
end Pnp4
