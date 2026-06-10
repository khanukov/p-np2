import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRouteRunCompose

/-!
# Realizability of the `bZeroRouteProgram` run-through decision (NP-verifier track — D2t-3 routing)

`TreeMCSPBZeroRouteRunCompose.lean` proves the composed run-through *routing-agnostically*, from an
**arbitrary start config `c0`** (the `spread + double marker` layout enters as hypotheses relative to
`c0.head`).  This module exhibits **concrete inputs** that satisfy those hypotheses with
`c0 := initialConfig x` (so `c0.head = 0`), so the end-to-end decision is **non-vacuously instantiable**
(the analogue of `bZeroRoute_*_realizable` for the full run-through):

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

/-- `initialConfig` places the head at cell `0`; the run-through decision (stated relative to `c0.head`)
specializes to absolute positions through this. -/
private theorem initialConfig_head_val {L : Nat} (x : Boolcube.Point L) :
    (((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).head : Nat) = 0 := rfl

/-- The composed `B = 0` decision is realizable: a concrete double-marker input reaches phase `4`. -/
theorem bZeroRouteProgram_decide_true_realizable {L : Nat} (w : Nat) (hwL : w + 1 < L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
          (w + 1 + 1 + 1 + 1)).state).fst : Nat) = 4 := by
  refine ⟨fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1), ?_⟩
  apply bZeroRouteProgram_runConfig_decide_true _ rfl w
  · rw [initialConfig_head_val]
    have hLe : L ≤ (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L := by
      simp only [TM.tapeLength]; omega
    omega
  · intro p hp1 hp2
    rw [initialConfig_head_val] at hp2
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    rw [initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    rw [initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega

/-- The composed `B > 0` decision is realizable: a concrete single-set-bit input reaches phase `5`. -/
theorem bZeroRouteProgram_decide_false_realizable {L : Nat} (j : Nat) (hjL : j + 1 < L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
          (j + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  refine ⟨fun q => decide ((q : Nat) = j), ?_⟩
  apply bZeroRouteProgram_runConfig_decide_false _ rfl j
  · rw [initialConfig_head_val]
    have hLe : L ≤ (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L := by
      simp only [TM.tapeLength]; omega
    omega
  · intro p hp1 hp2
    rw [initialConfig_head_val] at hp2
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    rw [initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    rw [initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega

end ContractExpansion
end Frontier
end Pnp4
