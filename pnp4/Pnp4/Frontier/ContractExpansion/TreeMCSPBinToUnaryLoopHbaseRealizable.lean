import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopHbase

/-!
# Realizability of `binToUnaryLoop`'s base case (`hbase`) (NP-verifier track — D2t-3 `ε`)

`TreeMCSPBinToUnaryLoopHbase.lean` proves the `B = 0 → sink` run-through *layout-agnostically* (the
`zeros + double marker` layout enters as hypotheses relative to `c0.head`).  This module exhibits a
**concrete input** that satisfies those hypotheses with `c0 := initialConfig x` (so `c0.head = 0`), so the
base case is **non-vacuously instantiable** in the loop machine — the analogue of the route's
`bZeroRouteProgram_decide_true_realizable`:

* `binToUnaryLoop_hbase_realizable` — the input with the double marker at cells `z`, `z + 1` (all else
  `0`) drives `binToUnaryLoop` to the sink phase `4` after `z + 4` steps.

This is an existence witness (validation), not the converter's mid-loop layout; it confirms the layout the
`hbase` run-through consumes does fit the loop machine's tape (`tapeLength L = 2·L + 1`) and is reachable
from `initialConfig`.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- `initialConfig` places the loop machine's head at cell `0`; the `hbase` run-through (stated relative
to `c0.head`) specializes to absolute positions through this. -/
private theorem binToUnaryLoop_initialConfig_head_val {L : Nat} (x : Boolcube.Point L) :
    ((binToUnaryLoop.toPhased.toTM.initialConfig x).head : Nat) = 0 := rfl

/-- The loop's `B = 0` base case is realizable: a concrete double-marker input reaches the sink phase
`4`. -/
theorem binToUnaryLoop_hbase_realizable {L : Nat} (z : Nat) (hzL : z + 1 < L) :
    ∃ x : Boolcube.Point L,
      (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM)
          (binToUnaryLoop.toPhased.toTM.initialConfig x) (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 4 := by
  refine ⟨fun j => decide ((j : Nat) = z ∨ (j : Nat) = z + 1), ?_⟩
  apply binToUnaryLoop_runConfig_hbase _ rfl z
  · rw [binToUnaryLoop_initialConfig_head_val]
    simp only [TM.tapeLength]; omega
  · intro p hp1 hp2
    rw [binToUnaryLoop_initialConfig_head_val] at hp2
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  · intro p hp
    rw [binToUnaryLoop_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  · intro p hp
    rw [binToUnaryLoop_initialConfig_head_val] at hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega

end ContractExpansion
end Frontier
end Pnp4
