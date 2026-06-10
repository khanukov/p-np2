import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Two-sided head-displacement bounds (NP-verifier track — bidirectional accounting foundation)

The right-only layer tracks the head with an upper bound (`runConfig_head_val_le`: `head ≤ c.head + j`)
and a lower bound *only under* `TMNeverMovesLeft` (`runConfig_head_val_ge_of_never_left`: head is
monotone, so `head ≥ c.head`).  Bidirectional phases (e.g. `selfLoopScanLeft`) violate `neverMovesLeft`,
so that lower bound no longer applies — yet the head still moves by **at most one cell per step** in
*either* direction.  This module proves the **direction-agnostic** lower bound (`head ≥ c.head − j`)
and packages it with the existing upper bound into the two-sided displacement bound
`|head − c.head| ≤ j`.

This is the kinematic accounting foundation the bidirectional algorithms (counted gamma-payload read,
prefix compare) need to bound how far the head travels — replacing the right-only monotone-head
arguments.  All lemmas are **generic over any `TM.{u}`** (no never-left, no phased-program structure);
they carry only the standard `[propext, Classical.choice, Quot.sound]` execution triple. -/

/-- One `moveHead` step decreases the head value by at most one (in *any* direction): `Move.left`
loses one (or clamps at `0`), `Move.stay` keeps it, `Move.right` only increases it.  The direction-
agnostic dual of `moveHead_val_le_succ`. -/
theorem moveHead_val_succ_ge {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (m : Move) :
    (c.head : ℕ) ≤ ((Configuration.moveHead (c := c) m) : ℕ) + 1 := by
  cases m with
  | left =>
      by_cases h : (c.head : ℕ) = 0
      · simp [Configuration.moveHead, h]
      · rw [Configuration.moveHead_left_val_of_pos c (by omega)]; omega
  | stay => simp [Configuration.moveHead]
  | right =>
      by_cases h : (c.head : ℕ) + 1 < M.tapeLength n
      · rw [Configuration.moveHead_right_lt (c := c) h]
        show (c.head : ℕ) ≤ ((c.head : ℕ) + 1) + 1
        omega
      · rw [Configuration.moveHead_right_clamp (c := c) h]; omega

/-- One `stepConfig` step decreases the head value by at most one (direction-agnostic). -/
theorem stepConfig_head_val_succ_ge {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) :
    (c.head : ℕ) ≤ ((TM.stepConfig (M := M) c).head : ℕ) + 1 := by
  rw [stepConfig_head]
  exact moveHead_val_succ_ge c _

/-- Direction-agnostic lower bound: after `j` steps the head has retreated by at most `j` cells —
`c.head − j ≤ (runConfig c j).head` — for **any** TM (no `TMNeverMovesLeft` assumption).  The
bidirectional dual of `runConfig_head_val_le`. -/
theorem runConfig_head_val_ge {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (j : Nat) :
    (c.head : ℕ) ≤ ((TM.runConfig (M := M) c j).head : ℕ) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [runConfig_succ]
      have step := stepConfig_head_val_succ_ge (M := M) (n := n) (TM.runConfig (M := M) c j)
      omega

/-- Two-sided head-displacement bound for **any** TM: after `j` steps the head stays within `j` cells
of its start, `c.head − j ≤ (runConfig c j).head ≤ c.head + j`.  Combines the generic upper bound
(`runConfig_head_val_le`) with the new direction-agnostic lower bound (`runConfig_head_val_ge`).  This
is the kinematic budget for bidirectional phases — the replacement for the right-only confinement
(`seqList_runConfig_head_bounds`) once `neverMovesLeft` no longer holds. -/
theorem runConfig_head_dist_le {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (j : Nat) :
    (c.head : ℕ) ≤ ((TM.runConfig (M := M) c j).head : ℕ) + j
      ∧ ((TM.runConfig (M := M) c j).head : ℕ) ≤ (c.head : ℕ) + j :=
  ⟨runConfig_head_val_ge c j, runConfig_head_val_le c j⟩

end ContractExpansion
end Frontier
end Pnp4
