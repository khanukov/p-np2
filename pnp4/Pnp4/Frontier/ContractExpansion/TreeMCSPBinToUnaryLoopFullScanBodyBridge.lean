import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanPeel

/-!
# `binToUnaryLoopFullScan` body bridge — collapsing the depth-4 nesting (NP-verifier track — D2t-3 `ε`)

`hstep`'s body leg, foundational tool.  The sound loop body
`binToUnaryLoopBodyFullScan w = seq stepRightOnce (seq (bZeroFullScanRouteBody w)
  (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)))`
buries `binToUnaryBody` at **`seq`-depth 4**, occupying composition phases `w + 15 .. w + 29` (its
local phases `0 .. 14` shifted up by `stepRightOnce (2) + bZeroFullScanRouteBody (w+2) + stepRightOnce (2)
+ seekHomeAfterRoute (9) = w + 15`).

On the **Rehome** loop the body sits at depth 2 with *concrete* phases `15 .. 29`, so each single step is
re-derived by one `simp [seq, seqList, …]` that evaluates the nested routing by computation
(`TreeMCSPBinToUnaryLoopRehomeBodyStep.lean`).  Here the phase `w + 15 + k` is **symbolic in `w`**, so
that `simp` cannot decide `i.val < P1.numPhases` (e.g. `P1.numPhases = w + 2`) and whnf-blows up.

This module supplies the missing tool: a **bridge** that, via four `seq_transition_P2_*` lifts (each with
`omega`-discharged region/bound side-conditions that tolerate the symbolic `w`), rewrites the loop body's
transition at composition phase `w + 15 + k` (`k < 15`) to `binToUnaryBody`'s transition at its local
phase `k` — the phase shifted up by `w + 15`, the local state / written bit / head move inherited
verbatim.  Composed with the loop peel (`binToUnaryLoopFullScan_transition_body`) and `binToUnaryBody`'s
*concrete*-phase transition (which `decide`/`simp` then evaluate), it turns each body single step into the
short, symbolic-`w`-robust form — the FullScan analogue of the Rehome body's per-step `simp`.

**Progress classification (AGENTS.md): Infrastructure** — a transition-rewrite lemma toward the
NP-membership leg; it proves no run behaviour and builds no verifier.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option linter.unusedSimpArgs false in
/-- **Body bridge — phase.**  At composition phase `w + 15 + k` (`k < 15`) the loop body's transition
advances to phase `w + 15 + (binToUnaryBody.transition ⟨k⟩ s b).fst` — `binToUnaryBody`'s local next
phase shifted up by `w + 15`. -/
theorem binToUnaryLoopBodyFullScan_atBody_phase (w k : Nat) (hk : k < 15)
    {i : Fin (binToUnaryLoopBodyFullScan w).numPhases}
    (hi : (i : Nat) = w + 15 + k) (s : Unit) (b : Bool) :
    ((binToUnaryLoopBodyFullScan w).transition i s b).fst.val
      = w + 15 + (binToUnaryBody.transition ⟨k, by rw [binToUnaryBody_numPhases]; exact hk⟩ s b).fst.val := by
  unfold binToUnaryLoopBodyFullScan
  rw [seq_transition_P2_phase stepRightOnce
        (seq (bZeroFullScanRouteBody w) (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_phase (bZeroFullScanRouteBody w)
        (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_phase stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_phase seekHomeAfterRoute binToUnaryBody
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  simp only [stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases, seekHomeAfterRoute_numPhases]
  simp only [show (↑i - 2 - (w + 2) - 2 - 9 : Nat) = k from by omega]
  omega

set_option linter.unusedSimpArgs false in
/-- **Body bridge — written bit.**  At composition phase `w + 15 + k` (`k < 15`) the loop body writes the
bit `binToUnaryBody`'s transition would write at local phase `k`. -/
theorem binToUnaryLoopBodyFullScan_atBody_bit (w k : Nat) (hk : k < 15)
    {i : Fin (binToUnaryLoopBodyFullScan w).numPhases}
    (hi : (i : Nat) = w + 15 + k) (s : Unit) (b : Bool) :
    ((binToUnaryLoopBodyFullScan w).transition i s b).snd.snd.fst
      = (binToUnaryBody.transition ⟨k, by rw [binToUnaryBody_numPhases]; exact hk⟩ s b).snd.snd.fst := by
  unfold binToUnaryLoopBodyFullScan
  rw [seq_transition_P2_bit stepRightOnce
        (seq (bZeroFullScanRouteBody w) (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_bit (bZeroFullScanRouteBody w)
        (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_bit stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_bit seekHomeAfterRoute binToUnaryBody
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  simp only [stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases, seekHomeAfterRoute_numPhases]
  simp only [show (↑i - 2 - (w + 2) - 2 - 9 : Nat) = k from by omega]

set_option linter.unusedSimpArgs false in
/-- **Body bridge — head move.**  At composition phase `w + 15 + k` (`k < 15`) the loop body moves the
head as `binToUnaryBody`'s transition would at local phase `k`. -/
theorem binToUnaryLoopBodyFullScan_atBody_move (w k : Nat) (hk : k < 15)
    {i : Fin (binToUnaryLoopBodyFullScan w).numPhases}
    (hi : (i : Nat) = w + 15 + k) (s : Unit) (b : Bool) :
    ((binToUnaryLoopBodyFullScan w).transition i s b).snd.snd.snd
      = (binToUnaryBody.transition ⟨k, by rw [binToUnaryBody_numPhases]; exact hk⟩ s b).snd.snd.snd := by
  unfold binToUnaryLoopBodyFullScan
  rw [seq_transition_P2_move stepRightOnce
        (seq (bZeroFullScanRouteBody w) (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_move (bZeroFullScanRouteBody w)
        (seq stepRightOnce (seq seekHomeAfterRoute binToUnaryBody))
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_move stepRightOnce (seq seekHomeAfterRoute binToUnaryBody)
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  rw [seq_transition_P2_move seekHomeAfterRoute binToUnaryBody
        (h2 := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega)
        (hi_lt := by simp only [Fin.val_mk, stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases,
          seekHomeAfterRoute_numPhases, binToUnaryBody_numPhases, seq_numPhases]; omega) s b]
  simp only [stepRightOnce_numPhases, bZeroFullScanRouteBody_numPhases, seekHomeAfterRoute_numPhases]
  simp only [show (↑i - 2 - (w + 2) - 2 - 9 : Nat) = k from by omega]

end ContractExpansion
end Frontier
end Pnp4
