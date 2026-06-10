import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRoute

/-!
# `bZeroRouteProgram` run-through, P2 region (NP-verifier track — D2t-3 routing run-through)

`TreeMCSPBZeroRoute.lean` ships the composed routing program `bZeroRouteProgram :=
seq gammaSelfLoopScan stepRightThenBranch` and its structural layer.  This module proves the **P2-region
run-through**: once control has handed off into the `stepRightThenBranch` half (phase `2`, i.e.
`embedSeqP2Config` of `stepRightThenBranch`'s start), two steps reach the composed branch target —

* **`bZeroRouteProgram_P2_runConfig_branch_true`** — reading `1` one cell right ⇒ composed phase `4`
  (the `B = 0` → sink target);
* **`bZeroRouteProgram_P2_runConfig_branch_false`** — reading `0` ⇒ composed phase `5`
  (the `B > 0` → body-entry target).

Both lift `stepRightThenBranch_runConfig_branch_*` through `embedSeqP2Config_runConfig_eq` (`seq`'s
P2-region simulation).  The lift's safety obligation (right-moves stay in bounds) discharges from the
generic `runConfig_head_val_le` (head advances `≤` steps) under the mild bound `c.head + 2 < tapeLength`
— which holds with room to spare in the real layout (the scan-stop lies in the input region `[0, L)`,
while `tapeLength = 2L+1`).

This is the **P2 half** of the composed run-through; the **P1-region** (the scan running to its stop in
`seq`'s first region) and the **handoff** step, then the full composition (`scan-steps + 1 + 2` → reaches
phase `4` iff `B = 0`), are the remaining run-through pieces, followed by `ε` (`loopUntilSink`) and `ζ`.

**Progress classification (AGENTS.md): Infrastructure** — run-behaviour of a composed control program
toward the NP-membership leg.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No
`P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Safety obligation for `embedSeqP2Config_runConfig_eq` over `stepRightThenBranch` for `2` steps:
the run stays in-phase (any `Fin numPhases`) and right-moves stay in bounds (head advances `≤ s ≤ 1`
cells, and `c.head + 2 < tapeLength`). -/
private theorem stepRightThenBranch_P2_safe {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hbnd2 : (c.head : Nat) + 2 < stepRightThenBranch.toPhased.toTM.tapeLength L) :
    ∀ s < 2,
      (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).state.fst.val
          < stepRightThenBranch.numPhases ∧
      ((stepRightThenBranch.toPhased.toTM.step
          (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).state
          ((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).tape
            (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).head)).snd.snd = Move.right →
        (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).head.val + 1
          < stepRightThenBranch.toPhased.toTM.tapeLength L) := by
  intro s hs
  refine ⟨(TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c s).state.fst.isLt, fun _ => ?_⟩
  have hle := runConfig_head_val_le (M := stepRightThenBranch.toPhased.toTM) c s
  omega

/-- **P2 region, `read = 1`.**  From the embedded `stepRightThenBranch` start (composed phase `2`) with
the cell one to the right reading `1`, two steps of `bZeroRouteProgram` reach composed phase `4` (the
`B = 0` → sink target). -/
theorem bZeroRouteProgram_P2_runConfig_branch_true {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hbnd2 : (c.head : Nat) + 2 < stepRightThenBranch.toPhased.toTM.tapeLength L)
    (hstart : (c.state.fst : Nat) = 0)
    (hread : c.tape ⟨(c.head : Nat) + 1, Nat.lt_of_succ_lt hbnd2⟩ = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        (embedSeqP2Config gammaSelfLoopScan stepRightThenBranch c) 2).state).fst : Nat) = 4 := by
  rw [embedSeqP2Config_runConfig_eq gammaSelfLoopScan stepRightThenBranch c 2
        (stepRightThenBranch_P2_safe c hbnd2),
      embedSeqP2Config_state_fst_val]
  obtain ⟨hbr, _, _⟩ := stepRightThenBranch_runConfig_branch_true c (Nat.lt_of_succ_lt hbnd2) hstart hread
  rw [hbr]; decide

/-- **P2 region, `read = 0`.**  From the embedded `stepRightThenBranch` start (composed phase `2`) with
the cell one to the right reading `0`, two steps of `bZeroRouteProgram` reach composed phase `5` (the
`B > 0` → body-entry target). -/
theorem bZeroRouteProgram_P2_runConfig_branch_false {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hbnd2 : (c.head : Nat) + 2 < stepRightThenBranch.toPhased.toTM.tapeLength L)
    (hstart : (c.state.fst : Nat) = 0)
    (hread : c.tape ⟨(c.head : Nat) + 1, Nat.lt_of_succ_lt hbnd2⟩ = false) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        (embedSeqP2Config gammaSelfLoopScan stepRightThenBranch c) 2).state).fst : Nat) = 5 := by
  rw [embedSeqP2Config_runConfig_eq gammaSelfLoopScan stepRightThenBranch c 2
        (stepRightThenBranch_P2_safe c hbnd2),
      embedSeqP2Config_state_fst_val]
  obtain ⟨hbr, _, _⟩ := stepRightThenBranch_runConfig_branch_false c (Nat.lt_of_succ_lt hbnd2) hstart hread
  rw [hbr]; decide

end ContractExpansion
end Frontier
end Pnp4
