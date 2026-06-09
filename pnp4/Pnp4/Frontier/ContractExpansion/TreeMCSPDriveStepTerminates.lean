import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStep

/-!
# `step_reachesTerminal` — D2t-5b: the small-step driver terminates (the pure mirror of `reachesSink`)

`TreeMCSPDriveStep` ships the one-micro-step driver `DriveState.step`, its measure `mu`, and the two
facts the on-tape loop needs: `mu_step_lt` (off a terminal state `mu` strictly drops) and `step_terminal`
(a terminal state is fixed).  This module closes the loop on the **pure** side: iterating `step` always
**reaches a terminal state**, in at most `mu` steps — the exact pure analogue of the on-tape
`loopUntilSink_reachesSink` (strong induction on the measure, the same shape the machine discharge will
transcribe).

* `step_reachesTerminal` — from any micro-state, `∃ k, (step^[k] s).terminal`.
* `driveStep_halts_with_flatten` — **the headline**: run from `⟨preorder c, [], [], [], false⟩`, the
  small-step driver halts (reaches a terminal state — the loop's sink) with WORK exactly
  `(flatten c).gates`, the postorder flatten.

Together with `driveStep_out_eq_flatten` this gives the full pure correctness-and-termination statement the
on-tape D2t-5b `loopUntilSink` driver realises.

**Progress classification (AGENTS.md): Infrastructure** — a pure termination proof for the small-step
driver spec; builds no machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The small-step driver terminates.**  From any micro-state, iterating `step` reaches a terminal state
(tokens exhausted, not settling) — in at most `mu s` steps.  Strong induction on the measure `mu` via
`mu_step_lt` (non-terminal ⇒ strictly smaller measure) and `step_terminal` (terminal ⇒ fixed). -/
theorem step_reachesTerminal {n : Nat} (s : DriveState n) :
    ∃ k, (DriveState.step^[k] s).terminal := by
  suffices H : ∀ m (s : DriveState n), s.mu = m → ∃ k, (DriveState.step^[k] s).terminal by
    exact H s.mu s rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hm
    by_cases hterm : s.terminal
    · exact ⟨0, hterm⟩
    · have hlt : s.step.mu < m := hm ▸ DriveState.mu_step_lt s hterm
      obtain ⟨k, hk⟩ := ih s.step.mu hlt s.step rfl
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hk

/-- **The small-step driver halts with the flatten.**  Run from the empty initial state, iterating `step`
reaches a terminal state (the loop's halt condition) whose WORK is exactly `(flatten c).gates` — the full
pure correctness-and-termination statement realised by the on-tape D2t-5b driver loop. -/
theorem driveStep_halts_with_flatten {n : Nat} (c : CircuitTree n) :
    ∃ k, (DriveState.step^[k] ⟨preorder c, [], [], [], false⟩).terminal
      ∧ (DriveState.step^[k] ⟨preorder c, [], [], [], false⟩).out = (CircuitTree.flatten c).gates := by
  obtain ⟨k, hk⟩ := driveStep_drive c
  refine ⟨k, ?_, ?_⟩
  · rw [hk]; exact ⟨rfl, rfl⟩
  · rw [hk]; show driveWORK c = (CircuitTree.flatten c).gates; exact driveWORK_eq_flatten c

end ContractExpansion
end Frontier
end Pnp4
