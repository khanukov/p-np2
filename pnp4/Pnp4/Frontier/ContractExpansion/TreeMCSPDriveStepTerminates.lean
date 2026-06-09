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

/-! ### Explicit step-count bound (the polynomial runtime witness for the on-tape driver) -/

/-- Terminal states are **fixed by iteration**: once the certificate is consumed the loop idles for any
number of further steps. -/
theorem DriveState.step_terminal_state_stays {n : Nat} (s : DriveState n) (h : s.terminal) :
    ∀ j, DriveState.step^[j] s = s := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, DriveState.step_terminal s h]; exact ih

/-- Once a prefix of the run reaches a terminal state, every longer prefix lands on the **same** state
(terminal is absorbing). -/
theorem DriveState.step_after_terminal {n : Nat} (s : DriveState n) {a : Nat}
    (h : (DriveState.step^[a] s).terminal) {b : Nat} (hab : a ≤ b) :
    DriveState.step^[b] s = DriveState.step^[a] s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_comm a d, Function.iterate_add_apply, DriveState.step_terminal_state_stays _ h d]

/-- **Termination within `mu` steps.**  After exactly `mu s` iterations the driver is terminal — the
explicit step-count bound (strong induction on `mu`: the non-terminal step drops `mu`, and
`step_after_terminal` absorbs the slack). -/
theorem DriveState.step_terminal_at_mu {n : Nat} (s : DriveState n) :
    (DriveState.step^[s.mu] s).terminal := by
  suffices H : ∀ m (s : DriveState n), s.mu = m → (DriveState.step^[s.mu] s).terminal by
    exact H s.mu s rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hm
    by_cases hterm : s.terminal
    · rw [DriveState.step_terminal_state_stays s hterm]; exact hterm
    · have hlt : s.step.mu < s.mu := DriveState.mu_step_lt s hterm
      have key : (DriveState.step^[s.step.mu] s.step).terminal := ih s.step.mu (by omega) s.step rfl
      have key' : (DriveState.step^[s.step.mu + 1] s).terminal := by
        rw [Function.iterate_succ_apply]; exact key
      have hb1 : s.step.mu + 1 ≤ s.mu := by omega
      rw [DriveState.step_after_terminal s key' hb1]
      exact key'

/-- The preorder token stream has exactly one token per tree node: `|preorder c| = c.size`. -/
theorem preorder_length {n : Nat} (c : CircuitTree n) : (preorder c).length = c.size := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih => simp only [preorder, List.length_cons, ih, CircuitTree.size]
  | and a b iha ihb =>
      simp only [preorder, List.length_cons, List.length_append, iha, ihb, CircuitTree.size]
  | or a b iha ihb =>
      simp only [preorder, List.length_cons, List.length_append, iha, ihb, CircuitTree.size]

/-- The measure of the empty initial state is `3 · c.size` — the driver's explicit step budget. -/
theorem mu_init {n : Nat} (c : CircuitTree n) :
    (⟨preorder c, [], [], [], false⟩ : DriveState n).mu = 3 * c.size := by
  simp [DriveState.mu, preorder_length]

/-- **D2t-5b driver step-count bound.**  Within `3 · c.size` micro-steps the driver has halted (terminal)
with WORK exactly `(flatten c).gates` — the explicit polynomial runtime witness the on-tape `loopUntilSink`
driver inherits (each micro-step = one bounded body pass). -/
theorem driveStep_halts_bound {n : Nat} (c : CircuitTree n) :
    (DriveState.step^[3 * c.size] (⟨preorder c, [], [], [], false⟩ : DriveState n)).terminal
    ∧ (DriveState.step^[3 * c.size] (⟨preorder c, [], [], [], false⟩ : DriveState n)).out
        = (CircuitTree.flatten c).gates := by
  obtain ⟨k, hk⟩ := driveStep_drive c
  have hkterm : (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).terminal := by
    rw [hk]; exact ⟨rfl, rfl⟩
  have hbterm : (DriveState.step^[3 * c.size]
      (⟨preorder c, [], [], [], false⟩ : DriveState n)).terminal := by
    have h := DriveState.step_terminal_at_mu (⟨preorder c, [], [], [], false⟩ : DriveState n)
    rwa [mu_init c] at h
  have e1 := DriveState.step_after_terminal (⟨preorder c, [], [], [], false⟩ : DriveState n) hkterm
    (le_max_left k (3 * c.size))
  have e2 := DriveState.step_after_terminal (⟨preorder c, [], [], [], false⟩ : DriveState n) hbterm
    (le_max_right k (3 * c.size))
  have heq : DriveState.step^[3 * c.size] (⟨preorder c, [], [], [], false⟩ : DriveState n)
      = DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n) := by rw [← e2, e1]
  refine ⟨hbterm, ?_⟩
  rw [heq, hk]
  show driveWORK c = (CircuitTree.flatten c).gates
  exact driveWORK_eq_flatten c

end ContractExpansion
end Frontier
end Pnp4
