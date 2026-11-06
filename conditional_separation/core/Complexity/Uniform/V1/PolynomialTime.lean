import Complexity.Uniform.V1.Machine

/-!
# Polynomial clocks and the versioned `UniformP` predicate
-/

namespace Pnp3.Complexity.Uniform.V1

/-- The pinned P1a polynomial clock family. -/
def polyClock (c n : Nat) : Nat := n ^ c + c

/-- Exponent zero always gives the one-step clock. -/
theorem polyClock_exponent_zero (n : Nat) : polyClock 0 n = 1 := by
  simp [polyClock]

/-- The `c = 0`, `n = 0` corner is one, following `0 ^ 0 = 1`. -/
theorem polyClock_zero_zero : polyClock 0 0 = 1 := by
  simp [polyClock]

/-- At input length zero the clock is one for exponent zero and otherwise is
the exponent itself. -/
theorem polyClock_input_zero (c : Nat) :
    polyClock c 0 = if c = 0 then 1 else c := by
  cases c <;> simp [polyClock]

/-- Exponent one gives the linear clock `n + 1`. -/
theorem polyClock_exponent_one (n : Nat) : polyClock 1 n = n + 1 := by
  simp [polyClock]

/-- Every pinned polynomial clock has at least one step. -/
theorem polyClock_pos (c n : Nat) : 0 < polyClock c n := by
  cases c with
  | zero => simp [polyClock]
  | succ c =>
      exact Nat.add_pos_right (n ^ (c + 1)) (Nat.zero_lt_succ c)

/-- One fixed finite machine and one fixed exponent decide all input lengths. -/
def UniformP (L : Language) : Prop :=
  ∃ M c, ∀ n (x : Bitstring n),
    DecidesWithin M (polyClock c n) x (L n x)

/-- P1b handoff: within-budget `UniformP` is exactly equivalent to an
exact-deadline presentation on the same clock-indexed tape. -/
theorem uniformP_iff_exists_decidesAt (L : Language) :
    UniformP L ↔
      ∃ M c, ∀ n (x : Bitstring n),
        DecidesAt M (polyClock c n) (polyClock c n) x (L n x) := by
  constructor
  · rintro ⟨M, c, h⟩
    exact ⟨M, c, fun n x =>
      (decidesAt_budget_iff_decidesWithin M x (L n x)).2 (h n x)⟩
  · rintro ⟨M, c, h⟩
    exact ⟨M, c, fun n x =>
      (decidesAt_budget_iff_decidesWithin M x (L n x)).1 (h n x)⟩

/-- Swap the two terminal labels without changing finite control or raw rows. -/
def UniformTM.swap (M : UniformTM) : UniformTM where
  stateCount := M.stateCount
  start := M.start
  accept := M.reject
  reject := M.accept
  accept_ne_reject := M.accept_ne_reject.symm
  rawStep := M.rawStep

/-- Swapping terminal labels leaves every executable transition unchanged. -/
theorem UniformTM.swap_step (M : UniformTM) (q : Fin M.stateCount)
    (symbol : Option Bool) :
    M.swap.step q symbol = M.step q symbol := by
  by_cases ha : q = M.accept <;> by_cases hr : q = M.reject <;>
    simp [UniformTM.swap, UniformTM.step, ha, hr, M.accept_ne_reject]

/-- Therefore swapping terminal labels leaves full configuration steps
unchanged. -/
theorem UniformTM.swap_stepConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    M.swap.stepConfig c = M.stepConfig c := by
  simp [UniformTM.stepConfig, M.swap_step]

/-- Therefore swapped and original runs have identical configurations. -/
theorem UniformTM.swap_run (M : UniformTM) {n budget : Nat} (steps : Nat)
    (c : Config M.stateCount n budget) :
    M.swap.run steps c = M.run steps c := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [UniformTM.run, ih, M.swap_stepConfig]

/-- Swapped acceptance is original literal rejection at the same time and on
the same budget tape. -/
theorem UniformTM.swap_acceptsAt_iff_rejectsAt (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    AcceptsAt M.swap budget steps x ↔ RejectsAt M budget steps x := by
  change
    (M.swap.run steps (initialConfig M.swap budget x)).state = M.reject ↔
      (M.run steps (initialConfig M budget x)).state = M.reject
  rw [M.swap_run steps (initialConfig M.swap budget x)]
  rfl

/-- Swapped rejection is original acceptance at the same time and on the same
budget tape. -/
theorem UniformTM.swap_rejectsAt_iff_acceptsAt (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    RejectsAt M.swap budget steps x ↔ AcceptsAt M budget steps x := by
  change
    (M.swap.run steps (initialConfig M.swap budget x)).state = M.accept ↔
      (M.run steps (initialConfig M budget x)).state = M.accept
  rw [M.swap_run steps (initialConfig M.swap budget x)]
  rfl

private theorem swap_acceptsWithin_iff_rejectsWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    AcceptsWithin M.swap budget x ↔ RejectsWithin M budget x := by
  constructor
  · rintro ⟨steps, hsteps, h⟩
    exact ⟨steps, hsteps, (M.swap_acceptsAt_iff_rejectsAt x).1 h⟩
  · rintro ⟨steps, hsteps, h⟩
    exact ⟨steps, hsteps, (M.swap_acceptsAt_iff_rejectsAt x).2 h⟩

private theorem swap_rejectsWithin_iff_acceptsWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    RejectsWithin M.swap budget x ↔ AcceptsWithin M budget x := by
  constructor
  · rintro ⟨steps, hsteps, h⟩
    exact ⟨steps, hsteps, (M.swap_rejectsAt_iff_acceptsAt x).1 h⟩
  · rintro ⟨steps, hsteps, h⟩
    exact ⟨steps, hsteps, (M.swap_rejectsAt_iff_acceptsAt x).2 h⟩

/-- Swapping decides the Boolean negation exactly when the original decides the
original answer. -/
theorem UniformTM.swap_decidesWithin (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (answer : Bool) :
    DecidesWithin M.swap budget x (!answer) ↔ DecidesWithin M budget x answer := by
  cases answer <;>
    simp [DecidesWithin, swap_acceptsWithin_iff_rejectsWithin,
      swap_rejectsWithin_iff_acceptsWithin]

/-- Pointwise language complement. -/
def complement (L : Language) : Language := fun n x => !(L n x)

/-- `UniformP` is closed under complement by a finite terminal-label swap. -/
theorem uniformP_complement (L : Language) (h : UniformP L) :
    UniformP (complement L) := by
  rcases h with ⟨M, c, hM⟩
  refine ⟨M.swap, c, ?_⟩
  intro n x
  exact (M.swap_decidesWithin x (L n x)).2 (hM n x)

end Pnp3.Complexity.Uniform.V1
