import Mathlib.Data.Fin.Basic

/-!
# Versioned uniform deterministic Turing-machine foundation

This is a deliberately small, standalone P1a model.  Its finite control has no
clock, advice, input-length, runtime, or correctness field.  A run's tape type
is indexed by one fixed budget; only the elapsed-step argument changes.
-/

namespace Pnp3.Complexity.Uniform.V1

/-- Boolean strings of exactly `n` bits.  This alias is intentionally local. -/
abbrev Bitstring (n : Nat) := Fin n → Bool

/-- A length-indexed Boolean language.  This alias is intentionally local. -/
abbrev Language := ∀ n, Bitstring n → Bool

/-- The three possible head movements. -/
inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq

/-- Finite machine data only; terminal behavior is imposed by `step`. -/
structure UniformTM where
  stateCount : Nat
  start : Fin stateCount
  accept : Fin stateCount
  reject : Fin stateCount
  accept_ne_reject : accept ≠ reject
  rawStep : Fin stateCount → Bool → Fin stateCount × Bool × Move

/-- Public execution makes both verdict states absorbing and preserves the
scanned cell while staying put.  Consequently raw terminal rows are
unobservable. -/
def UniformTM.step (M : UniformTM) (q : Fin M.stateCount) (b : Bool) :
    Fin M.stateCount × Bool × Move :=
  if q = M.accept then (q, b, Move.stay)
  else if q = M.reject then (q, b, Move.stay)
  else M.rawStep q b

/-- The accept row of the public step is absorbing. -/
theorem UniformTM.step_accept (M : UniformTM) (b : Bool) :
    M.step M.accept b = (M.accept, b, Move.stay) := by
  simp [UniformTM.step]

/-- The reject row of the public step is absorbing. -/
theorem UniformTM.step_reject (M : UniformTM) (b : Bool) :
    M.step M.reject b = (M.reject, b, Move.stay) := by
  simp [UniformTM.step]

/-- A budget-`budget` run on an `n`-bit input has `n + budget + 1` cells. -/
def tapeLength (n budget : Nat) : Nat := n + budget + 1

/-- Full configurations retain the same `n` and `budget` indices throughout a
run. -/
structure Config (k n budget : Nat) where
  state : Fin k
  head : Fin (tapeLength n budget)
  tape : Fin (tapeLength n budget) → Bool

private theorem config_eq {k n budget : Nat} {c d : Config k n budget}
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cstate chead ctape =>
      cases d with
      | mk dstate dhead dtape =>
          change cstate = dstate at hstate
          change chead = dhead at hhead
          change ctape = dtape at htape
          subst dstate
          subst dhead
          subst dtape
          rfl

/-- Move one cell and clamp at the two finite-tape boundaries. -/
def moveHead {length : Nat} (head : Fin length) : Move → Fin length
  | Move.left =>
      ⟨head.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le head.val 1) head.isLt⟩
  | Move.stay => head
  | Move.right =>
      if h : head.val + 1 < length then ⟨head.val + 1, h⟩ else head

/-- A left move at cell zero is clamped to cell zero. -/
theorem moveHead_left_zero (length : Nat) :
    moveHead (⟨0, Nat.zero_lt_succ length⟩ : Fin (length + 1)) Move.left =
      ⟨0, Nat.zero_lt_succ length⟩ := by
  rfl

/-- A right move at the last cell is clamped to the last cell. -/
theorem moveHead_right_last (length : Nat) :
    moveHead (Fin.last length) Move.right = Fin.last length := by
  simp [moveHead, Fin.last]

/-- Initial configuration: input at the left edge and false padding. -/
def initialConfig (M : UniformTM) {n : Nat} (budget : Nat) (x : Bitstring n) :
    Config M.stateCount n budget where
  state := M.start
  head := ⟨0, by simp [tapeLength]⟩
  tape := fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

/-- One full transition on the fixed-budget tape. -/
def UniformTM.stepConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) : Config M.stateCount n budget :=
  let action := M.step c.state (c.tape c.head)
  { state := action.1
    head := moveHead c.head action.2.2
    tape := fun i => if i = c.head then action.2.1 else c.tape i }

/-- Accepting full configurations are fixed points. -/
theorem UniformTM.stepConfig_accept (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.accept) :
    M.stepConfig c = c := by
  cases c with
  | mk state head tape =>
      change state = M.accept at h
      subst state
      apply config_eq
      · simp [UniformTM.stepConfig, UniformTM.step]
      · simp [UniformTM.stepConfig, UniformTM.step, moveHead]
      · funext i
        by_cases hi : i = head
        · subst i
          simp [UniformTM.stepConfig, UniformTM.step]
        · simp [UniformTM.stepConfig, UniformTM.step, hi]

/-- Rejecting full configurations are fixed points. -/
theorem UniformTM.stepConfig_reject (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.reject) :
    M.stepConfig c = c := by
  cases c with
  | mk state head tape =>
      change state = M.reject at h
      subst state
      apply config_eq
      · simp [UniformTM.stepConfig, UniformTM.step]
      · simp [UniformTM.stepConfig, UniformTM.step, moveHead]
      · funext i
        by_cases hi : i = head
        · subst i
          simp [UniformTM.stepConfig, UniformTM.step]
        · simp [UniformTM.stepConfig, UniformTM.step, hi]

/-- Execute `steps` transitions without changing the tape's budget index. -/
def UniformTM.run (M : UniformTM) {n budget : Nat} :
    Nat → Config M.stateCount n budget → Config M.stateCount n budget
  | 0, c => c
  | steps + 1, c => M.stepConfig (M.run steps c)

/-- Runs compose additively on the same budget-indexed configuration type. -/
theorem UniformTM.run_add (M : UniformTM) {n budget : Nat} (a b : Nat)
    (c : Config M.stateCount n budget) :
    M.run (a + b) c = M.run b (M.run a c) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      simpa [Nat.add_succ, UniformTM.run] using congrArg M.stepConfig ih

/-- Any run from an accepting full configuration is unchanged. -/
theorem UniformTM.run_accept (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.accept) (steps : Nat) :
    M.run steps c = c := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [UniformTM.run, ih, M.stepConfig_accept c h]

/-- Any run from a rejecting full configuration is unchanged. -/
theorem UniformTM.run_reject (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.reject) (steps : Nat) :
    M.run steps c = c := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [UniformTM.run, ih, M.stepConfig_reject c h]

/-- Initial tape cells below `n` contain the input. -/
theorem initialConfig_tape_input (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (i : Fin n) :
    (initialConfig M budget x).tape
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n (budget + 1))⟩ = x i := by
  simp [initialConfig]

/-- Initial tape cells at or above `n` are false padding. -/
theorem initialConfig_tape_padding (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (i : Fin (tapeLength n budget)) (h : n ≤ i.val) :
    (initialConfig M budget x).tape i = false := by
  simp [initialConfig, Nat.not_lt_of_ge h]

/-- Acceptance after exactly `steps` transitions on a `budget` tape. -/
def AcceptsAt (M : UniformTM) {n : Nat} (budget steps : Nat) (x : Bitstring n) : Prop :=
  (M.run steps (initialConfig M budget x)).state = M.accept

/-- Literal rejection after exactly `steps` transitions on a `budget` tape. -/
def RejectsAt (M : UniformTM) {n : Nat} (budget steps : Nat) (x : Bitstring n) : Prop :=
  (M.run steps (initialConfig M budget x)).state = M.reject

/-- Acceptance at some time no later than the fixed tape budget. -/
def AcceptsWithin (M : UniformTM) {n : Nat} (budget : Nat) (x : Bitstring n) : Prop :=
  ∃ steps ≤ budget, AcceptsAt M budget steps x

/-- Literal rejection at some time no later than the fixed tape budget. -/
def RejectsWithin (M : UniformTM) {n : Nat} (budget : Nat) (x : Bitstring n) : Prop :=
  ∃ steps ≤ budget, RejectsAt M budget steps x

private theorem acceptsAt_add (M : UniformTM) {n budget steps : Nat}
    (x : Bitstring n) (h : AcceptsAt M budget steps x) (extra : Nat) :
    AcceptsAt M budget (steps + extra) x := by
  change (M.run steps (initialConfig M budget x)).state = M.accept at h
  rw [AcceptsAt, M.run_add]
  rw [M.run_accept (M.run steps (initialConfig M budget x)) h extra]
  exact h

private theorem rejectsAt_add (M : UniformTM) {n budget steps : Nat}
    (x : Bitstring n) (h : RejectsAt M budget steps x) (extra : Nat) :
    RejectsAt M budget (steps + extra) x := by
  change (M.run steps (initialConfig M budget x)).state = M.reject at h
  rw [RejectsAt, M.run_add]
  rw [M.run_reject (M.run steps (initialConfig M budget x)) h extra]
  exact h

/-- By full-configuration absorption and run addition, exact deadline
acceptance is equivalent to acceptance within the same tape budget. -/
theorem acceptsAt_budget_iff_acceptsWithin (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) :
    AcceptsAt M budget budget x ↔ AcceptsWithin M budget x := by
  constructor
  · intro h
    exact ⟨budget, Nat.le_refl budget, h⟩
  · rintro ⟨steps, hsteps, haccept⟩
    have h := acceptsAt_add M x haccept (budget - steps)
    simpa [Nat.add_sub_of_le hsteps] using h

/-- By full-configuration absorption and run addition, exact deadline
rejection is equivalent to rejection within the same tape budget. -/
theorem rejectsAt_budget_iff_rejectsWithin (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) :
    RejectsAt M budget budget x ↔ RejectsWithin M budget x := by
  constructor
  · intro h
    exact ⟨budget, Nat.le_refl budget, h⟩
  · rintro ⟨steps, hsteps, hreject⟩
    have h := rejectsAt_add M x hreject (budget - steps)
    simpa [Nat.add_sub_of_le hsteps] using h

/-- A configuration cannot carry both distinct verdict states at one time. -/
theorem not_acceptsAt_and_rejectsAt (M : UniformTM) {n budget steps : Nat}
    (x : Bitstring n) :
    ¬ (AcceptsAt M budget steps x ∧ RejectsAt M budget steps x) := by
  rintro ⟨ha, hr⟩
  exact M.accept_ne_reject (ha.symm.trans hr)

/-- Absorption aligns any two within-budget verdicts at the deadline, where
distinct terminal states make simultaneous acceptance and rejection
impossible. -/
theorem not_acceptsWithin_and_rejectsWithin (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) :
    ¬ (AcceptsWithin M budget x ∧ RejectsWithin M budget x) := by
  rintro ⟨ha, hr⟩
  exact not_acceptsAt_and_rejectsAt M x
    ⟨(acceptsAt_budget_iff_acceptsWithin M x).2 ha,
      (rejectsAt_budget_iff_rejectsWithin M x).2 hr⟩

/-- Exact decision semantics: true means accept and false means literal reject. -/
def DecidesAt (M : UniformTM) {n : Nat} (budget steps : Nat)
    (x : Bitstring n) (answer : Bool) : Prop :=
  if answer then AcceptsAt M budget steps x else RejectsAt M budget steps x

/-- Within-budget decision semantics: true means accept and false means literal
reject.  A timeout is neither branch. -/
def DecidesWithin (M : UniformTM) {n : Nat} (budget : Nat)
    (x : Bitstring n) (answer : Bool) : Prop :=
  if answer then AcceptsWithin M budget x else RejectsWithin M budget x

/-- Exact-deadline and within-budget decision semantics coincide. -/
theorem decidesAt_budget_iff_decidesWithin (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (answer : Bool) :
    DecidesAt M budget budget x answer ↔ DecidesWithin M budget x answer := by
  cases answer <;>
    simp [DecidesAt, DecidesWithin, acceptsAt_budget_iff_acceptsWithin,
      rejectsAt_budget_iff_rejectsWithin]

/-- Exact execution cannot decide both Boolean answers. -/
theorem not_decidesAt_true_and_false (M : UniformTM) {n budget steps : Nat}
    (x : Bitstring n) :
    ¬ (DecidesAt M budget steps x true ∧ DecidesAt M budget steps x false) := by
  simpa [DecidesAt] using not_acceptsAt_and_rejectsAt M x

/-- Within-budget execution cannot decide both Boolean answers. -/
theorem not_decidesWithin_true_and_false (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) :
    ¬ (DecidesWithin M budget x true ∧ DecidesWithin M budget x false) := by
  simpa [DecidesWithin] using not_acceptsWithin_and_rejectsWithin M x

end Pnp3.Complexity.Uniform.V1
