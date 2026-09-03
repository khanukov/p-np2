import Complexity.Uniform.V1.PolynomialTime

/-!
# Literal machines for the Uniform P V1 foundation

These closed finite records are executable sanity checks, including a machine
that never reaches either verdict and therefore pins timeout as distinct from
literal rejection.
-/

namespace Pnp3.Complexity.Uniform.V1

/-- Constant-true language. -/
def constTrue : Language := fun _ _ => true

/-- Constant-false language. -/
def constFalse : Language := fun _ _ => false

/-- The first input bit, with empty input defined to be false. -/
def firstBit : Language := fun n x =>
  if h : 0 < n then x ⟨0, h⟩ else false

/-- A genuine two-state literal whose start state is its accept state. -/
def allAcceptMachine : UniformTM :=
  UniformTM.mk
    2
    (⟨0, by decide⟩)
    (⟨0, by decide⟩)
    (⟨1, by decide⟩)
    (by decide)
    (fun q b => (q, b, Move.stay))

/-- A genuine two-state literal whose start state is its reject state. -/
def allRejectMachine : UniformTM :=
  UniformTM.mk
    2
    (⟨1, by decide⟩)
    (⟨0, by decide⟩)
    (⟨1, by decide⟩)
    (by decide)
    (fun q b => (q, b, Move.stay))

/-- The all-accept literal accepts at every exact time. -/
theorem allAccept_acceptsAt {n budget steps : Nat} (x : Bitstring n) :
    AcceptsAt allAcceptMachine budget steps x := by
  change
    (allAcceptMachine.run steps
      (initialConfig allAcceptMachine budget x)).state = allAcceptMachine.accept
  rw [allAcceptMachine.run_accept
    (initialConfig allAcceptMachine budget x) (by rfl) steps]
  rfl

/-- The all-accept literal accepts within every budget, including zero. -/
theorem allAccept_acceptsWithin {n budget : Nat} (x : Bitstring n) :
    AcceptsWithin allAcceptMachine budget x :=
  ⟨0, Nat.zero_le budget, allAccept_acceptsAt x⟩

/-- The all-reject literal rejects at every exact time. -/
theorem allReject_rejectsAt {n budget steps : Nat} (x : Bitstring n) :
    RejectsAt allRejectMachine budget steps x := by
  change
    (allRejectMachine.run steps
      (initialConfig allRejectMachine budget x)).state = allRejectMachine.reject
  rw [allRejectMachine.run_reject
    (initialConfig allRejectMachine budget x) (by rfl) steps]
  rfl

/-- The all-reject literal rejects within every budget, including zero. -/
theorem allReject_rejectsWithin {n budget : Nat} (x : Bitstring n) :
    RejectsWithin allRejectMachine budget x :=
  ⟨0, Nat.zero_le budget, allReject_rejectsAt x⟩

/-- A three-state literal that branches after one step on the scanned first
bit.  Padding makes the empty-input branch false. -/
def firstBitMachine : UniformTM :=
  UniformTM.mk
    3
    (⟨0, by decide⟩)
    (⟨1, by decide⟩)
    (⟨2, by decide⟩)
    (by decide)
    (fun q b =>
      if q = (⟨0, by decide⟩ : Fin 3) then
        if b then
          (⟨1, by decide⟩, b, Move.stay)
        else
          (⟨2, by decide⟩, b, Move.stay)
      else
        (q, b, Move.stay))

private theorem firstBit_run_one_state {n budget : Nat} (x : Bitstring n) :
    (firstBitMachine.run 1
      (initialConfig firstBitMachine budget x)).state =
        if firstBit n x then firstBitMachine.accept else firstBitMachine.reject := by
  cases n with
  | zero =>
      simp [UniformTM.run, UniformTM.stepConfig, UniformTM.step, initialConfig,
        firstBitMachine, firstBit]
  | succ n =>
      cases hx : x ⟨0, Nat.zero_lt_succ n⟩ <;>
        simp [UniformTM.run, UniformTM.stepConfig, UniformTM.step, initialConfig,
          firstBitMachine, firstBit]
      all_goals split <;> rfl

private theorem firstBit_run_succ_state {n budget steps : Nat} (x : Bitstring n) :
    (firstBitMachine.run (steps + 1)
      (initialConfig firstBitMachine budget x)).state =
        if firstBit n x then firstBitMachine.accept else firstBitMachine.reject := by
  rw [Nat.add_comm, firstBitMachine.run_add]
  cases hbit : firstBit n x with
  | false =>
      have hreject :
          (firstBitMachine.run 1
            (initialConfig firstBitMachine budget x)).state =
              firstBitMachine.reject := by
        simpa [hbit] using firstBit_run_one_state (budget := budget) x
      rw [firstBitMachine.run_reject _ hreject steps]
      exact hreject
  | true =>
      have haccept :
          (firstBitMachine.run 1
            (initialConfig firstBitMachine budget x)).state =
              firstBitMachine.accept := by
        simpa [hbit] using firstBit_run_one_state (budget := budget) x
      rw [firstBitMachine.run_accept _ haccept steps]
      exact haccept

/-- After any positive exact time, first-bit acceptance is precisely a true
first bit. -/
theorem firstBit_acceptsAt_iff {n budget steps : Nat} (x : Bitstring n)
    (hsteps : 1 ≤ steps) :
    AcceptsAt firstBitMachine budget steps x ↔ firstBit n x = true := by
  cases steps with
  | zero => simp at hsteps
  | succ steps =>
      change
        (firstBitMachine.run (steps + 1)
          (initialConfig firstBitMachine budget x)).state =
            firstBitMachine.accept ↔ firstBit n x = true
      rw [firstBit_run_succ_state]
      cases hbit : firstBit n x <;> simp [firstBitMachine]

/-- After any positive exact time, first-bit rejection is precisely a false
first bit (including empty input). -/
theorem firstBit_rejectsAt_iff {n budget steps : Nat} (x : Bitstring n)
    (hsteps : 1 ≤ steps) :
    RejectsAt firstBitMachine budget steps x ↔ firstBit n x = false := by
  cases steps with
  | zero => simp at hsteps
  | succ steps =>
      change
        (firstBitMachine.run (steps + 1)
          (initialConfig firstBitMachine budget x)).state =
            firstBitMachine.reject ↔ firstBit n x = false
      rw [firstBit_run_succ_state]
      cases hbit : firstBit n x <;> simp [firstBitMachine]

/-- With a positive budget, within-budget acceptance is precisely a true first
bit. -/
theorem firstBit_acceptsWithin_iff {n budget : Nat} (x : Bitstring n)
    (hbudget : 1 ≤ budget) :
    AcceptsWithin firstBitMachine budget x ↔ firstBit n x = true := by
  rw [← acceptsAt_budget_iff_acceptsWithin]
  exact firstBit_acceptsAt_iff x hbudget

/-- With a positive budget, within-budget rejection is precisely a false first
bit. -/
theorem firstBit_rejectsWithin_iff {n budget : Nat} (x : Bitstring n)
    (hbudget : 1 ≤ budget) :
    RejectsWithin firstBitMachine budget x ↔ firstBit n x = false := by
  rw [← rejectsAt_budget_iff_rejectsWithin]
  exact firstBit_rejectsAt_iff x hbudget

/-- At any positive exact time the first-bit literal decides `firstBit`. -/
theorem firstBit_decidesAt {n budget steps : Nat} (x : Bitstring n)
    (hsteps : 1 ≤ steps) :
    DecidesAt firstBitMachine budget steps x (firstBit n x) := by
  cases hbit : firstBit n x with
  | false =>
      simp [DecidesAt, (firstBit_rejectsAt_iff x hsteps).2 hbit]
  | true =>
      simp [DecidesAt, (firstBit_acceptsAt_iff x hsteps).2 hbit]

/-- With at least one available step, the first-bit literal decides within the
budget. -/
theorem firstBit_decidesWithin {n budget : Nat} (x : Bitstring n)
    (hbudget : 1 ≤ budget) :
    DecidesWithin firstBitMachine budget x (firstBit n x) := by
  cases hbit : firstBit n x with
  | false =>
      exact ⟨1, hbudget, (firstBit_rejectsAt_iff x (Nat.le_refl 1)).2 hbit⟩
  | true =>
      exact ⟨1, hbudget, (firstBit_acceptsAt_iff x (Nat.le_refl 1)).2 hbit⟩

/-- Concrete true-verdict execution. -/
theorem firstBit_true_verdict :
    DecidesWithin firstBitMachine 1 (fun _ : Fin 1 => true) true := by
  simpa [firstBit] using
    firstBit_decidesWithin (budget := 1) (fun _ : Fin 1 => true) (Nat.le_refl 1)

/-- Concrete false verdict on empty input, read from false padding. -/
theorem firstBit_false_verdict :
    DecidesWithin firstBitMachine 1 (fun _ : Fin 0 => true) false := by
  simpa [firstBit] using
    firstBit_decidesWithin (budget := 1) (fun _ : Fin 0 => true) (Nat.le_refl 1)

/-- A three-state literal that stays forever in a nonterminal start state. -/
def nonterminalMachine : UniformTM :=
  UniformTM.mk
    3
    (⟨0, by decide⟩)
    (⟨1, by decide⟩)
    (⟨2, by decide⟩)
    (by decide)
    (fun _ b => (⟨0, by decide⟩, b, Move.stay))

private theorem example_config_eq {k n budget : Nat} {c d : Config k n budget}
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

private theorem nonterminal_step_initial {n budget : Nat} (x : Bitstring n) :
    nonterminalMachine.stepConfig (initialConfig nonterminalMachine budget x) =
      initialConfig nonterminalMachine budget x := by
  apply example_config_eq
  · simp [UniformTM.stepConfig, UniformTM.step, initialConfig, nonterminalMachine]
  · simp [UniformTM.stepConfig, UniformTM.step, initialConfig, nonterminalMachine,
      moveHead]
  · funext i
    by_cases hi : i = (initialConfig nonterminalMachine budget x).head
    · subst i
      simp [UniformTM.stepConfig, UniformTM.step, initialConfig, nonterminalMachine]
    · simp [initialConfig] at hi
      simp [UniformTM.stepConfig, UniformTM.step, initialConfig, nonterminalMachine, hi]

private theorem nonterminal_run_initial {n budget steps : Nat} (x : Bitstring n) :
    nonterminalMachine.run steps (initialConfig nonterminalMachine budget x) =
      initialConfig nonterminalMachine budget x := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [UniformTM.run, ih, nonterminal_step_initial]

/-- Every exact run of the nonterminal literal remains in its start state. -/
theorem nonterminal_run_state {n budget : Nat} (x : Bitstring n) (steps : Nat) :
    (nonterminalMachine.run steps
      (initialConfig nonterminalMachine budget x)).state = nonterminalMachine.start := by
  rw [nonterminal_run_initial]
  rfl

/-- The deadline state's executable acceptance flag is false. -/
theorem nonterminal_acceptFlag_false {n budget : Nat} (x : Bitstring n) :
    ((nonterminalMachine.run budget
      (initialConfig nonterminalMachine budget x)).state ==
        nonterminalMachine.accept) = false := by
  rw [nonterminal_run_state]
  decide

/-- Despite its false acceptance flag, the nonterminal literal never
literally rejects within the budget. -/
theorem nonterminal_not_rejectsWithin {n budget : Nat} (x : Bitstring n) :
    ¬ RejectsWithin nonterminalMachine budget x := by
  rintro ⟨steps, _hsteps, hreject⟩
  change
    (nonterminalMachine.run steps
      (initialConfig nonterminalMachine budget x)).state =
        nonterminalMachine.reject at hreject
  rw [nonterminal_run_state] at hreject
  exact (by decide : nonterminalMachine.start ≠ nonterminalMachine.reject) hreject

/-- In particular, timeout/nontermination is not a false decision. -/
theorem nonterminal_not_decidesWithin_false {n budget : Nat} (x : Bitstring n) :
    ¬ DecidesWithin nonterminalMachine budget x false := by
  simpa [DecidesWithin] using nonterminal_not_rejectsWithin x

/-- Combined negative control: an executable false acceptance flag does not
turn timeout into rejection or a false decision. -/
theorem nonterminal_timeout_counterexample {n budget : Nat} (x : Bitstring n) :
    ((nonterminalMachine.run budget
        (initialConfig nonterminalMachine budget x)).state ==
          nonterminalMachine.accept) = false ∧
      ¬ RejectsWithin nonterminalMachine budget x ∧
      ¬ DecidesWithin nonterminalMachine budget x false :=
  ⟨nonterminal_acceptFlag_false x,
    nonterminal_not_rejectsWithin x,
    nonterminal_not_decidesWithin_false x⟩

/-- The constant-true language is in the versioned `UniformP`. -/
theorem uniformP_constTrue : UniformP constTrue := by
  refine ⟨allAcceptMachine, 0, ?_⟩
  intro n x
  simpa [constTrue, DecidesWithin] using
    (allAccept_acceptsWithin (budget := polyClock 0 n) x)

/-- The constant-false language is in the versioned `UniformP`. -/
theorem uniformP_constFalse : UniformP constFalse := by
  refine ⟨allRejectMachine, 0, ?_⟩
  intro n x
  simpa [constFalse, DecidesWithin] using
    (allReject_rejectsWithin (budget := polyClock 0 n) x)

/-- The first-bit language (empty input false) is in the versioned `UniformP`. -/
theorem uniformP_firstBit : UniformP firstBit := by
  refine ⟨firstBitMachine, 1, ?_⟩
  intro n x
  exact firstBit_decidesWithin x (polyClock_pos 1 n)

end Pnp3.Complexity.Uniform.V1
