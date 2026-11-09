import Complexity.DagCompose

namespace Research.IdeaLeanPilot
open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-- A useful budgeted existence statement; includes zero input width. -/
def BudgetWitness : Prop :=
  ∀ n budget : Nat, 2 ≤ budget →
    ∃ c : DagCircuit n, size c ≤ budget ∧ ∀ x, eval c x = true

/-- Deliberately false strengthening: every bounded circuit accepts. -/
def AllBoundedAccept : Prop :=
  ∀ n budget : Nat, 2 ≤ budget →
    ∀ c : DagCircuit n, size c ≤ budget → ∀ x, eval c x = true

theorem budget_witness :
    ∀ n budget : Nat, 2 ≤ budget →
      ∃ c : DagCircuit n, size c ≤ budget ∧ ∀ x, eval c x = true := by
  intro n budget h
  exact ⟨constCircuit n true, by simpa using h, fun x => eval_constCircuit true x⟩

theorem not_all_bounded_accept :
    ¬ (∀ n budget : Nat, 2 ≤ budget →
      ∀ c : DagCircuit n, size c ≤ budget → ∀ x, eval c x = true) := by
  intro h
  have bad := h 0 2 (by decide) (constCircuit 0 false) (by simp) (fun i => Fin.elim0 i)
  simp at bad

theorem check_budget_witness :
    ∀ n budget : Nat, 2 ≤ budget →
      ∃ c : DagCircuit n, size c ≤ budget ∧ ∀ x, eval c x = true := budget_witness

theorem check_not_all_bounded_accept :
    ¬ (∀ n budget : Nat, 2 ≤ budget →
      ∀ c : DagCircuit n, size c ≤ budget → ∀ x, eval c x = true) := not_all_bounded_accept

#check (BudgetWitness : Prop)
#check (AllBoundedAccept : Prop)
#print axioms BudgetWitness
#print axioms AllBoundedAccept
#print axioms budget_witness
#print axioms not_all_bounded_accept
#print axioms check_budget_witness
#print axioms check_not_all_bounded_accept
end Research.IdeaLeanPilot
