import Attempt.Lengthwise

namespace Research.LengthwiseSearch.Examples

open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier

/-- Copy the input bit. There is exactly one valid witness per input. -/
def identityProblem : SearchMCSPCompressionProblem where
  instanceBits := fun _ => 1
  witnessBits := fun _ => 1
  promise := fun _ _ => True
  relation := fun _ x w => w 0 = x 0
  totalOnPromise := fun _ x _ => ⟨x, rfl⟩

/-- The restricted model has only the two constant circuits. -/
def constantClass : CircuitFamilyClass where
  Family := fun _ => Bool
  eval := fun b _ => b
  size := fun _ => 1

/-- A genuine lower bound: no constant circuit copies an arbitrary input bit. -/
theorem identity_constant_lower_bound (n : Nat) :
    LowerBoundAt identityProblem constantClass n 1 := by
  intro outputCircuit _
  refine ⟨fun _ => !(outputCircuit (0 : Fin 1)), trivial, ?_⟩
  change ¬ (outputCircuit (0 : Fin 1) = !(outputCircuit (0 : Fin 1)))
  cases outputCircuit (0 : Fin 1) <;> simp

/-- The bad input must depend on the selected circuit tuple. -/
theorem no_common_bad_input (n : Nat) :
    ¬ ∃ x : Pnp4.AlgorithmsToLowerBounds.BitVec 1,
      ∀ outputCircuit : Fin 1 → Bool,
        (∀ i, constantClass.size (n := 1) (outputCircuit i) ≤ 1) →
        ¬ identityProblem.relation n x
          (searchSolverOutput (problem := identityProblem) (C := constantClass)
            (n := n) outputCircuit x) := by
  rintro ⟨x, h⟩
  exact h (fun _ => x 0) (fun _ => Nat.le_refl 1) rfl

inductive OneBitCircuit (m : Nat) where
  | constant : Bool → OneBitCircuit m
  | input : Fin m → OneBitCircuit m

def projectionClass : CircuitFamilyClass where
  Family := OneBitCircuit
  eval := fun c x => match c with
    | .constant b => b
    | .input i => x i
  size := fun _ => 1

/-- A positive solver fixture for the same substantive relation. -/
def identity_solver (n : Nat) : SolverAt identityProblem projectionClass n 1 where
  outputCircuit := fun _ => .input (0 : Fin 1)
  size_le := fun _ => Nat.le_refl 1
  solves := fun _ _ => rfl

theorem identity_projection_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt identityProblem projectionClass n 1 := by
  intro h
  exact (lowerBoundAt_iff_no_solver _ _ _ _).mp h ⟨identity_solver n⟩

def emptyCircuitClass : CircuitFamilyClass where
  Family := fun _ => Empty
  eval := fun c => nomatch c
  size := fun c => nomatch c

def zeroWidthProblem : SearchMCSPCompressionProblem where
  instanceBits := fun _ => 1
  witnessBits := fun _ => 0
  promise := fun _ _ => True
  relation := fun _ _ _ => True
  totalOnPromise := fun _ _ _ => ⟨Fin.elim0, trivial⟩

/-- Empty output vectors work even when no individual circuits exist. -/
def zero_width_solver (n : Nat) : SolverAt zeroWidthProblem emptyCircuitClass n 0 where
  outputCircuit := Fin.elim0
  size_le := fun i => Fin.elim0 i
  solves := fun _ _ => trivial

theorem zero_width_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt zeroWidthProblem emptyCircuitClass n 0 := by
  intro h
  exact (lowerBoundAt_iff_no_solver _ _ _ _).mp h ⟨zero_width_solver n⟩

/-- The generic formulation honestly retains vacuity when no tuple fits. -/
theorem zero_budget_vacuous_obstruction (n : Nat) :
    LowerBoundAt identityProblem constantClass n 0 := by
  intro outputCircuit hsize
  have h := hsize (0 : Fin 1)
  change 1 ≤ 0 at h
  omega

/-- An empty promise does not force a lower bound when a bounded tuple exists. -/
def emptyPromiseProblem : SearchMCSPCompressionProblem where
  instanceBits := fun _ => 0
  witnessBits := fun _ => 1
  promise := fun _ _ => False
  relation := fun _ _ _ => False
  totalOnPromise := fun _ _ h => False.elim h

def empty_promise_solver (n : Nat) : SolverAt emptyPromiseProblem constantClass n 1 where
  outputCircuit := fun _ => false
  size_le := fun _ => Nat.le_refl 1
  solves := fun _ h => False.elim h

theorem empty_promise_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt emptyPromiseProblem constantClass n 1 := by
  intro h
  exact (lowerBoundAt_iff_no_solver _ _ _ _).mp h ⟨empty_promise_solver n⟩

end Research.LengthwiseSearch.Examples
