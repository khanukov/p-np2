import Attempt.Equality
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter

namespace Research.SolverToDag
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion

/-- The fixed concrete promise problem; no generic codec parameter. -/
def concreteProblem (k : Nat) : SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem (thresholdPoly k)
    (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))

def witnessWidth (k n : Nat) : Nat :=
  (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n

theorem witnessWidth_exact (k n : Nat) :
    witnessWidth k n = (bitLength n + 4) * (n ^ k + k) := rfl

def solverBudget (d n : Nat) : Nat := Pnp3.Models.Partial.tableLen n ^ d + d

abbrev ConcreteSolver (k d : Nat) :=
  BoundedSearchSolver (concreteProblem k) C_DAG (solverBudget d)

/-- Copy EACH solver bit's real gate graph once into a shared output bundle. -/
def witnessBundle {k d : Nat} (S : ConcreteSolver k d) (n : Nat) :
    DagBundle (Pnp3.Models.Partial.tableLen n) (witnessWidth k n) :=
  bundleOfFamily (witnessWidth k n) (S.outputCircuit n)

theorem witnessBundle_eval {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (i : Fin (witnessWidth k n)) (tt : Bitstring (Pnp3.Models.Partial.tableLen n)) :
    (witnessBundle S n).evalOutput i tt = searchSolverOutput (S.outputCircuit n) tt i := by
  simp [witnessBundle, searchSolverOutput, C_DAG]

theorem witnessBundle_gates_le {k d : Nat} (S : ConcreteSolver k d) (n : Nat) :
    (witnessBundle S n).gates ≤ witnessWidth k n * solverBudget d n := by
  rw [witnessBundle, bundleOfFamily_gates]
  calc
    ∑ i, (S.outputCircuit n i).gates ≤ ∑ _i : Fin (witnessWidth k n), solverBudget d n := by
      apply Finset.sum_le_sum
      intro i _
      have h := S.size_le n i
      change (S.outputCircuit n i).gates + 1 ≤ solverBudget d n at h
      omega
    _ = witnessWidth k n * solverBudget d n := by simp

/-- Compose an ACTUAL supplied head graph with inputs and solver witness bits.
No claim that this head is a codec verifier, and no verifier field, is added. -/
def plugSolver {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n)) :
    DagCircuit (Pnp3.Models.Partial.tableLen n) :=
  substInputsWithBundle head (passthroughBundle (witnessBundle S n))

theorem plugSolver_eval {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n))
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)) :
    eval (plugSolver S n head) tt =
      eval head (Fin.addCases tt (searchSolverOutput (S.outputCircuit n) tt)) := by
  rw [plugSolver, eval_substInputsWithBundle]
  congr 1
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp
  · intro i
    simp [witnessBundle_eval]

theorem plugSolver_size_le {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n)) :
    size (plugSolver S n head) ≤ size head + witnessWidth k n * solverBudget d n := by
  have h := witnessBundle_gates_le S n
  change (witnessBundle S n).gates + head.gates + 1 ≤
    head.gates + 1 + witnessWidth k n * solverBudget d n
  omega

/-- Exact component semantics AND accounting; this is NOT the full MCSP capstone. -/
theorem plugSolver_capstone {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n))
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)) :
    eval (plugSolver S n head) tt =
      eval head (Fin.addCases tt (searchSolverOutput (S.outputCircuit n) tt)) ∧
    size (plugSolver S n head) ≤ size head +
      ((bitLength n + 4) * (n ^ k + k)) * (Pnp3.Models.Partial.tableLen n ^ d + d) := by
  exact ⟨plugSolver_eval S n head tt,
    by simpa [witnessWidth_exact, solverBudget] using plugSolver_size_le S n head⟩

/-- Closed polynomial price of ALL solver output graphs plus one output.
The exponent depends on k,d only and works for every n and every solver. -/
theorem solverWiring_polynomial (k d : Nat) :
    ∃ e : Nat, ∀ (S : ConcreteSolver k d) (n : Nat),
      (witnessBundle S n).gates + 1 ≤ Pnp3.Models.Partial.tableLen n ^ e + e := by
  have hw : PolyBoundedInTable (witnessWidth k) :=
    polyBoundedInTable_treeWitnessBits_of_thresholdPoly _ (polyBoundedInTable_thresholdPoly k)
  have hb : PolyBoundedInTable (solverBudget d) :=
    (PolyBoundedInTable.tableLen_pow d).add (PolyBoundedInTable.const d)
  obtain ⟨e, he⟩ := ((hw.mul hb).add (PolyBoundedInTable.const 1)).powAdd
  exact ⟨e, fun S n => le_trans (Nat.add_le_add_right (witnessBundle_gates_le S n) 1) (he n)⟩

end Research.SolverToDag
