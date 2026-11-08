import Attempt.Fixtures

namespace Research.SolverToDag
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds

/- Full propositions and type/arity signatures elaborated again. These are checks
of the exposed propositions/types, not independent proofs or peer review. -/
def type_bitMismatch : DagCircuit 2 := @bitMismatch

theorem check_eval_bitMismatch : ∀ (x : Bitstring 2),
  eval bitMismatch x = !(x 0 == x 1) := @eval_bitMismatch

theorem check_bitMismatch_size : size bitMismatch = 6 := @bitMismatch_size

def type_pairMismatch : ∀ {m : Nat} (_a _b : Fin m),
  DagCircuit m := @pairMismatch

theorem check_eval_pairMismatch : ∀ {m : Nat} (a b : Fin m) (x : Bitstring m),
  eval (pairMismatch a b) x = !(x a == x b) := @eval_pairMismatch

theorem check_pairMismatch_gates : ∀ {m : Nat} (a b : Fin m),
  (pairMismatch a b).gates = 5 := @pairMismatch_gates

theorem check_pairMismatch_size : ∀ {m : Nat} (a b : Fin m),
  size (pairMismatch a b) = 6 := @pairMismatch_size

def type_vectorEquality : ∀ (w : Nat),
  DagCircuit (w + w) := @vectorEquality

theorem check_vectorEquality_iff : ∀ (w : Nat) (x : Bitstring (w + w)),
  eval (vectorEquality w) x = true ↔
      ∀ i : Fin w, x (Fin.castAdd w i) = x (Fin.natAdd w i) := @vectorEquality_iff

theorem check_vectorEquality_size : ∀ (w : Nat),
  size (vectorEquality w) = 6 * w + 3 := @vectorEquality_size

def type_tableEquality : ∀ (n : Nat),
  DagCircuit (Pnp3.Models.Partial.tableLen n + Pnp3.Models.Partial.tableLen n) := @tableEquality

theorem check_tableEquality_capstone : ∀ (n : Nat)
    (tt predicted : Pnp4.AlgorithmsToLowerBounds.TruthTable n),
  (eval (tableEquality n) (Fin.addCases tt predicted) = true ↔ tt = predicted) ∧
      size (tableEquality n) = 6 * Pnp3.Models.Partial.tableLen n + 3 := @tableEquality_capstone

def type_concreteProblem : ∀ (_k : Nat),
  SearchMCSPCompressionProblem := @concreteProblem

def type_witnessWidth : ∀ (_k _n : Nat),
  Nat := @witnessWidth

theorem check_witnessWidth_exact : ∀ (k n : Nat),
  witnessWidth k n = (bitLength n + 4) * (n ^ k + k) := @witnessWidth_exact

def type_solverBudget : ∀ (_d _n : Nat),
  Nat := @solverBudget

def type_ConcreteSolver : ∀ (_k _d : Nat),
  Type := @ConcreteSolver

def type_witnessBundle : ∀ {k d : Nat} (_S : ConcreteSolver k d) (n : Nat),
  DagBundle (Pnp3.Models.Partial.tableLen n) (witnessWidth k n) := @witnessBundle

theorem check_witnessBundle_eval : ∀ {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (i : Fin (witnessWidth k n)) (tt : Bitstring (Pnp3.Models.Partial.tableLen n)),
  (witnessBundle S n).evalOutput i tt = searchSolverOutput (S.outputCircuit n) tt i := @witnessBundle_eval

theorem check_witnessBundle_gates_le : ∀ {k d : Nat} (S : ConcreteSolver k d) (n : Nat),
  (witnessBundle S n).gates ≤ witnessWidth k n * solverBudget d n := @witnessBundle_gates_le

def type_plugSolver : ∀ {k d : Nat} (_S : ConcreteSolver k d) (n : Nat)
    (_head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n)),
  DagCircuit (Pnp3.Models.Partial.tableLen n) := @plugSolver

theorem check_plugSolver_eval : ∀ {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n))
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)),
  eval (plugSolver S n head) tt =
      eval head (Fin.addCases tt (searchSolverOutput (S.outputCircuit n) tt)) := @plugSolver_eval

theorem check_plugSolver_size_le : ∀ {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n)),
  size (plugSolver S n head) ≤ size head + witnessWidth k n * solverBudget d n := @plugSolver_size_le

theorem check_plugSolver_capstone : ∀ {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (head : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n))
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)),
  eval (plugSolver S n head) tt =
      eval head (Fin.addCases tt (searchSolverOutput (S.outputCircuit n) tt)) ∧
    size (plugSolver S n head) ≤ size head +
      ((bitLength n + 4) * (n ^ k + k)) * (Pnp3.Models.Partial.tableLen n ^ d + d) := @plugSolver_capstone

theorem check_solverWiring_polynomial : ∀ (k d : Nat),
  ∃ e : Nat, ∀ (S : ConcreteSolver k d) (n : Nat),
      (witnessBundle S n).gates + 1 ≤ Pnp3.Models.Partial.tableLen n ^ e + e := @solverWiring_polynomial

def type_treeTable : ∀ {n : Nat} (_c : Pnp3.Models.Circuit n),
  TruthTable n := @treeTable

theorem check_computes_iff_table : ∀ {n : Nat} (c : Pnp3.Models.Circuit n) (tt : TruthTable n),
  ComputesTruthTable treeCircuitClass c tt ↔ tt = treeTable c := @computes_iff_table

def type_matchesTable : ∀ {n : Nat} (_t : TruthTable n),
  DagCircuit (Pnp3.Models.Partial.tableLen n) := @matchesTable

theorem check_matchesTable_iff : ∀ {n : Nat} (t tt : TruthTable n),
  eval (matchesTable t) tt = true ↔ tt = t := @matchesTable_iff

theorem check_matchesTable_size : ∀ {n : Nat} (t : TruthTable n),
  size (matchesTable t) = 7 * Pnp3.Models.Partial.tableLen n + 3 := @matchesTable_size

def type_leaves : ∀ (n : Nat),
  List (Pnp3.Models.Circuit n) := @leaves

theorem check_tree_size_pos : ∀ {n : Nat} (c : Pnp3.Models.Circuit n),
  1 ≤ c.size := @tree_size_pos

theorem check_leaves_characterize : ∀ {n : Nat} (c : Pnp3.Models.Circuit n),
  c ∈ leaves n ↔ c.size ≤ 1 := @leaves_characterize

def type_leafRecognizer : ∀ (n : Nat),
  DagCircuit (Pnp3.Models.Partial.tableLen n) := @leafRecognizer

theorem check_leafRecognizer_iff : ∀ (n : Nat) (tt : TruthTable n),
  eval (leafRecognizer n) tt = true ↔ treeMCSPPredicate n 1 tt := @leafRecognizer_iff

theorem check_leafRecognizer_size : ∀ (n : Nat),
  size (leafRecognizer n) =
      2 + (n + 2) * (7 * Pnp3.Models.Partial.tableLen n + 3) := @leafRecognizer_size

theorem check_leafRecognizer_capstone : ∀ (n : Nat) (tt : TruthTable n),
  (eval (leafRecognizer n) tt = true ↔ treeMCSPPredicate n (thresholdPoly 0 n) tt) ∧
    size (leafRecognizer n) =
      2 + (n + 2) * (7 * Pnp3.Models.Partial.tableLen n + 3) := @leafRecognizer_capstone

theorem check_leafRecognizer_polynomial : ∃ e : Nat, ∀ n : Nat,
      size (leafRecognizer n) ≤ Pnp3.Models.Partial.tableLen n ^ e + e := @leafRecognizer_polynomial

def type_projectionTable : TruthTable 1 := @projectionTable

def type_negationTable : TruthTable 1 := @negationTable

def type_malformedBits : Bitstring (witnessWidth 0 0) := @malformedBits

theorem check_zero_width_equality : eval (vectorEquality 0) (fun i => Fin.elim0 i) = true := @zero_width_equality

theorem check_zero_width_size : size (vectorEquality 0) = 3 := @zero_width_size

theorem check_zero_variable_false : eval (leafRecognizer 0) (fun _ => false) = true := @zero_variable_false

theorem check_zero_variable_true : eval (leafRecognizer 0) (fun _ => true) = true := @zero_variable_true

theorem check_projection_yes : eval (leafRecognizer 1) projectionTable = true := @projection_yes

theorem check_negation_not_size_one : ¬ treeMCSPPredicate 1 1 negationTable := @negation_not_size_one

theorem check_negation_no : eval (leafRecognizer 1) negationTable = false := @negation_no

theorem check_malformed_decode : ((treeCircuitWitnessCodec (thresholdPoly 0)).decode 0 malformedBits).isNone = true := @malformed_decode

theorem check_malformed_not_verifies : ∀ (tt : TruthTable 0),
  ¬ (treeCircuitWitnessCodec (thresholdPoly 0)).verifies 0 tt malformedBits := @malformed_not_verifies

end Research.SolverToDag
