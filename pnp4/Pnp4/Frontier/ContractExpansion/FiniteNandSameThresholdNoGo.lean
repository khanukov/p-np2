import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Finite NAND obstruction to same-threshold DAG-to-tree transfer

This side-track/no-go module gives a concrete two-input counterexample to
transferring a DAG circuit to a tree circuit at the *same numeric threshold
under the repository's two different size functions*.  A two-gate DAG (size
three under `DagCircuit.size`) computes NAND, while the corresponding tree has
size four because `Models.Circuit.size` also counts its two input leaves.

The witness uses no shared subcomputation: this is a cross-model
metric-normalization obstruction, not an unfolding/fanout lower bound.  It only
rejects transfer at the same numeric threshold under these unaligned metrics;
it does not survive aligned gate-count conventions, rule out DAG-to-tree
simulation with an adjusted threshold, establish an asymptotic separation, or
discharge any P-vs-NP source obligation.
-/

namespace Pnp4.Frontier.ContractExpansion.FiniteNand

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp4.AlgorithmsToLowerBounds

def nandFn (assignment : Core.BitVec 2) : Bool :=
  !(assignment 0 && assignment 1)

def nandTable : TruthTable 2 :=
  fun index => nandFn (Core.vecOfNat 2 index.val)

def nandDag : DagCircuit 2 where
  gates := 2
  gate index :=
    if hzero : index.val = 0 then
      .and (.input 0) (.input 1)
    else
      .not (.gate ⟨0, by omega⟩)
  output := .gate ⟨1, by omega⟩

def explicitDagClass : CircuitFamilyClass where
  Family := DagCircuit
  eval := fun {_} circuit assignment =>
    DagCircuit.eval circuit (fun index => assignment index)
  size := fun {_} circuit => DagCircuit.size circuit

def nandTree : Models.Circuit 2 :=
  .not (.and (.input 0) (.input 1))

private theorem threshold_at_one_two :
    thresholdPoly 1 2 = 3 := by
  rfl

private theorem nand_dag_gates : nandDag.gates = 2 := rfl

private theorem nand_dag_gate_zero :
    nandDag.gate ⟨0, by decide⟩ =
      .and (.input 0) (.input 1) := by
  simp [nandDag]

private theorem nand_dag_gate_one :
    nandDag.gate ⟨1, by decide⟩ =
      .not (.gate ⟨0, by decide⟩) := by
  simp [nandDag]

private theorem nand_dag_size :
    DagCircuit.size nandDag = 3 := by
  rfl

private theorem nand_dag_eval (assignment : Bitstring 2) :
    DagCircuit.eval nandDag assignment =
      !(assignment 0 && assignment 1) := by
  simp [nandDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

private theorem nand_tree_size :
    Models.Circuit.size nandTree = 4 := by
  rfl

private theorem nand_tree_eval (assignment : Core.BitVec 2) :
    Models.Circuit.eval nandTree assignment = nandFn assignment := by
  rfl

private theorem nand_table_decode (assignment : Core.BitVec 2) :
    Models.truthTableFunction nandTable assignment = nandFn assignment := by
  change nandFn (Core.vecOfNat 2 (Models.assignmentIndex assignment).val) =
    nandFn assignment
  rw [Models.vecOfNat_assignmentIndex_val]

private theorem nand_dag_computes :
    ComputesTruthTable explicitDagClass nandDag nandTable := by
  intro assignment
  change DagCircuit.eval nandDag (fun index => assignment index) =
    Models.truthTableFunction nandTable assignment
  rw [nand_dag_eval, nand_table_decode]
  rfl

private theorem nand_tree_computes :
    Models.circuitComputes nandTree nandTable := by
  intro assignment
  rw [nand_tree_eval, nand_table_decode]

private theorem tree_size_positive {arity : Nat}
    (circuit : Models.Circuit arity) :
    1 ≤ Models.Circuit.size circuit := by
  cases circuit <;> simp only [Models.Circuit.size] <;> omega

private theorem one_node_cases {arity : Nat}
    (circuit : Models.Circuit arity)
    (hsize : Models.Circuit.size circuit ≤ 1) :
    (∃ index : Fin arity, circuit = Models.Circuit.input index) ∨
      (∃ value : Bool, circuit = Models.Circuit.const value) := by
  cases circuit with
  | input index =>
      exact Or.inl ⟨index, rfl⟩
  | const value =>
      exact Or.inr ⟨value, rfl⟩
  | not child =>
      have hpositive := tree_size_positive child
      simp only [Models.Circuit.size] at hsize
      omega
  | and left right =>
      have hleft := tree_size_positive left
      have hright := tree_size_positive right
      simp only [Models.Circuit.size] at hsize
      omega
  | or left right =>
      have hleft := tree_size_positive left
      have hright := tree_size_positive right
      simp only [Models.Circuit.size] at hsize
      omega

private def allFalse : Core.BitVec 2 :=
  fun _ => false

private def allTrue : Core.BitVec 2 :=
  fun _ => true

private def firstOnly : Core.BitVec 2 :=
  fun index => if index.val = 0 then true else false

private def secondOnly : Core.BitVec 2 :=
  fun index => if index.val = 0 then false else true

private theorem no_small_tree_nand_function
    (circuit : Models.Circuit 2)
    (hsize : Models.Circuit.size circuit ≤ 3) :
    ¬ (∀ assignment : Core.BitVec 2,
      Models.Circuit.eval circuit assignment = nandFn assignment) := by
  intro hcomputes
  have hzero := hcomputes allFalse
  have hone := hcomputes allTrue
  have hfirst := hcomputes firstOnly
  have hsecond := hcomputes secondOnly
  cases circuit with
  | input index =>
      simp [Models.Circuit.eval, nandFn, allTrue] at hone
  | const value =>
      cases value <;>
        simp_all [Models.Circuit.eval, nandFn, allFalse, allTrue]
  | not child =>
      have hchild : Models.Circuit.size child ≤ 2 := by
        simp only [Models.Circuit.size] at hsize
        omega
      cases child with
      | input index =>
          fin_cases index <;>
            simp_all [Models.Circuit.eval, nandFn, firstOnly, secondOnly]
      | const value =>
          cases value <;>
            simp_all [Models.Circuit.eval, nandFn, allFalse, allTrue]
      | not grandchild =>
          have hgrandchild : Models.Circuit.size grandchild ≤ 1 := by
            simp only [Models.Circuit.size] at hchild
            omega
          rcases one_node_cases grandchild hgrandchild with
            ⟨index, rfl⟩ | ⟨value, rfl⟩
          · simp [Models.Circuit.eval, nandFn, allTrue] at hone
          · cases value <;>
              simp_all [Models.Circuit.eval, nandFn, allFalse, allTrue]
      | and left right =>
          have hleft := tree_size_positive left
          have hright := tree_size_positive right
          simp only [Models.Circuit.size] at hchild
          omega
      | or left right =>
          have hleft := tree_size_positive left
          have hright := tree_size_positive right
          simp only [Models.Circuit.size] at hchild
          omega
  | and left right =>
      have hleftPositive := tree_size_positive left
      have hrightPositive := tree_size_positive right
      have hchildren :
          Models.Circuit.size left ≤ 1 ∧
            Models.Circuit.size right ≤ 1 := by
        simp only [Models.Circuit.size] at hsize
        omega
      rcases one_node_cases left hchildren.1 with
        ⟨leftIndex, rfl⟩ | ⟨leftValue, rfl⟩ <;>
        rcases one_node_cases right hchildren.2 with
          ⟨rightIndex, rfl⟩ | ⟨rightValue, rfl⟩ <;>
          simp_all [Models.Circuit.eval, nandFn, allFalse, allTrue]
  | or left right =>
      have hleftPositive := tree_size_positive left
      have hrightPositive := tree_size_positive right
      have hchildren :
          Models.Circuit.size left ≤ 1 ∧
            Models.Circuit.size right ≤ 1 := by
        simp only [Models.Circuit.size] at hsize
        omega
      rcases one_node_cases left hchildren.1 with
        ⟨leftIndex, rfl⟩ | ⟨leftValue, rfl⟩ <;>
        rcases one_node_cases right hchildren.2 with
          ⟨rightIndex, rfl⟩ | ⟨rightValue, rfl⟩ <;>
          simp_all [Models.Circuit.eval, nandFn, allFalse, allTrue]

private theorem no_small_tree_nand_table :
    ¬ ∃ circuit : Models.Circuit 2,
      Models.Circuit.size circuit ≤ 3 ∧
        Models.circuitComputes circuit nandTable := by
  rintro ⟨circuit, hsize, hcomputes⟩
  apply no_small_tree_nand_function circuit hsize
  intro assignment
  exact (hcomputes assignment).trans (nand_table_decode assignment)

private theorem nand_tree_at_four :
    treeMCSPPredicate 2 4 nandTable := by
  refine ⟨nandTree, Nat.le_of_eq nand_tree_size, ?_⟩
  exact nand_tree_computes

/-- NAND is computable by the explicit DAG class at `thresholdPoly 1 2 = 3`,
but not by any tree circuit at that same threshold. -/
theorem nand_same_threshold_mismatch :
    circuitComplexityLE explicitDagClass 2 (thresholdPoly 1 2) nandTable ∧
      ¬ treeMCSPPredicate 2 (thresholdPoly 1 2) nandTable := by
  rw [threshold_at_one_two]
  constructor
  · refine ⟨nandDag, ?_, nand_dag_computes⟩
    change 3 ≤ 3
    exact Nat.le_refl 3
  · change ¬ ∃ circuit : Models.Circuit 2,
      Models.Circuit.size circuit ≤ 3 ∧
        Models.circuitComputes circuit nandTable
    exact no_small_tree_nand_table

/-- There is no universal implication from the explicit DAG predicate to the
tree-MCSP predicate when both use the same threshold `thresholdPoly 1 2`. -/
theorem same_threshold_promise_transfer_false :
    ¬ (∀ table : TruthTable 2,
      circuitComplexityLE explicitDagClass 2 (thresholdPoly 1 2) table →
        treeMCSPPredicate 2 (thresholdPoly 1 2) table) := by
  intro htransfer
  exact nand_same_threshold_mismatch.2
    (htransfer nandTable nand_same_threshold_mismatch.1)

/-- Under the repository's unaligned DAG/tree size functions, there is no
universal conversion at the same numeric threshold from two-input DAG circuits
to extensionally equivalent tree circuits. -/
theorem same_threshold_witness_transfer_false :
    ¬ (∀ circuit : DagCircuit 2,
      DagCircuit.size circuit ≤ thresholdPoly 1 2 →
        ∃ tree : Models.Circuit 2,
          Models.Circuit.size tree ≤ thresholdPoly 1 2 ∧
            ∀ assignment : Core.BitVec 2,
              Models.Circuit.eval tree assignment =
                DagCircuit.eval circuit (fun index => assignment index)) := by
  intro htransfer
  have hbound : DagCircuit.size nandDag ≤ thresholdPoly 1 2 := by
    change 3 ≤ 3
    exact Nat.le_refl 3
  rcases htransfer nandDag hbound with ⟨tree, hsize, heval⟩
  apply no_small_tree_nand_function tree
    (by simpa only [threshold_at_one_two] using hsize)
  intro assignment
  exact (heval assignment).trans
    (nand_dag_eval (fun index => assignment index))

end Pnp4.Frontier.ContractExpansion.FiniteNand

