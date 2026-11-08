import Attempt.RNormalForm
import Attempt.Examples

/-! Explicit public proposition mirrors and full type/arity pins.
These checks add no lower-bound premise or changed codec. Audit checks both
originals and these checking declarations, plus explicit compiler entries.
-/
namespace Research.LengthwiseSearch.Audit
open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier Pnp4.Frontier.ContractExpansion

theorem check_R_full_contract : ConditionalSeparation.OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ∃ n : Nat,
      ∀ outputCircuit :
          Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) →
            Pnp3.ComplexityInterfaces.DagCircuit (Pnp3.Models.Partial.tableLen n),
        (∀ i, Pnp3.ComplexityInterfaces.DagCircuit.size (outputCircuit i) ≤
          (Pnp3.Models.Partial.tableLen n) ^ d + d) →
        ∃ x : Pnp4.AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen n),
          treeMCSPPredicate n (thresholdPoly k n) x ∧
          ¬ (treeCircuitWitnessCodec (thresholdPoly k)).verifies n x
            (fun i => Pnp3.ComplexityInterfaces.DagCircuit.eval (outputCircuit i) x)) :=
  R_iff_lengthwise
end Research.LengthwiseSearch.Audit

namespace Research.LengthwiseSearch.Surface
open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier Pnp4.Frontier.ContractExpansion
universe u

theorem check_family_iff_all_lengths (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass.{u}) (bound : Nat → Nat) :
    Nonempty (Pnp4.Frontier.BoundedSearchSolver problem C bound) ↔
      ∀ n, Nonempty (SolverAt problem C n (bound n)) :=
  family_iff_all_lengths problem C bound

theorem check_lowerBoundAt_iff_no_solver (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass.{u}) (n bound : Nat) :
    LowerBoundAt problem C n bound ↔ ¬ Nonempty (SolverAt problem C n bound) :=
  lowerBoundAt_iff_no_solver problem C n bound

theorem check_no_family_iff_exists_lowerBoundAt (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass.{u}) (bound : Nat → Nat) :
    ¬ Nonempty (Pnp4.Frontier.BoundedSearchSolver problem C bound) ↔
      ∃ n, LowerBoundAt problem C n (bound n) :=
  no_family_iff_exists_lowerBoundAt problem C bound

theorem check_lowerBoundAt_mono {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass.{u}} {n small big : Nat} (hle : small ≤ big)
    (h : LowerBoundAt problem C n big) : LowerBoundAt problem C n small :=
  lowerBoundAt_mono hle h

theorem check_lengthwiseAt_iff_no_family (k : Nat) :
    LengthwiseAt k ↔ ∀ d : Nat,
      ¬ Nonempty (Pnp4.Frontier.BoundedSearchSolver
        (concreteProblem k) C_DAG (polynomialBudget d)) :=
  lengthwiseAt_iff_no_family k

theorem check_R_iff_lengthwise : ConditionalSeparation.OpenProblem.R ↔ LengthwiseR :=
  R_iff_lengthwise

theorem check_exact_R_of_lengthwise (h : LengthwiseR) :
    ConditionalSeparation.OpenProblem.R := exact_R_of_lengthwise h

theorem check_bounded_output_tuple_exists (k d n : Nat) :
    ∃ outputCircuit : Fin ((concreteProblem k).witnessBits n) →
        C_DAG.Family ((concreteProblem k).instanceBits n),
      ∀ i, C_DAG.size (outputCircuit i) ≤ polynomialBudget d n :=
  bounded_output_tuple_exists k d n

theorem check_promised_input_of_lowerBoundAt (k d n : Nat)
    (h : LowerBoundAt (concreteProblem k) C_DAG n (polynomialBudget d n)) :
    ∃ x, (concreteProblem k).promise n x := promised_input_of_lowerBoundAt k d n h

theorem check_threshold_one_le (k n : Nat) : 1 ≤ thresholdPoly k n :=
  threshold_one_le k n

theorem check_witness_width_four_le (k n : Nat) :
    4 ≤ (concreteProblem k).witnessBits n := witness_width_four_le k n

theorem check_constant_table_promised (k n : Nat) (b : Bool) :
    (concreteProblem k).promise n (fun _ => b) := constant_table_promised k n b

theorem check_R_full_contract : ConditionalSeparation.OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ∃ n : Nat,
      ∀ outputCircuit :
          Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) →
            Pnp3.ComplexityInterfaces.DagCircuit (Pnp3.Models.Partial.tableLen n),
        (∀ i, Pnp3.ComplexityInterfaces.DagCircuit.size (outputCircuit i) ≤
          (Pnp3.Models.Partial.tableLen n) ^ d + d) →
        ∃ x : Pnp4.AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen n),
          treeMCSPPredicate n (thresholdPoly k n) x ∧
          ¬ (treeCircuitWitnessCodec (thresholdPoly k)).verifies n x
            (fun i => Pnp3.ComplexityInterfaces.DagCircuit.eval (outputCircuit i) x)) :=
  Audit.check_R_full_contract

theorem check_identity_constant_lower_bound (n : Nat) :
    LowerBoundAt Examples.identityProblem Examples.constantClass n 1 :=
  Examples.identity_constant_lower_bound n

theorem check_no_common_bad_input (n : Nat) :
    ¬ ∃ x : Pnp4.AlgorithmsToLowerBounds.BitVec 1, ∀ outputCircuit : Fin 1 → Bool,
      (∀ i, Examples.constantClass.size (n := 1) (outputCircuit i) ≤ 1) →
      ¬ Examples.identityProblem.relation n x
        (searchSolverOutput (problem := Examples.identityProblem) (C := Examples.constantClass)
          (n := n) outputCircuit x) := Examples.no_common_bad_input n

theorem check_identity_projection_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt Examples.identityProblem Examples.projectionClass n 1 :=
  Examples.identity_projection_no_lower_bound n

theorem check_zero_width_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt Examples.zeroWidthProblem Examples.emptyCircuitClass n 0 :=
  Examples.zero_width_no_lower_bound n

theorem check_zero_budget_vacuous_obstruction (n : Nat) :
    LowerBoundAt Examples.identityProblem Examples.constantClass n 0 :=
  Examples.zero_budget_vacuous_obstruction n

theorem check_empty_promise_no_lower_bound (n : Nat) :
    ¬ LowerBoundAt Examples.emptyPromiseProblem Examples.constantClass n 1 :=
  Examples.empty_promise_no_lower_bound n

def pin_SolverAt : SearchMCSPCompressionProblem → CircuitFamilyClass.{u} → Nat → Nat → Type u :=
  SolverAt

def pin_SolverAt_mk {problem : SearchMCSPCompressionProblem} {C : CircuitFamilyClass.{u}}
    {n bound : Nat} :
    (outputCircuit : Fin (problem.witnessBits n) → C.Family (problem.instanceBits n)) →
    (∀ i, C.size (outputCircuit i) ≤ bound) →
    (∀ x, problem.promise n x → problem.relation n x
      (searchSolverOutput (problem := problem) (C := C) outputCircuit x)) →
    SolverAt problem C n bound := @SolverAt.mk problem C n bound

def pin_SolverAt_outputCircuit {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass.{u}} {n bound : Nat} :
    SolverAt problem C n bound → Fin (problem.witnessBits n) → C.Family (problem.instanceBits n) :=
  SolverAt.outputCircuit

def pin_SolverAt_size_le {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass.{u}} {n bound : Nat} (solver : SolverAt problem C n bound) :
    ∀ i, C.size (solver.outputCircuit i) ≤ bound := SolverAt.size_le solver

def pin_SolverAt_solves {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass.{u}} {n bound : Nat} (solver : SolverAt problem C n bound) :
    ∀ x, problem.promise n x → problem.relation n x
      (searchSolverOutput (problem := problem) (C := C) solver.outputCircuit x) := SolverAt.solves solver

def pin_LowerBoundAt : SearchMCSPCompressionProblem → CircuitFamilyClass.{u} → Nat → Nat → Prop :=
  LowerBoundAt

def pin_atLength {problem : SearchMCSPCompressionProblem} {C : CircuitFamilyClass.{u}}
    {bound : Nat → Nat} (solver : Pnp4.Frontier.BoundedSearchSolver problem C bound) (n : Nat) :
    SolverAt problem C n (bound n) := BoundedSearchSolver.atLength solver n

def pin_concreteProblem : Nat → SearchMCSPCompressionProblem := concreteProblem
def pin_polynomialBudget : Nat → Nat → Nat := polynomialBudget
def pin_LengthwiseAt : Nat → Prop := LengthwiseAt
def pin_LengthwiseR : Prop := LengthwiseR
def pin_boundedProjection (n : Nat) :
    Pnp3.ComplexityInterfaces.DagCircuit (Pnp3.Models.Partial.tableLen n) := boundedProjection n
def pin_identityProblem : SearchMCSPCompressionProblem := Examples.identityProblem
def pin_constantClass : CircuitFamilyClass.{0} := Examples.constantClass
def pin_OneBitCircuit : Nat → Type := Examples.OneBitCircuit
def pin_OneBitCircuit_constant {m : Nat} : Bool → Examples.OneBitCircuit m :=
  @Examples.OneBitCircuit.constant m
def pin_OneBitCircuit_input {m : Nat} : Fin m → Examples.OneBitCircuit m :=
  @Examples.OneBitCircuit.input m
def pin_projectionClass : CircuitFamilyClass.{0} := Examples.projectionClass
def pin_identity_solver (n : Nat) : SolverAt Examples.identityProblem Examples.projectionClass n 1 :=
  Examples.identity_solver n
def pin_emptyCircuitClass : CircuitFamilyClass.{0} := Examples.emptyCircuitClass
def pin_zeroWidthProblem : SearchMCSPCompressionProblem := Examples.zeroWidthProblem
def pin_zero_width_solver (n : Nat) : SolverAt Examples.zeroWidthProblem Examples.emptyCircuitClass n 0 :=
  Examples.zero_width_solver n
def pin_emptyPromiseProblem : SearchMCSPCompressionProblem := Examples.emptyPromiseProblem
def pin_empty_promise_solver (n : Nat) : SolverAt Examples.emptyPromiseProblem Examples.constantClass n 1 :=
  Examples.empty_promise_solver n

-- Explicit boundary elaboration, without extra anonymous declarations.
#check (constant_table_promised 0 0 false : (concreteProblem 0).promise 0 (fun _ => false))
#check (constant_table_promised 0 1 true : (concreteProblem 0).promise 1 (fun _ => true))
#check (Examples.zero_width_solver 0 : SolverAt Examples.zeroWidthProblem Examples.emptyCircuitClass 0 0)
#check (Examples.zero_width_solver 1 : SolverAt Examples.zeroWidthProblem Examples.emptyCircuitClass 1 0)
#check (Examples.empty_promise_solver 0 : SolverAt Examples.emptyPromiseProblem Examples.constantClass 0 1)
#check (Examples.empty_promise_solver 1 : SolverAt Examples.emptyPromiseProblem Examples.constantClass 1 1)
end Research.LengthwiseSearch.Surface
