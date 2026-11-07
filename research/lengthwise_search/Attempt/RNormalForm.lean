import Attempt.Lengthwise
import ConditionalSeparation.OpenProblem

namespace Research.LengthwiseSearch

open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier Pnp4.Frontier.ContractExpansion

/-- Exactly the problem in OpenProblem.R; this introduces no alternate codec. -/
def concreteProblem (k : Nat) : SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem (thresholdPoly k)
    (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))

/-- The existing full-truth-table bound, including lengths zero and one. -/
def polynomialBudget (d n : Nat) : Nat :=
  (Pnp3.Models.Partial.tableLen n) ^ d + d

/-- Keep a caller-selected k fixed before every forbidden degree. -/
def LengthwiseAt (k : Nat) : Prop :=
  ∀ d : Nat, ∃ n : Nat,
    LowerBoundAt (concreteProblem k) C_DAG n (polynomialBudget d n)

def LengthwiseR : Prop := ∃ k : Nat, LengthwiseAt k

theorem lengthwiseAt_iff_no_family (k : Nat) :
    LengthwiseAt k ↔ ∀ d : Nat,
      ¬ Nonempty (Pnp4.Frontier.BoundedSearchSolver
        (concreteProblem k) C_DAG (polynomialBudget d)) := by
  constructor
  · intro h d
    exact (no_family_iff_exists_lowerBoundAt _ _ _).mpr (h d)
  · intro h d
    exact (no_family_iff_exists_lowerBoundAt _ _ _).mp (h d)

/-- Exact R normal form; not a proof of either side. -/
theorem R_iff_lengthwise : ConditionalSeparation.OpenProblem.R ↔ LengthwiseR := by
  change (∃ k : Nat, ∀ d : Nat,
    ¬ Nonempty (Pnp4.Frontier.BoundedSearchSolver
      (concreteProblem k) C_DAG (polynomialBudget d))) ↔ LengthwiseR
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (lengthwiseAt_iff_no_family k).mpr hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (lengthwiseAt_iff_no_family k).mp hk⟩

/-- Given a proof of LengthwiseR, constructs exact R. This conditional
declaration alone is rejected by the existing closed-R checker. -/
theorem exact_R_of_lengthwise (h : LengthwiseR) :
    ConditionalSeparation.OpenProblem.R := R_iff_lengthwise.mpr h

/-- No vacuous obstruction from absence of bounded output tuples in this model.
Zero-gate projections have size one, also for d=0. -/
def boundedProjection (n : Nat) :
    Pnp3.ComplexityInterfaces.DagCircuit (Pnp3.Models.Partial.tableLen n) where
  gates := 0
  gate := fun i => Fin.elim0 i
  output := .input ⟨0, by
    change 0 < 2 ^ n
    exact Nat.pow_pos (by decide)⟩

theorem bounded_output_tuple_exists (k d n : Nat) :
    ∃ outputCircuit : Fin ((concreteProblem k).witnessBits n) →
        C_DAG.Family ((concreteProblem k).instanceBits n),
      ∀ i, C_DAG.size (outputCircuit i) ≤ polynomialBudget d n := by
  refine ⟨fun _ => boundedProjection n, ?_⟩
  intro i
  change 1 ≤ (Pnp3.Models.Partial.tableLen n) ^ d + d
  have hpositive : 0 < Pnp3.Models.Partial.tableLen n := by
    change 0 < 2 ^ n
    exact Nat.pow_pos (by decide)
  have hp : 1 ≤ (Pnp3.Models.Partial.tableLen n) ^ d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos hpositive))
  exact Nat.le_trans hp (Nat.le_add_right _ _)

/-- An obstruction in the concrete model produces an actual promised bad input. -/
theorem promised_input_of_lowerBoundAt (k d n : Nat)
    (h : LowerBoundAt (concreteProblem k) C_DAG n (polynomialBudget d n)) :
    ∃ x, (concreteProblem k).promise n x := by
  obtain ⟨outputCircuit, hsize⟩ := bounded_output_tuple_exists k d n
  obtain ⟨x, hp, _⟩ := h outputCircuit hsize
  exact ⟨x, hp⟩

theorem threshold_one_le (k n : Nat) : 1 ≤ thresholdPoly k n := by
  cases k with
  | zero => simp [thresholdPoly]
  | succ k => unfold thresholdPoly; omega

/-- The concrete witness type never has zero width, even at n=0 or k=0. -/
theorem witness_width_four_le (k n : Nat) :
    4 ≤ (concreteProblem k).witnessBits n := by
  change 4 ≤ (bitLength n + 4) * thresholdPoly k n
  have hleft : 4 ≤ bitLength n + 4 := by omega
  have hright := threshold_one_le k n
  simpa using Nat.mul_le_mul hleft hright

/-- Every length has actual promised inputs; both constant truth tables qualify. -/
theorem constant_table_promised (k n : Nat) (b : Bool) :
    (concreteProblem k).promise n (fun _ => b) := by
  refine ⟨Pnp3.Models.Circuit.const b, threshold_one_le k n, ?_⟩
  intro x
  rfl

end Research.LengthwiseSearch
