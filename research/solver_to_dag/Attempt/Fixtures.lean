import Attempt.Leaves

namespace Research.SolverToDag
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier.ContractExpansion

def projectionTable : TruthTable 1 := ![false, true]
def negationTable : TruthTable 1 := ![true, false]
def malformedBits : Bitstring (witnessWidth 0 0) := fun _ => true

theorem zero_width_equality : eval (vectorEquality 0) (fun i => Fin.elim0 i) = true := by
  apply (vectorEquality_iff 0 _).mpr
  intro i
  exact Fin.elim0 i

theorem zero_width_size : size (vectorEquality 0) = 3 := by decide

theorem zero_variable_false : eval (leafRecognizer 0) (fun _ => false) = true := by
  apply (leafRecognizer_iff 0 _).mpr
  exact ⟨.const false, by decide, fun _ => rfl⟩

theorem zero_variable_true : eval (leafRecognizer 0) (fun _ => true) = true := by
  apply (leafRecognizer_iff 0 _).mpr
  exact ⟨.const true, by decide, fun _ => rfl⟩

theorem projection_yes : eval (leafRecognizer 1) projectionTable = true := by
  apply (leafRecognizer_iff 1 projectionTable).mpr
  refine ⟨.input 0, by decide, (computes_iff_table _ _).mpr ?_⟩
  funext j
  fin_cases j <;> rfl

theorem negation_not_size_one : ¬ treeMCSPPredicate 1 1 negationTable := by
  rintro ⟨c, hc, ht⟩
  have hmem := (leaves_characterize c).mpr hc
  have he := (computes_iff_table c negationTable).mp ht
  simp [leaves] at hmem
  rcases hmem with rfl | rfl | ⟨i, rfl⟩
  · have h := congrFun he ⟨0, by decide⟩
    change true = false at h
    contradiction
  · have h := congrFun he ⟨1, by decide⟩
    change false = true at h
    contradiction
  · fin_cases i
    have h := congrFun he ⟨0, by decide⟩
    change true = false at h
    contradiction

/-- The n=1 negationTable NO fixture is rejected by the threshold-one graph. -/
theorem negation_no : eval (leafRecognizer 1) negationTable = false := by
  cases h : eval (leafRecognizer 1) negationTable with
  | false => rfl
  | true => exact False.elim (negation_not_size_one ((leafRecognizer_iff _ _).mp h))

/-- SOURCE decoder fixture only: this is NOT a DAG implementation of decoding. -/
theorem malformed_decode :
    ((treeCircuitWitnessCodec (thresholdPoly 0)).decode 0 malformedBits).isNone = true := by
  decide

theorem malformed_not_verifies (tt : TruthTable 0) :
    ¬ (treeCircuitWitnessCodec (thresholdPoly 0)).verifies 0 tt malformedBits := by
  rintro ⟨c, hc, _, _⟩
  have h := malformed_decode
  rw [hc] at h
  contradiction

end Research.SolverToDag
