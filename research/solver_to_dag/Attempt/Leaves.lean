import Attempt.Assembly

namespace Research.SolverToDag
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier.ContractExpansion

/-- Compile-time table of a GIVEN finite formula, not a chosen decision circuit. -/
def treeTable {n : Nat} (c : Pnp3.Models.Circuit n) : TruthTable n :=
  fun j => c.eval (Pnp3.Core.vecOfNat n j.val)

theorem computes_iff_table {n : Nat} (c : Pnp3.Models.Circuit n) (tt : TruthTable n) :
    ComputesTruthTable treeCircuitClass c tt ↔ tt = treeTable c := by
  constructor
  · intro h
    funext j
    obtain ⟨x, rfl⟩ := Pnp3.Models.assignmentIndex_surjective j
    change tt (Pnp3.Models.assignmentIndex x) =
      c.eval (Pnp3.Core.vecOfNat n (Pnp3.Models.assignmentIndex x).val)
    rw [Pnp3.Models.vecOfNat_assignmentIndex_val]
    exact (h x).symm
  · rintro rfl x
    change c.eval x = c.eval (Pnp3.Core.vecOfNat n (Pnp3.Models.assignmentIndex x).val)
    rw [Pnp3.Models.vecOfNat_assignmentIndex_val]

/-- Equality with a specified raw table; the constant gates are counted too. -/
def matchesTable {n : Nat} (t : TruthTable n) : DagCircuit (Pnp3.Models.Partial.tableLen n) :=
  substInputs (tableEquality n) (Fin.addCases inputProj
    (fun i => constCircuit (Pnp3.Models.Partial.tableLen n) (t i)))

theorem matchesTable_iff {n : Nat} (t tt : TruthTable n) :
    eval (matchesTable t) tt = true ↔ tt = t := by
  simp only [matchesTable, eval_substInputs]
  have h : (fun j => eval (Fin.addCases inputProj
      (fun i => constCircuit (Pnp3.Models.Partial.tableLen n) (t i)) j) tt) =
      Fin.addCases tt t := by
    funext j
    refine Fin.addCases ?_ ?_ j <;> intro i <;>
      simp only [Fin.addCases_left, Fin.addCases_right, eval_inputProj, eval_constCircuit]
  rw [h]
  exact (tableEquality_capstone n tt t).1

theorem matchesTable_size {n : Nat} (t : TruthTable n) :
    size (matchesTable t) = 7 * Pnp3.Models.Partial.tableLen n + 3 := by
  have he := (tableEquality_capstone n t t).2
  rw [matchesTable, size_substInputs, bundleOfFamily_gates]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, inputProj, constCircuit]
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_zero, mul_one, zero_add]
  change (tableEquality n).gates + 1 = _ at he
  omega

/-- Exactly the size-one TREE formulas: n inputs and two constants. -/
def leaves (n : Nat) : List (Pnp3.Models.Circuit n) :=
  [.const false, .const true] ++ (List.finRange n).map Pnp3.Models.Circuit.input

theorem tree_size_pos {n : Nat} (c : Pnp3.Models.Circuit n) : 1 ≤ c.size := by
  cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega

theorem leaves_characterize {n : Nat} (c : Pnp3.Models.Circuit n) :
    c ∈ leaves n ↔ c.size ≤ 1 := by
  cases c with
  | input i => simp [leaves, Pnp3.Models.Circuit.size]
  | const b => cases b <;> simp [leaves, Pnp3.Models.Circuit.size]
  | not a =>
    have h := tree_size_pos a
    simp [leaves, Pnp3.Models.Circuit.size]
    omega
  | and a b =>
    have h := tree_size_pos a
    simp [leaves, Pnp3.Models.Circuit.size]
    omega
  | or a b =>
    have h := tree_size_pos a
    simp [leaves, Pnp3.Models.Circuit.size]
    omega

/-- A real recognizer for threshold one; not an arbitrary-k codec verifier. -/
def leafRecognizer (n : Nat) : DagCircuit (Pnp3.Models.Partial.tableLen n) :=
  bigOrCircuit ((leaves n).map (fun c => matchesTable (treeTable c)))

theorem leafRecognizer_iff (n : Nat) (tt : TruthTable n) :
    eval (leafRecognizer n) tt = true ↔ treeMCSPPredicate n 1 tt := by
  simp only [leafRecognizer, eval_bigOrCircuit_map, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, (leaves_characterize c).mp hc,
      (computes_iff_table c tt).mpr ((matchesTable_iff _ _).mp ht)⟩
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, (leaves_characterize c).mpr hc,
      (matchesTable_iff _ _).mpr ((computes_iff_table c tt).mp ht)⟩

theorem leafRecognizer_size (n : Nat) :
    size (leafRecognizer n) =
      2 + (n + 2) * (7 * Pnp3.Models.Partial.tableLen n + 3) := by
  simp [leafRecognizer, size_bigOrCircuit, matchesTable_size, leaves, List.map_map,
    Function.comp_def]
  ring

/-- Closed all-n capstone for k=0 (threshold n^0+0=1), with an explicit size. -/
theorem leafRecognizer_capstone (n : Nat) (tt : TruthTable n) :
    (eval (leafRecognizer n) tt = true ↔ treeMCSPPredicate n (thresholdPoly 0 n) tt) ∧
    size (leafRecognizer n) =
      2 + (n + 2) * (7 * Pnp3.Models.Partial.tableLen n + 3) := by
  exact ⟨by simpa [thresholdPoly] using leafRecognizer_iff n tt, leafRecognizer_size n⟩

theorem leafRecognizer_polynomial :
    ∃ e : Nat, ∀ n : Nat,
      size (leafRecognizer n) ≤ Pnp3.Models.Partial.tableLen n ^ e + e := by
  have hn := polyBoundedInTable_id
  have hN := polyBoundedInTable_tableLen
  have hp := (PolyBoundedInTable.const 2).add
    ((hn.add (PolyBoundedInTable.const 2)).mul
      (((PolyBoundedInTable.const 7).mul hN).add (PolyBoundedInTable.const 3)))
  obtain ⟨e, he⟩ := hp.powAdd
  exact ⟨e, fun n => by simpa only [leafRecognizer_size] using he n⟩

end Research.SolverToDag
