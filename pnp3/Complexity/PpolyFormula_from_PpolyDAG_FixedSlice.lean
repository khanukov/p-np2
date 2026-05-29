import Complexity.Interfaces
import Models.Model_PartialMCSP

namespace Pnp3
namespace Complexity

open ComplexityInterfaces
open Models

namespace DagCircuit

/-- Literal fixing one input bit to the value taken by `a`. -/
private def matchingLiteral {n : Nat} (a : Bitstring n) (i : Fin n) :
    FormulaCircuit n :=
  if a i then FormulaCircuit.input i else FormulaCircuit.not (FormulaCircuit.input i)

/-- Conjunction recognizing one concrete assignment on the listed coordinates. -/
private def matchingFormulaAux {n : Nat} (a : Bitstring n) :
    List (Fin n) → FormulaCircuit n
  | [] => FormulaCircuit.const true
  | i :: is => FormulaCircuit.and (matchingLiteral a i) (matchingFormulaAux a is)

/-- Conjunction recognizing one concrete assignment on all coordinates. -/
private def matchingFormula {n : Nat} (a : Bitstring n) : FormulaCircuit n :=
  matchingFormulaAux a (List.finRange n)

/-- DNF over a list of satisfying assignments. -/
private def truthTableFormulaAux {n : Nat} : List (Bitstring n) → FormulaCircuit n
  | [] => FormulaCircuit.const false
  | a :: as => FormulaCircuit.or (matchingFormula a) (truthTableFormulaAux as)

/-- Formula representing the full truth table of one fixed DAG circuit. -/
noncomputable def toFormula {n : Nat} (C : DagCircuit n) : FormulaCircuit n :=
  truthTableFormulaAux
    ((Finset.univ.filter (fun a : Bitstring n => DagCircuit.eval C a = true)).toList)

private theorem eval_matchingLiteral {n : Nat}
    (a x : Bitstring n) (i : Fin n) :
    FormulaCircuit.eval (matchingLiteral a i) x = true ↔ x i = a i := by
  by_cases h : a i
  · simp [matchingLiteral, h, FormulaCircuit.eval]
  · simp [matchingLiteral, h, FormulaCircuit.eval]

private theorem eval_matchingFormulaAux {n : Nat}
    (a x : Bitstring n) :
    ∀ L : List (Fin n),
      FormulaCircuit.eval (matchingFormulaAux a L) x = true ↔
        ∀ i ∈ L, x i = a i
  | [] => by
      simp [matchingFormulaAux, FormulaCircuit.eval]
  | i :: is => by
      simp [matchingFormulaAux, FormulaCircuit.eval, eval_matchingLiteral,
        eval_matchingFormulaAux a x is, List.mem_cons]

private theorem eval_matchingFormula {n : Nat} (a x : Bitstring n) :
    FormulaCircuit.eval (matchingFormula a) x = true ↔ x = a := by
  constructor
  · intro h
    apply funext
    intro i
    exact
      (eval_matchingFormulaAux a x (List.finRange n)).mp h i
        (by simp)
  · intro hEq
    cases hEq
    exact (eval_matchingFormulaAux a a (List.finRange n)).2
      (by
        intro i hi
        rfl)

private theorem eval_truthTableFormulaAux {n : Nat}
    (L : List (Bitstring n)) (x : Bitstring n) :
    FormulaCircuit.eval (truthTableFormulaAux L) x = true ↔
      ∃ a ∈ L, x = a := by
  induction L with
  | nil =>
      simp [truthTableFormulaAux, FormulaCircuit.eval]
  | cons a L ih =>
      simp [truthTableFormulaAux, FormulaCircuit.eval, eval_matchingFormula, ih]

/-- The truth-table formula computes the same Boolean function as the DAG. -/
theorem eval_toFormula {n : Nat} (C : DagCircuit n) (x : Bitstring n) :
    FormulaCircuit.eval (toFormula C) x = DagCircuit.eval C x := by
  by_cases hCx : DagCircuit.eval C x = true
  · have hxMem :
        x ∈ Finset.univ.filter (fun a : Bitstring n => DagCircuit.eval C a = true) := by
      simp [hCx]
    have hTrue :
        FormulaCircuit.eval (toFormula C) x = true := by
      apply (eval_truthTableFormulaAux
        ((Finset.univ.filter (fun a : Bitstring n => DagCircuit.eval C a = true)).toList) x).2
      exact ⟨x, by simpa using hxMem, rfl⟩
    simpa [hCx] using hTrue
  · have hFalseDag : DagCircuit.eval C x = false := by
      cases hEval : DagCircuit.eval C x <;> simp_all
    have hFalseFormula :
        FormulaCircuit.eval (toFormula C) x = false := by
      by_contra hFormula
      have hFormulaTrue : FormulaCircuit.eval (toFormula C) x = true := by
        cases hEval : FormulaCircuit.eval (toFormula C) x <;> simp_all
      rcases
        (eval_truthTableFormulaAux
          ((Finset.univ.filter (fun a : Bitstring n => DagCircuit.eval C a = true)).toList)
          x).1 hFormulaTrue with
        ⟨a, ha, hxa⟩
      have haTrue : DagCircuit.eval C a = true := by
        have haMem :
            a ∈ Finset.univ.filter (fun a : Bitstring n => DagCircuit.eval C a = true) := by
          simpa using ha
        exact (Finset.mem_filter.mp haMem).2
      have hxTrue : DagCircuit.eval C x = true := by
        simpa [hxa] using haTrue
      exact hCx hxTrue
    simp [hFalseFormula, hFalseDag]

end DagCircuit

/-- Any strict formula has syntactic size at least `1`. -/
private lemma formula_size_pos {n : Nat} (c : FormulaCircuit n) :
    1 ≤ FormulaCircuit.size c := by
  induction c with
  | const _ =>
      simp [FormulaCircuit.size]
  | input _ =>
      simp [FormulaCircuit.size]
  | not c ih =>
      exact Nat.succ_le_succ (Nat.zero_le _)
  | and c₁ c₂ ih₁ ih₂ =>
      exact Nat.succ_le_succ (Nat.zero_le _)
  | or c₁ c₂ ih₁ ih₂ =>
      exact Nat.succ_le_succ (Nat.zero_le _)

/--
Fixed-slice bridge: on a language that matters only at one concrete input
length, a DAG witness can be unfolded into a formula witness on that same
length and completed with constant-false formulas off the slice.

This bridge is intentionally specialized to `gapPartialMCSP_Language p` to
avoid overstating it as a generic `PpolyDAG ⊆ PpolyFormula` theorem.
-/
theorem ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice
    (p : GapPartialMCSPParams) :
    PpolyDAG (gapPartialMCSP_Language p) →
      PpolyFormula (gapPartialMCSP_Language p) := by
  intro hDag
  rcases hDag with ⟨w, _⟩
  let targetDag : DagCircuit (partialInputLen p) := w.family (partialInputLen p)
  let targetFormula : FormulaCircuit (partialInputLen p) := DagCircuit.toFormula targetDag
  let c : Nat := FormulaCircuit.size targetFormula
  refine ⟨{
    polyBound := fun m => if hm : m = partialInputLen p then c else 1
    polyBound_poly := ?_
    family := fun m =>
      if hm : m = partialInputLen p then
        cast (by cases hm; rfl) targetFormula
      else
        FormulaCircuit.const false
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · refine ⟨c, ?_⟩
    intro m
    by_cases hm : m = partialInputLen p
    · simp [hm, c]
    · have hcpos : 1 ≤ c := formula_size_pos targetFormula
      have hbound : 1 ≤ m ^ c + c := by
        exact le_trans hcpos (Nat.le_add_left _ _)
      simpa [hm, c] using hbound
  · intro m
    by_cases hm : m = partialInputLen p
    · cases hm
      simp [c, targetFormula]
    · simp [hm, FormulaCircuit.size]
  · intro m x
    by_cases hm : m = partialInputLen p
    · cases hm
      have hCorrect :=
        w.correct (partialInputLen p) x
      simpa [targetDag, targetFormula, DagCircuit.eval_toFormula] using hCorrect
    · simp [hm, gapPartialMCSP_Language, FormulaCircuit.eval]

end Complexity
end Pnp3
