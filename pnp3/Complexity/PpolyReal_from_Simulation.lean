import Complexity.Interfaces
import Complexity.PsubsetPpolyInternal.CircuitTree

namespace Pnp3
namespace Complexity

open ComplexityInterfaces

namespace TreeAdapter

/-- Compile external tree circuits into the strict `FormulaCircuit` syntax. -/
def toFormula {n : Nat} :
    Internal.PsubsetPpoly.Boolcube.Circuit n → FormulaCircuit n
  | .var i => .input i
  | .const b => .const b
  | .not c => .not (toFormula c)
  | .and c1 c2 => .and (toFormula c1) (toFormula c2)
  | .or c1 c2 => .or (toFormula c1) (toFormula c2)

/-- Source-side structural size used for transport bounds. -/
def size {n : Nat} : Internal.PsubsetPpoly.Boolcube.Circuit n → Nat
  | .var _ => 1
  | .const _ => 1
  | .not c => size c + 1
  | .and c1 c2 => size c1 + size c2 + 1
  | .or c1 c2 => size c1 + size c2 + 1

@[simp] lemma eval_toFormula {n : Nat}
    (c : Internal.PsubsetPpoly.Boolcube.Circuit n) (x : ComplexityInterfaces.Bitstring n) :
    FormulaCircuit.eval (toFormula c) x = Internal.PsubsetPpoly.Boolcube.Circuit.eval c x := by
  induction c with
  | var i => rfl
  | const b => rfl
  | not c ih =>
      simp [toFormula, FormulaCircuit.eval, Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih]
  | and c1 c2 ih1 ih2 =>
      simp [toFormula, FormulaCircuit.eval, Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
      simp [toFormula, FormulaCircuit.eval, Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih1, ih2]

@[simp] lemma size_toFormula {n : Nat} (c : Internal.PsubsetPpoly.Boolcube.Circuit n) :
    FormulaCircuit.size (toFormula c) = size c := by
  induction c with
  | var i => rfl
  | const b => rfl
  | not c ih => simp [toFormula, FormulaCircuit.size, size, ih]
  | and c1 c2 ih1 ih2 =>
      simp [toFormula, FormulaCircuit.size, size, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
      simp [toFormula, FormulaCircuit.size, size, ih1, ih2]

/--
Generic transport lemma: any polynomial-size external tree family gives
`PpolyReal` after compiling into `FormulaCircuit`.
-/
theorem ppolyReal_of_tree_family
    {L : ComplexityInterfaces.Language}
    (polyBound : Nat → Nat)
    (polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c)
    (family : ∀ n, Internal.PsubsetPpoly.Boolcube.Circuit n)
    (family_size_le : ∀ n, size (family n) ≤ polyBound n)
    (correct : ∀ n (x : ComplexityInterfaces.Bitstring n),
      Internal.PsubsetPpoly.Boolcube.Circuit.eval (family n) x = L n x) :
    PpolyReal L := by
  refine ⟨{
    polyBound := polyBound
    polyBound_poly := polyBound_poly
    family := fun n => toFormula (family n)
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · intro n
    simpa [size_toFormula] using family_size_le n
  · intro n x
    simpa [eval_toFormula] using correct n x

end TreeAdapter

end Complexity
end Pnp3
