import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Pnp4.AlgorithmsToLowerBounds.Growth

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
The language `L` has polynomial-size non-uniform circuits from class `C`.

The parameters `a` and `k` are fixed externally and do not depend on the input
length.
-/
def HasPolynomialSizeFamily
    (C : CircuitFamilyClass)
    (L : BitVecLanguage) : Prop :=
  ∃ a k : Nat,
    ∀ n : Nat,
      ∃ c : C.Family n,
        (∀ x : BitVec n, C.eval c x = L n x) ∧
          C.size c ≤ a * n ^ k

/--
Generic super-polynomial bridge.

If every exact circuit for `L` has size at least a super-polynomial lower-bound
schedule, then `L` has no polynomial-size non-uniform family from `C`.
-/
theorem not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : SizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L := by
  intro hPoly
  rcases hPoly with ⟨a, k, hFamily⟩
  rcases hGrowth a k with ⟨N0, hDom⟩
  rcases hFamily N0 with ⟨circ, hCorrect, hSize⟩
  have hLower : lower N0 ≤ C.size circ :=
    hLB N0 circ hCorrect
  have hUpper : C.size circ ≤ a * N0 ^ k := hSize
  have hLowerLePoly : lower N0 ≤ a * N0 ^ k :=
    le_trans hLower hUpper
  have hPolyLtLower : a * N0 ^ k < lower N0 :=
    hDom N0 le_rfl
  exact (Nat.not_lt_of_ge hLowerLePoly) hPolyLtLower

/--
Quasi-polynomial lower bounds are already enough to rule out polynomial-size
families.
-/
theorem not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : SizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L := by
  exact not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
    hLB
    quasiPolyLower_superPolynomialGrowth

end AlgorithmsToLowerBounds
end Pnp4
