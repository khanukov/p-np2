import Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Asymptotic size lower-bound surface.

Published lower bounds usually hold only above a sufficiently large input
length.  This interface keeps that cutoff explicit instead of forcing finite
small cases into a pointwise `SizeLowerBound`.
-/
def EventuallySizeLowerBound
    (C : CircuitFamilyClass)
    (L : BitVecLanguage)
    (lower : Nat → Nat) : Prop :=
  ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
    ∀ c : C.Family N,
      (∀ x : BitVec N, C.eval c x = L N x) →
        lower N ≤ C.size c

/-- A pointwise lower bound is an asymptotic lower bound with cutoff `0`. -/
theorem EventuallySizeLowerBound.of_sizeLowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : SizeLowerBound C L lower) :
    EventuallySizeLowerBound C L lower := by
  refine ⟨0, ?_⟩
  intro N _hN
  exact hLB N

/--
Generic asymptotic super-polynomial bridge.

If exact circuits for `L` are eventually at least `lower`, and `lower` is
super-polynomial, then `L` has no polynomial-size non-uniform family from `C`.
-/
theorem not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : EventuallySizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L := by
  intro hPoly
  rcases hPoly with ⟨a, k, hFamily⟩
  rcases hLB with ⟨NLower, hLB⟩
  rcases hGrowth a k with ⟨NGrowth, hGrowth⟩
  let N := max NLower NGrowth
  have hNLower : NLower ≤ N := Nat.le_max_left NLower NGrowth
  have hNGrowth : NGrowth ≤ N := Nat.le_max_right NLower NGrowth
  rcases hFamily N with ⟨circ, hCorrect, hSize⟩
  have hLower : lower N ≤ C.size circ :=
    hLB N hNLower circ hCorrect
  have hLowerLePoly : lower N ≤ a * N ^ k :=
    le_trans hLower hSize
  have hPolyLtLower : a * N ^ k < lower N :=
    hGrowth N hNGrowth
  exact (Nat.not_lt_of_ge hLowerLePoly) hPolyLtLower

/--
The normalized quasi-polynomial lower bound is enough in the asymptotic lower
bound interface as well.
-/
theorem not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : EventuallySizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L := by
  exact not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
    hLB
    quasiPolyLower_superPolynomialGrowth

end AlgorithmsToLowerBounds
end Pnp4
