import Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.AsymptoticSizeLowerBound

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Fixed-depth asymptotic bridge.

The depth is fixed externally; this theorem does not allow depth to grow with
input length.
-/
theorem not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB :
      EventuallySizeLowerBound
        (model.classOf p depth)
        L
        QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L := by
  exact not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound hLB

/--
If every fixed depth has an eventual quasi-polynomial lower bound, then `L` is
not in the fixed-modulus `AC0[p]` union.
-/
theorem not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB :
      ∀ depth : Nat,
        EventuallySizeLowerBound
          (model.classOf p depth)
          L
          QuasiPolyLower) :
    ¬ InAC0p model p L := by
  intro hIn
  rcases hIn with ⟨depth, hPoly⟩
  exact
    (not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
      model p depth L (hLB depth)) hPoly

/--
Asymptotic published-contract shape for an external `AC0[p]` lower-bound
theorem normalized to the weaker lower bound `QuasiPolyLower`.

This is the contract shape that matches published "for sufficiently large input
length" lower bounds.  The bridge theorems using this contract are not
repo-unconditional until the contract itself is proved internally.
-/
structure AC0pAsymptoticQuasiPolynomialLowerBoundContract
    (model : AC0pFamilyModel)
    (L : BitVecLanguage) where
  lowerBound :
    ∀ p depth : Nat,
      Nat.Prime p →
        EventuallySizeLowerBound
          (model.classOf p depth)
          L
          QuasiPolyLower

/-- Pointwise quasi-polynomial contracts can be read as asymptotic contracts. -/
def AC0pAsymptoticQuasiPolynomialLowerBoundContract.of_pointwise
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pQuasiPolynomialLowerBoundContract model L) :
    AC0pAsymptoticQuasiPolynomialLowerBoundContract model L where
  lowerBound := by
    intro p depth hp
    exact EventuallySizeLowerBound.of_sizeLowerBound
      (contract.lowerBound p depth hp)

/--
Contract-derived `AC0[p]` exclusion from asymptotic quasi-polynomial lower
bounds.
-/
theorem not_in_AC0p_from_asymptotic_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pAsymptoticQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L := by
  exact not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
    model
    p
    L
    (fun depth => contract.lowerBound p depth hp)

end AlgorithmsToLowerBounds
end Pnp4
