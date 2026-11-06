import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Membership in the fixed-modulus `AC0[p]` union: there is one fixed depth whose
circuit family has polynomial size.

The depth is an external constant chosen once.  This is not a statement about
depth growing with the input length.
-/
def InAC0p
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage) : Prop :=
  ∃ depth : Nat,
    HasPolynomialSizeFamily (model.classOf p depth) L

/--
Fixed-depth bridge: a quasi-polynomial lower bound against one fixed
`AC0[p]` depth rules out polynomial-size circuits at that depth.
-/
theorem not_depth_d_AC0p_of_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB :
      SizeLowerBound
        (model.classOf p depth)
        L
        QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L := by
  exact not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound hLB

/--
Depthwise bridge: if every fixed depth has a quasi-polynomial lower bound, then
the language is not in the fixed-modulus `AC0[p]` union.
-/
theorem not_in_AC0p_of_depthwise_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB :
      ∀ depth : Nat,
        SizeLowerBound
          (model.classOf p depth)
          L
          QuasiPolyLower) :
    ¬ InAC0p model p L := by
  intro hIn
  rcases hIn with ⟨depth, hPoly⟩
  exact
    (not_depth_d_AC0p_of_quasiPoly_lowerBound
      model p depth L (hLB depth)) hPoly

/--
Weak published-contract shape for an external `AC0[p]` lower-bound theorem.

The contract is intentionally normalized to the weaker lower bound
`QuasiPolyLower`; stronger published envelopes such as `exp(N^ε)` can be
weakened to this form outside this bridge.  Passing this contract as an argument
does not make the resulting theorem unconditional.
-/
structure AC0pQuasiPolynomialLowerBoundContract
    (model : AC0pFamilyModel)
    (L : BitVecLanguage) where
  lowerBound :
    ∀ p depth : Nat,
      Nat.Prime p →
        SizeLowerBound
          (model.classOf p depth)
          L
          QuasiPolyLower

/--
Contract-derived `AC0[p]` exclusion.

The bridge from quasi-polynomial lower bounds to no polynomial-size fixed-depth
`AC0[p]` families is unconditional; the lower-bound contract itself remains the
external published input.
-/
theorem not_in_AC0p_from_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L := by
  exact not_in_AC0p_of_depthwise_quasiPoly_lowerBound
    model
    p
    L
    (fun depth => contract.lowerBound p depth hp)

end AlgorithmsToLowerBounds
end Pnp4
