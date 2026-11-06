import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Abstract family model for `AC0[p]`-style circuit classes.

The actual circuit syntax stays abstract for now; only the dependency on the
prime modulus `p` and depth parameter is fixed at the interface level.
-/
structure AC0pFamilyModel where
  classOf : Nat → Nat → CircuitFamilyClass

/--
Abstract `AC0[p]` family model equipped with the input-restriction closure used
by the masking translation.

For concrete `AC0[p]` syntax this is normally proved by substituting selected
inputs by constants without increasing depth or size.  Since `AC0pFamilyModel`
is intentionally abstract here, the closure is carried as explicit adequacy
data rather than assumed silently.
-/
structure AC0pFamilyModelWithMasking extends AC0pFamilyModel where
  closedUnderInputMasking :
    ∀ p depth : Nat, ClosedUnderInputMasking (classOf p depth)

/-- Read the input-masking closure for one fixed modulus/depth slice. -/
def AC0pFamilyModelWithMasking.closed
    (model : AC0pFamilyModelWithMasking)
    (p depth : Nat) :
    ClosedUnderInputMasking (model.toAC0pFamilyModel.classOf p depth) :=
  model.closedUnderInputMasking p depth

/--
Concrete package for one depth-`d`, modulus-`p` `AC0[p]` family surface.

This is a paper-facing wrapper around `AC0pFamilyModel.classOf p d`.
-/
structure AC0pCircuitClass where
  modulusPrime : Nat
  depth : Nat
  modulus_is_prime : Nat.Prime modulusPrime
  family : CircuitFamilyClass

/-- Package one instance of the abstract `AC0[p]` family model. -/
def AC0pFamilyModel.at
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (hp : Nat.Prime p) :
    AC0pCircuitClass where
  modulusPrime := p
  depth := depth
  modulus_is_prime := hp
  family := model.classOf p depth

/--
Quantitative hardness regime for the paper-facing half-vs-fair coin problem on
truth-table inputs of length `2^n`.

The ICALP 2019 argument uses a bias parameter `ε = Θ(N^{-0.49})` after the
translation step (Claim 2.4).  We keep the exact function abstract here, but
make the shape of the regime explicit.
-/
structure HalfVsFairTruthTableCoinHardness where
  biasGap : Nat → Rat
  advantage : Nat → Rat
  biasGap_pos : ∀ n : Nat, 0 < biasGap n
  biasGap_le_one : ∀ n : Nat, biasGap n ≤ (1 : Rat)

/-- The corresponding half-vs-fair coin instance on truth-table inputs. -/
def HalfVsFairTruthTableCoinHardness.instance
    (hardness : HalfVsFairTruthTableCoinHardness)
    (n : Nat) :
    CoinProblemInstance :=
  halfVsFairCoinInstance
    (Pnp3.Models.Partial.tableLen n)
    (hardness.biasGap n)
    (hardness.biasGap_pos n)
    (hardness.biasGap_le_one n)

/--
Contract layer for published `AC0[p]` coin lower bounds.

This is now formulated as a size lower bound, not as an absolute impossibility
statement for the whole class.  That matches the literature more faithfully.
-/
structure AC0pHalfVsFairCoinLowerBoundContract
    (model : AC0pFamilyModel)
    (hardness : HalfVsFairTruthTableCoinHardness) where
  sizeBound : Nat → Nat → Nat
  noSmallSolver_for_hard_truthTableCoin :
    ∀ {p depth n : Nat}
      (_hp : Nat.Prime p),
      ¬ BoundedClassSolvesCoinProblem
          (model.classOf p depth)
          (hardness.instance n)
          (hardness.advantage n)
          (sizeBound depth n)

/--
Convenience specialization of the contract theorem to one concrete `AC0[p]`
family package.
-/
theorem AC0pHalfVsFairCoinLowerBoundContract.excludes_small_solver
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (_hp : Nat.Prime p) :
    ¬ BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (contract.sizeBound depth n) :=
  contract.noSmallSolver_for_hard_truthTableCoin _hp

end AlgorithmsToLowerBounds
end Pnp4
