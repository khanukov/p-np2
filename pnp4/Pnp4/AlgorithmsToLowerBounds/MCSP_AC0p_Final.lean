import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
MCSP-to-coin reduction witness specialized to the paper-facing half-vs-fair
regime on truth-table inputs.
-/
abbrev HalfVsFairMCSPCoinReductionWitness
    (hardness : HalfVsFairTruthTableCoinHardness)
    (n : Nat) : Type :=
  MCSPCoinReductionWitness
    n
    (((1 : Rat) - hardness.biasGap n) / 2)
    ((1 : Rat) / 2)
    (halfVsFair_lowBias_nonneg (hardness.biasGap_le_one n))
    (by norm_num)
    (halfVsFair_lowBias_lt_fair (hardness.biasGap_pos n))
    (hardness.advantage n)

/--
If a thresholded MCSP oracle yields the paper-facing half-vs-fair truth-table
coin solver, then no implementation of that oracle can have size at most the
published `AC0[p]` lower-bound threshold.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) := by
  intro hImpl
  rcases hImpl with ⟨impl, hSize, hThreshold, hDecide⟩
  have hSmallSolver :
      BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (contract.sizeBound depth n) := by
    refine ⟨impl.circuit, hSize, ?_⟩
    have hCoinForDecide :
        SolvesCoinProblem
          (hardness.instance n)
          impl.decide
          (hardness.advantage n) :=
      solvesCoinProblem_congr
        (inst := hardness.instance n)
        (A := w.oracle.decide)
        (B := impl.decide)
        (adv := hardness.advantage n)
        (funext fun tt => (hDecide tt).symm)
        w.solvesCoin
    exact solvesCoinProblem_congr
      (inst := hardness.instance n)
      (A := impl.decide)
      (B := fun x => (model.classOf p depth).eval impl.circuit x)
      (adv := hardness.advantage n)
      (funext fun tt => (impl.circuit_correct tt).symm)
      hCoinForDecide
  exact contract.excludes_small_solver hp hSmallSolver

/--
Equivalent contradiction form for one candidate implementation of the threshold
oracle together with an explicit size bound.
-/
theorem smallImplementedThresholdOracle_contradiction_of_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n)
    (impl : ImplementedThresholdOracle (model.classOf p depth) n)
    (hSize : (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n)
    (hThreshold : impl.threshold = w.oracle.threshold)
    (hDecide : ∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :
    False := by
  exact noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
    contract hp w
    ⟨impl, hSize, hThreshold, hDecide⟩

end AlgorithmsToLowerBounds
end Pnp4
