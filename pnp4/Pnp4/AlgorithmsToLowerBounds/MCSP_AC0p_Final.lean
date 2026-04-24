import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract

namespace Pnp4
namespace AlgorithmsToLowerBounds

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

/--
Contradiction form for one exact small circuit computing the thresholded
tree-MCSP slice singled out by the half-vs-fair coin-reduction witness.
-/
theorem smallCircuit_contradiction_of_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n)
    (c : (model.classOf p depth).Family (Pnp3.Models.Partial.tableLen n))
    (hSize : (model.classOf p depth).size c ≤ contract.sizeBound depth n)
    (hComputes :
      ∀ tt : TruthTable n,
        (model.classOf p depth).eval c tt =
          exactTreeMCSPThresholdDecision n w.oracle.threshold tt) :
    False := by
  let impl :=
    implementedThresholdOracleOfCircuit
      (C := model.classOf p depth)
      (n := n)
      (threshold := w.oracle.threshold)
      c
      hComputes
  have hDecide :
      ∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt := by
    intro tt
    have hExact :
        exactTreeMCSPThresholdDecision n w.oracle.threshold tt = w.oracle.decide tt := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hTrue
        exact
          (w.oracle.correct tt).2
            ((exactTreeMCSPThresholdDecision_spec tt).1 hTrue)
      · intro hTrue
        exact
          (exactTreeMCSPThresholdDecision_spec tt).2
            ((w.oracle.correct tt).1 hTrue)
    calc
      impl.decide tt = exactTreeMCSPThresholdDecision n w.oracle.threshold tt := by
        exact hComputes tt
      _ = w.oracle.decide tt := hExact
  exact smallImplementedThresholdOracle_contradiction_of_AC0pCoinLowerBound
    contract hp w impl hSize rfl hDecide

/--
Size-lower-bound form of the `AC0[p]` coin route on the exact thresholded
tree-MCSP language singled out by the reduction witness.
-/
theorem sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) := by
  intro m c hComp
  by_cases hm : m = Pnp3.Models.Partial.tableLen n
  · subst hm
    have hExact :
        ∀ tt : TruthTable n,
          (model.classOf p depth).eval c tt =
            exactTreeMCSPThresholdDecision n w.oracle.threshold tt := by
      intro tt
      simpa [exactTreeMCSPThresholdLanguage] using hComp tt
    by_contra hLower
    have hLower' :
        ¬ contract.sizeBound depth n + 1 ≤ (model.classOf p depth).size c := by
      simpa [exactTreeMCSPThresholdLowerBound] using hLower
    have hSizeLt :
        (model.classOf p depth).size c < contract.sizeBound depth n + 1 :=
      Nat.not_le.mp hLower'
    have hSize :
        (model.classOf p depth).size c ≤ contract.sizeBound depth n :=
      Nat.lt_succ_iff.mp hSizeLt
    exact smallCircuit_contradiction_of_AC0pCoinLowerBound
      contract hp w c hSize hExact
  · simp [exactTreeMCSPThresholdLowerBound, hm]

/--
Paper-facing lower-bound theorem for the `AC0[p]`-coin route, now in the
standard `SizeLowerBound` form rather than only as an oracle contradiction.
-/
theorem MCSP_lower_bound_from_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) := by
  exact sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
    contract hp w

/--
Theorem-facing lower-bound form of the `AC0[p]` coin route using the smaller
reduction contract instead of an explicit per-slice witness argument.
-/
theorem MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (lowerBound.sizeBound depth n)) := by
  simpa [halfVsFairMCSPCoinLanguage, halfVsFairMCSPCoinLowerBound] using
    MCSP_lower_bound_from_AC0pCoinLowerBound
      lowerBound hp (reduction.toWitness n)

/--
Theorem-facing contradiction form of the `AC0[p]` coin route using the smaller
reduction contract instead of an explicit witness argument.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ lowerBound.sizeBound depth n ∧
        impl.threshold = reduction.threshold n := by
  intro hImpl
  rcases hImpl with ⟨impl, hSize, hThresholdEq⟩
  have hComp :
      ∀ x : BitVec (Pnp3.Models.Partial.tableLen n),
        (model.classOf p depth).eval impl.circuit x =
          halfVsFairMCSPCoinLanguage reduction n
            (Pnp3.Models.Partial.tableLen n) x := by
    intro x
    have hDecideEq :
        impl.decide x = exactTreeMCSPThresholdDecision n impl.threshold x := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hTrue
        exact
          (exactTreeMCSPThresholdDecision_spec x).2
            ((impl.correct x).1 hTrue)
      · intro hTrue
        exact
          (impl.correct x).2
            ((exactTreeMCSPThresholdDecision_spec x).1 hTrue)
    calc
      (model.classOf p depth).eval impl.circuit x = impl.decide x := by
        exact impl.circuit_correct x
      _ = exactTreeMCSPThresholdDecision n impl.threshold x := hDecideEq
      _ = exactTreeMCSPThresholdDecision n (reduction.threshold n) x := by
        simp [hThresholdEq]
      _ = halfVsFairMCSPCoinLanguage reduction n
            (Pnp3.Models.Partial.tableLen n) x := by
        simp [halfVsFairMCSPCoinLanguage, exactTreeMCSPThresholdLanguage]
  have hLower :
      halfVsFairMCSPCoinLowerBound reduction n (lowerBound.sizeBound depth n)
          (Pnp3.Models.Partial.tableLen n) ≤
        (model.classOf p depth).size impl.circuit :=
    MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
      lowerBound reduction hp
      (Pnp3.Models.Partial.tableLen n)
      impl.circuit
      hComp
  have hImpossible : lowerBound.sizeBound depth n + 1 ≤ lowerBound.sizeBound depth n := by
    simpa [halfVsFairMCSPCoinLowerBound, exactTreeMCSPThresholdLowerBound] using
      le_trans hLower hSize
  exact Nat.not_succ_le_self _ hImpossible

end AlgorithmsToLowerBounds
end Pnp4
