import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Integer-friendly lower-envelope for the Golovnev-Ilango-Impagliazzo-Kabanets-
Kolokolova-Tal ICALP 2019 `AC0[p]` lower bound on truth-table slices `N = 2^n`.

The paper-facing statement is `exp(N^(0.49 / d))` for depth `d`.  Since our
slice parameter is already `n = log N`, one representative envelope is
`2 ^ (2 ^ ((49 * n) / (100 * (depth + c + 1))))`, where the extra parameter
`c` absorbs constant-factor losses and indexing conventions for the depth.
-/
def ac0pCoinLowerEnvelope
    (c depth n : Nat) : Nat :=
  2 ^ (2 ^ ((49 * n) / (100 * (depth + c + 1))))

/--
Paper-facing asymptotic profile for the published `AC0[p]` coin-route lower
bound.

This is quantified depth-by-depth, matching the usual fixed-depth reading of the
theorem: for every chosen depth, the published size schedule eventually dominates
the envelope above.
-/
def EventuallyAtLeastAC0pCoinLowerEnvelope
    (sizeBound : Nat → Nat → Nat) : Prop :=
  ∃ c : Nat,
    ∀ depth : Nat, ∃ n0 : Nat,
      ∀ n : Nat, n0 ≤ n →
        ac0pCoinLowerEnvelope c depth n ≤ sizeBound depth n

/--
The canonical published envelope dominates itself, so it immediately satisfies
the paper-facing asymptotic profile.
-/
theorem eventuallyAtLeastAC0pCoinLowerEnvelope_self
    (c : Nat) :
    EventuallyAtLeastAC0pCoinLowerEnvelope (ac0pCoinLowerEnvelope c) := by
  refine ⟨c, ?_⟩
  intro depth
  refine ⟨0, ?_⟩
  intro n _hn
  rfl

/--
Integer-friendly bias-gap envelope for the half-vs-fair coin regime used by the
published `AC0[p]` route.

For truth-table length `N = 2^n`, the paper-facing bias gap is on the order of
`N^(-0.49)`.  The natural-number parameter `c` absorbs constant-factor losses
and indexing conventions.
-/
def ac0pCoinBiasGapEnvelope
    (c n : Nat) : Rat :=
  (1 : Rat) / (2 ^ ((49 * n) / 100 + c) : Nat)

/--
Paper-facing profile for the half-vs-fair bias schedule in the published
`AC0[p]` coin route.
-/
def EventuallyAtMostAC0pCoinBiasGapEnvelope
    (biasGap : Nat → Rat) : Prop :=
  ∃ c n0 : Nat,
    ∀ n : Nat, n0 ≤ n →
      biasGap n ≤ ac0pCoinBiasGapEnvelope c n

/--
Paper-facing profile requiring a genuine positive distinguishing advantage
eventually along the truth-table slices.
-/
def EventuallyAtLeastPositiveCoinAdvantage
    (advantage : Nat → Rat) : Prop :=
  ∃ advFloor : Rat, 0 < advFloor ∧
    ∃ n0 : Nat,
      ∀ n : Nat, n0 ≤ n → advFloor ≤ advantage n

/--
Published half-vs-fair coin regime metadata for the `AC0[p]` route.

This records the two quantitative schedules that are not determined by the
size lower-bound envelope alone: the coin bias gap and the distinguishing
advantage.
-/
structure AC0pCoinPublishedHalfVsFairRegime
    (hardness : HalfVsFairTruthTableCoinHardness) where
  biasGap_profile :
    EventuallyAtMostAC0pCoinBiasGapEnvelope hardness.biasGap
  advantage_profile :
    EventuallyAtLeastPositiveCoinAdvantage hardness.advantage

/--
Quantitative paper-facing strengthening of the basic `AC0[p]` coin lower-bound
contract.

The base contract supplies the exact slice lower bound; the extra field records
that its size schedule has the asymptotic shape promised by the published
`exp(N^(0.49 / d))` lower bound.
-/
structure AC0pHalfVsFairCoinQuantitativeContract
    (model : AC0pFamilyModel)
    (hardness : HalfVsFairTruthTableCoinHardness)
    extends AC0pHalfVsFairCoinLowerBoundContract model hardness where
  theorem_profile :
    EventuallyAtLeastAC0pCoinLowerEnvelope sizeBound

/--
Package a base `AC0[p]` coin lower-bound contract together with an explicit
published-profile witness.
-/
def AC0pHalfVsFairCoinQuantitativeContract.ofLowerBoundContract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hProfile : EventuallyAtLeastAC0pCoinLowerEnvelope contract.sizeBound) :
    AC0pHalfVsFairCoinQuantitativeContract model hardness where
  toAC0pHalfVsFairCoinLowerBoundContract := contract
  theorem_profile := hProfile

/--
Specialized instantiation of the quantitative contract when the base lower-bound
contract already uses the canonical published `exp(N^(0.49 / d))` schedule.
-/
def AC0pHalfVsFairCoinQuantitativeContract.ofPublishedEnvelope
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (c : Nat)
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hSizeBound : contract.sizeBound = ac0pCoinLowerEnvelope c) :
    AC0pHalfVsFairCoinQuantitativeContract model hardness := by
  refine AC0pHalfVsFairCoinQuantitativeContract.ofLowerBoundContract contract ?_
  simpa [hSizeBound] using eventuallyAtLeastAC0pCoinLowerEnvelope_self c

/--
Paper-facing contract for the published `AC0[p]` coin-route schedule with one
explicit envelope constant `c`.

This records that the exact lower-bound contract has already been instantiated
with the canonical schedule `exp(N^(0.49 / d))`, and that the half-vs-fair
hardness object carries the published bias-gap / advantage metadata.
-/
structure AC0pCoinPublishedExpLowerBoundContract
    (model : AC0pFamilyModel)
    (hardness : HalfVsFairTruthTableCoinHardness) where
  envelopeConst : Nat
  hardness_profile :
    AC0pCoinPublishedHalfVsFairRegime hardness
  base :
    AC0pHalfVsFairCoinLowerBoundContract model hardness
  sizeBound_eq :
    base.sizeBound = ac0pCoinLowerEnvelope envelopeConst

/--
Compile the paper-facing published-envelope contract into the stronger
quantitative contract.
-/
def AC0pCoinPublishedExpLowerBoundContract.toQuantitative
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness) :
    AC0pHalfVsFairCoinQuantitativeContract model hardness :=
  AC0pHalfVsFairCoinQuantitativeContract.ofPublishedEnvelope
    contract.envelopeConst
    contract.base
    contract.sizeBound_eq

/--
Exact thresholded MCSP language singled out by one concrete half-vs-fair
reduction witness.
-/
noncomputable def AC0pCoinQuantitativeLanguage
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n : Nat}
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n w.oracle.threshold

/--
Pointwise lower-bound schedule attached to the quantitative `AC0[p]` contract at
depth `depth` and truth-table slice `2^n`.
-/
def AC0pCoinQuantitativeLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (depth n : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)

/--
Direct contradiction theorem from the quantitative `AC0[p]` coin contract.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) := by
  exact noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
    contract.toAC0pHalfVsFairCoinLowerBoundContract hp w

/--
Paper-facing contradiction theorem for the canonical published-envelope version
of the `AC0[p]` coin route.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) := by
  have hQuant :
      ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
          (model.classOf p depth).size impl.circuit ≤
            contract.toQuantitative.sizeBound depth n ∧
          impl.threshold = w.oracle.threshold ∧
          (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
    noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
      (contract := contract.toQuantitative)
      (hp := hp)
      (w := w)
  simpa [AC0pCoinPublishedExpLowerBoundContract.toQuantitative,
    AC0pHalfVsFairCoinQuantitativeContract.ofPublishedEnvelope,
    AC0pHalfVsFairCoinQuantitativeContract.ofLowerBoundContract,
    contract.sizeBound_eq] using hQuant

/--
Direct lower-bound theorem from the quantitative `AC0[p]` coin contract.
-/
theorem MCSP_lower_bound_from_AC0pCoinQuantitativeContract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (AC0pCoinQuantitativeLowerBound contract depth n) := by
  simpa [AC0pCoinQuantitativeLanguage, AC0pCoinQuantitativeLowerBound] using
    MCSP_lower_bound_from_AC0pCoinLowerBound
      contract.toAC0pHalfVsFairCoinLowerBoundContract hp w

/--
Theorem-facing lower-bound theorem for the quantitative `AC0[p]` coin route,
using the smaller reduction contract instead of an explicit witness argument.
-/
theorem MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (contract.sizeBound depth n)) := by
  simpa [halfVsFairMCSPCoinLanguage, halfVsFairMCSPCoinLowerBound] using
    MCSP_lower_bound_from_AC0pCoinQuantitativeContract
      contract hp (reduction.toWitness n)

/--
Paper-facing lower-bound theorem for the canonical published-envelope version of
the `AC0[p]` coin route.
-/
theorem MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) := by
  have hQuant :
      SizeLowerBound
        (model.classOf p depth)
        (AC0pCoinQuantitativeLanguage w)
        (AC0pCoinQuantitativeLowerBound contract.toQuantitative depth n) :=
    MCSP_lower_bound_from_AC0pCoinQuantitativeContract
      (contract := contract.toQuantitative)
      (hp := hp)
      (w := w)
  simpa [AC0pCoinQuantitativeLanguage, AC0pCoinQuantitativeLowerBound,
    AC0pCoinPublishedExpLowerBoundContract.toQuantitative,
    AC0pHalfVsFairCoinQuantitativeContract.ofPublishedEnvelope,
    AC0pHalfVsFairCoinQuantitativeContract.ofLowerBoundContract,
    contract.sizeBound_eq] using hQuant

/--
Theorem-facing lower-bound theorem for the canonical published-envelope version
of the `AC0[p]` coin route, using the smaller reduction contract.
-/
theorem MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) := by
  simpa [halfVsFairMCSPCoinLanguage, AC0pCoinPublishedExpLowerBoundContract.toQuantitative,
    AC0pHalfVsFairCoinQuantitativeContract.ofPublishedEnvelope,
    AC0pHalfVsFairCoinQuantitativeContract.ofLowerBoundContract, contract.sizeBound_eq] using
    MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
      contract hp (reduction.toWitness n)

/--
Theorem-facing contradiction form for the quantitative `AC0[p]` coin route,
using the smaller reduction contract instead of an explicit witness argument.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
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
      halfVsFairMCSPCoinLowerBound reduction n (contract.sizeBound depth n)
          (Pnp3.Models.Partial.tableLen n) ≤
        (model.classOf p depth).size impl.circuit :=
    MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
      contract reduction hp
      (Pnp3.Models.Partial.tableLen n)
      impl.circuit
      hComp
  have hImpossible : contract.sizeBound depth n + 1 ≤ contract.sizeBound depth n := by
    simpa [halfVsFairMCSPCoinLowerBound, exactTreeMCSPThresholdLowerBound] using
      le_trans hLower hSize
  exact Nat.not_succ_le_self _ hImpossible

/--
Theorem-facing contradiction form for the published-envelope version of the
`AC0[p]` coin route, using the smaller reduction contract.
-/
theorem noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
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
      exactTreeMCSPThresholdLowerBound
          n
          (ac0pCoinLowerEnvelope contract.envelopeConst depth n)
          (Pnp3.Models.Partial.tableLen n) ≤
        (model.classOf p depth).size impl.circuit :=
    MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
      contract reduction hp
      (Pnp3.Models.Partial.tableLen n)
      impl.circuit
      hComp
  have hImpossible :
      ac0pCoinLowerEnvelope contract.envelopeConst depth n + 1 ≤
        ac0pCoinLowerEnvelope contract.envelopeConst depth n := by
    simpa [exactTreeMCSPThresholdLowerBound] using le_trans hLower hSize
  exact Nat.not_succ_le_self _ hImpossible

end AlgorithmsToLowerBounds
end Pnp4
