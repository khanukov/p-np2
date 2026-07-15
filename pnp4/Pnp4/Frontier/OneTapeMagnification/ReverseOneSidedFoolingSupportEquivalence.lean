import Pnp4.Frontier.OneTapeMagnification.SignedDAGLocalGeneratorTransfer

/-!
# Reverse one-sided signed fooling is exactly support hitting

For every rational error, arbitrary unnormalized signed weights add no power
to the reverse one-sided condition used by the direct standard-DAG transfer.
The existence of such weights is equivalent to the generator support hitting
every tested predicate whose uniform acceptance mass is larger than the
error.

The reverse implication uses the explicit constant weight

`weight seed = Fintype.card Seed * (abs epsilon + 2)`.

For nonnegative error, the sharper constant weight
`Fintype.card Seed` already suffices.

After division by the seed-space cardinality, one accepting seed contributes
`abs epsilon + 2` to the scaled weighted average (or exactly one under the
nonnegative-error witness).  This is enough to dominate every Boolean uniform
average, which is at most one.  If the uniform mass is at most `epsilon`,
nonnegativity of the weighted average is already enough.

The generic finite-type lemmas below deliberately assume neither `Nonempty
Seed` nor `Nonempty Input`.  Thus division by a zero cardinality is covered by
Lean's field convention rather than hidden behind an inhabitation premise.
-/

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.TotalSearch
open ContractExpansion

/-! ## Finite Boolean-average bounds -/

@[simp] theorem boolIndicator_nonneg (value : Bool) :
    0 <= boolIndicator value := by
  cases value <;> simp [boolIndicator]

@[simp] theorem boolIndicator_le_one (value : Bool) :
    boolIndicator value <= 1 := by
  cases value <;> simp [boolIndicator]

/-- A Boolean uniform average lies in `[0,1]`, including on an empty input
type, where its denominator and numerator are both zero. -/
theorem uniformPredicateAverage_mem_unitInterval
    {Input : Type*} [Fintype Input] (predicate : Input -> Bool) :
    0 <= uniformPredicateAverage predicate /\
      uniformPredicateAverage predicate <= 1 := by
  classical
  by_cases hCard : Fintype.card Input = 0
  · simp [uniformPredicateAverage, hCard]
  · have hDenPositive : (0 : Rat) < (Fintype.card Input : Rat) := by
      exact_mod_cast Nat.pos_of_ne_zero hCard
    have hSumNonnegative :
        (0 : Rat) <= ∑ input : Input, boolIndicator (predicate input) := by
      exact Finset.sum_nonneg fun input _ => boolIndicator_nonneg _
    have hSumAtMostCard :
        (∑ input : Input, boolIndicator (predicate input)) <=
          (Fintype.card Input : Rat) := by
      have hTermwise := Finset.sum_le_sum fun input
        (_hMem : input ∈ (Finset.univ : Finset Input)) =>
          boolIndicator_le_one (predicate input)
      simpa using hTermwise
    constructor
    · unfold uniformPredicateAverage
      exact div_nonneg hSumNonnegative hDenPositive.le
    · unfold uniformPredicateAverage
      exact (div_le_one hDenPositive).2 hSumAtMostCard

theorem uniformPredicateAverage_nonneg
    {Input : Type*} [Fintype Input] (predicate : Input -> Bool) :
    0 <= uniformPredicateAverage predicate :=
  (uniformPredicateAverage_mem_unitInterval predicate).1

theorem uniformPredicateAverage_le_one
    {Input : Type*} [Fintype Input] (predicate : Input -> Bool) :
    uniformPredicateAverage predicate <= 1 :=
  (uniformPredicateAverage_mem_unitInterval predicate).2

/-! ## The constant-cardinality witness -/

/-- On an inhabited seed type, weighting every seed by the seed-space
cardinality turns the normalized weighted average into the unnormalized count
of accepting seeds. -/
theorem weightedGeneratorAverage_constantCard_eq_sum
    {Seed Input : Type*} [Fintype Seed] [Fintype Input] [Nonempty Seed]
    (generator : Seed -> Input) (predicate : Input -> Bool) :
    weightedGeneratorAverage generator
        (fun _ : Seed => (Fintype.card Seed : Rat)) predicate =
      ∑ seed : Seed, boolIndicator (predicate (generator seed)) := by
  classical
  have hCard : (Fintype.card Seed : Rat) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold weightedGeneratorAverage
  rw [← Finset.mul_sum]
  exact (mul_div_cancel_left₀ _ hCard)

/-- A hit contributes at least one to the constant-cardinality weighted
average.  Duplicate generator outputs can only increase this average. -/
theorem one_le_weightedGeneratorAverage_constantCard_of_hit
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (hHit : ∃ seed, predicate (generator seed) = true) :
    1 <= weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat)) predicate := by
  classical
  rcases hHit with ⟨seed, hAccepts⟩
  letI : Nonempty Seed := ⟨seed⟩
  rw [weightedGeneratorAverage_constantCard_eq_sum]
  have hTermNonnegative : ∀ other ∈ (Finset.univ : Finset Seed),
      (0 : Rat) <= boolIndicator (predicate (generator other)) := by
    intro other _
    exact boolIndicator_nonneg _
  have hSingle :
      boolIndicator (predicate (generator seed)) <=
        ∑ other : Seed, boolIndicator (predicate (generator other)) :=
    Finset.single_le_sum hTermNonnegative (Finset.mem_univ seed)
  simpa [boolIndicator, hAccepts] using hSingle

/-- For the constant-cardinality weight, every predicate has nonnegative
weighted average.  This also covers an empty seed type, where the average is
zero because both the sum and denominator vanish. -/
theorem weightedGeneratorAverage_constantCard_nonneg
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool) :
    0 <= weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat)) predicate := by
  classical
  by_cases hCard : Fintype.card Seed = 0
  · simp [weightedGeneratorAverage, hCard]
  · have hDenNonnegative : (0 : Rat) <= (Fintype.card Seed : Rat) := by
      positivity
    apply div_nonneg
    · exact Finset.sum_nonneg fun seed _ =>
        mul_nonneg hDenNonnegative (boolIndicator_nonneg _)
    · exact hDenNonnegative

/-- Scaling the constant-cardinality weight by `scale` scales the accepting
seed count by exactly `scale` on an inhabited seed type. -/
theorem weightedGeneratorAverage_scaledConstantCard_eq_mul_sum
    {Seed Input : Type*} [Fintype Seed] [Fintype Input] [Nonempty Seed]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (scale : Rat) :
    weightedGeneratorAverage generator
        (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate =
      scale * ∑ seed : Seed, boolIndicator (predicate (generator seed)) := by
  classical
  have hCard : (Fintype.card Seed : Rat) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold weightedGeneratorAverage
  rw [← Finset.mul_sum]
  apply (div_eq_iff hCard).2
  ring

/-- A hit contributes at least `scale` under a nonnegative scaled
constant-cardinality weight. -/
theorem scale_le_weightedGeneratorAverage_scaledConstantCard_of_hit
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (scale : Rat) (hScale : 0 <= scale)
    (hHit : ∃ seed, predicate (generator seed) = true) :
    scale <= weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate := by
  classical
  rcases hHit with ⟨seed, hAccepts⟩
  letI : Nonempty Seed := ⟨seed⟩
  rw [weightedGeneratorAverage_scaledConstantCard_eq_mul_sum]
  have hTermNonnegative : ∀ other ∈ (Finset.univ : Finset Seed),
      (0 : Rat) <= boolIndicator (predicate (generator other)) := by
    intro other _
    exact boolIndicator_nonneg _
  have hSingle :
      boolIndicator (predicate (generator seed)) <=
        ∑ other : Seed, boolIndicator (predicate (generator other)) :=
    Finset.single_le_sum hTermNonnegative (Finset.mem_univ seed)
  have hOneLe :
      (1 : Rat) <=
        ∑ other : Seed, boolIndicator (predicate (generator other)) := by
    simpa [boolIndicator, hAccepts] using hSingle
  simpa using mul_le_mul_of_nonneg_left hOneLe hScale

/-- A nonnegative scaled constant-cardinality weight always has nonnegative
weighted average, including for an empty seed type. -/
theorem weightedGeneratorAverage_scaledConstantCard_nonneg
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (scale : Rat) (hScale : 0 <= scale) :
    0 <= weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate := by
  classical
  unfold weightedGeneratorAverage
  apply div_nonneg
  · exact Finset.sum_nonneg fun seed _ =>
      mul_nonneg
        (mul_nonneg (by positivity) hScale)
        (boolIndicator_nonneg _)
  · positivity

/-- Support hitting above `epsilon` implies reverse one-sided approximation
under the explicit constant-cardinality weight.  No inhabitation assumption
is needed on either finite type. -/
theorem constantCardWeight_reverseOneSided_of_hitsAboveMass
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (epsilon : Rat) (hEpsilon : 0 <= epsilon)
    (hHits : epsilon < uniformPredicateAverage predicate ->
      ∃ seed, predicate (generator seed) = true) :
    uniformPredicateAverage predicate -
        weightedGeneratorAverage generator
          (fun _ : Seed => (Fintype.card Seed : Rat)) predicate <=
      epsilon := by
  by_cases hMass : epsilon < uniformPredicateAverage predicate
  · have hWeightedAtLeastOne :=
      one_le_weightedGeneratorAverage_constantCard_of_hit
        generator predicate (hHits hMass)
    have hUniformAtMostOne := uniformPredicateAverage_le_one predicate
    have hDifferenceNonpositive :
        uniformPredicateAverage predicate -
            weightedGeneratorAverage generator
              (fun _ : Seed => (Fintype.card Seed : Rat)) predicate <= 0 := by
      linarith
    exact hDifferenceNonpositive.trans hEpsilon
  · have hUniformAtMostEpsilon :
        uniformPredicateAverage predicate <= epsilon := le_of_not_gt hMass
    have hWeightedNonnegative :=
      weightedGeneratorAverage_constantCard_nonneg generator predicate
    linarith

/-- For arbitrary rational `epsilon`, support hitting above `epsilon` still
implies a reverse one-sided approximation.  The explicit nonnegative witness
uses the larger constant weight

`card Seed * (abs epsilon + 2)`.

The extra scale is only needed when `epsilon` may be negative; for
`0 <= epsilon`, the sharper constant-cardinality theorem above suffices. -/
theorem scaledConstantCardWeight_reverseOneSided_of_hitsAboveMass
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed -> Input) (predicate : Input -> Bool)
    (epsilon : Rat)
    (hHits : epsilon < uniformPredicateAverage predicate ->
      ∃ seed, predicate (generator seed) = true) :
    uniformPredicateAverage predicate -
        weightedGeneratorAverage generator
          (fun _ : Seed =>
            (Fintype.card Seed : Rat) * (abs epsilon + 2)) predicate <=
      epsilon := by
  have hScale : (0 : Rat) <= abs epsilon + 2 := by positivity
  by_cases hMass : epsilon < uniformPredicateAverage predicate
  · have hWeightedLarge :=
      scale_le_weightedGeneratorAverage_scaledConstantCard_of_hit
        generator predicate (abs epsilon + 2) hScale (hHits hMass)
    have hUniformAtMostOne := uniformPredicateAverage_le_one predicate
    have hAbs := neg_le_abs epsilon
    linarith
  · have hUniformAtMostEpsilon :
        uniformPredicateAverage predicate <= epsilon := le_of_not_gt hMass
    have hWeightedNonnegative :=
      weightedGeneratorAverage_scaledConstantCard_nonneg
        generator predicate (abs epsilon + 2) hScale
    linarith

/-! ## Exact equivalence for the standard-DAG family -/

/-- The support-only formulation: every standard DAG of bounded size whose
uniform acceptance mass exceeds `epsilon` accepts at least one generator
output. -/
def HitsDAGPredicatesAboveUniformMass
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) (epsilon : Rat) : Prop :=
  ∀ circuit : C_DAG.Family (Pnp3.Models.Partial.tableLen n),
    C_DAG.size circuit <= maxSize ->
      epsilon < uniformPredicateAverage
        (fun table : TruthTable n => C_DAG.eval circuit table) ->
      ∃ seed : FiniteBitTape generator.seedBits,
        C_DAG.eval circuit (generator.generate seed) = true

/-- Any reverse one-sided signed fooler has the corresponding support-hitting
property.  The accepting seed returned by the generic support lemma actually
has nonzero weight, although this support-only interface forgets that extra
fact. -/
theorem hitsDAGPredicatesAboveUniformMass_of_reverseOneSidedFools
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (maxSize : Nat) (epsilon : Rat)
    (hFools : ReverseOneSidedFoolsDAGLocalGenerator
      generator weight maxSize epsilon) :
    HitsDAGPredicatesAboveUniformMass generator maxSize epsilon := by
  intro circuit hSize hMass
  rcases lowerWeightedApproximation_support_hits
      generator.generate weight
      (fun table : TruthTable n => C_DAG.eval circuit table)
      epsilon (hFools circuit hSize) hMass with
    ⟨seed, _hWeight, hAccepts⟩
  exact ⟨seed, hAccepts⟩

/-- Constant-cardinality weights turn bounded-DAG support hitting into the
reverse one-sided fooling condition whenever `epsilon` is nonnegative. -/
theorem constantCardWeight_reverseOneSidedFoolsDAGLocalGenerator
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) (epsilon : Rat) (hEpsilon : 0 <= epsilon)
    (hHits : HitsDAGPredicatesAboveUniformMass
      generator maxSize epsilon) :
    ReverseOneSidedFoolsDAGLocalGenerator generator
      (fun _ : FiniteBitTape generator.seedBits =>
        (Fintype.card (FiniteBitTape generator.seedBits) : Rat))
      maxSize epsilon := by
  intro circuit hSize
  apply constantCardWeight_reverseOneSided_of_hitsAboveMass
    generator.generate
    (fun table : TruthTable n => C_DAG.eval circuit table)
    epsilon hEpsilon
  exact hHits circuit hSize

/-- For arbitrary rational error, the scaled constant-cardinality weight is
an explicit reverse one-sided fooler whenever the support hits every bounded
DAG predicate above that error mass. -/
theorem scaledConstantCardWeight_reverseOneSidedFoolsDAGLocalGenerator
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) (epsilon : Rat)
    (hHits : HitsDAGPredicatesAboveUniformMass
      generator maxSize epsilon) :
    ReverseOneSidedFoolsDAGLocalGenerator generator
      (fun _ : FiniteBitTape generator.seedBits =>
        (Fintype.card (FiniteBitTape generator.seedBits) : Rat) *
          (abs epsilon + 2))
      maxSize epsilon := by
  intro circuit hSize
  apply scaledConstantCardWeight_reverseOneSided_of_hitsAboveMass
    generator.generate
    (fun table : TruthTable n => C_DAG.eval circuit table)
    epsilon
  exact hHits circuit hSize

/-- Exact fixed-weight equivalence.  At nonnegative error, the particular
constant-cardinality weighting reverse-one-sided-fools the bounded standard
DAG class exactly when the generator support hits every predicate above the
error mass. -/
theorem constantCardWeight_reverseOneSidedFoolsDAGLocalGenerator_iff
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) (epsilon : Rat) (hEpsilon : 0 <= epsilon) :
    ReverseOneSidedFoolsDAGLocalGenerator generator
        (fun _ : FiniteBitTape generator.seedBits =>
          (Fintype.card (FiniteBitTape generator.seedBits) : Rat))
        maxSize epsilon ↔
      HitsDAGPredicatesAboveUniformMass generator maxSize epsilon := by
  constructor
  · exact hitsDAGPredicatesAboveUniformMass_of_reverseOneSidedFools
      generator _ maxSize epsilon
  · exact constantCardWeight_reverseOneSidedFoolsDAGLocalGenerator
      generator maxSize epsilon hEpsilon

/-- Exact existential equivalence for every rational `epsilon`: allowing
arbitrary unnormalized signed weights is equivalent to the support-only
hitting condition.  The reverse direction is witnessed explicitly by the
scaled constant-cardinality weight above. -/
theorem exists_reverseOneSidedFoolsDAGLocalGenerator_iff_hits
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) (epsilon : Rat) :
    (∃ weight : FiniteBitTape generator.seedBits -> Rat,
        ReverseOneSidedFoolsDAGLocalGenerator
          generator weight maxSize epsilon) ↔
      HitsDAGPredicatesAboveUniformMass generator maxSize epsilon := by
  constructor
  · rintro ⟨weight, hFools⟩
    exact hitsDAGPredicatesAboveUniformMass_of_reverseOneSidedFools
      generator weight maxSize epsilon hFools
  · intro hHits
    refine ⟨(fun _ : FiniteBitTape generator.seedBits =>
      (Fintype.card (FiniteBitTape generator.seedBits) : Rat) *
        (abs epsilon + 2)), ?_⟩
    exact scaledConstantCardWeight_reverseOneSidedFoolsDAGLocalGenerator
      generator maxSize epsilon hHits

/-! ## The sharp above-half endpoint -/

/-- Support hitting only for bounded standard-DAG predicates whose uniform
acceptance mass is strictly larger than one half. -/
def HitsEveryAboveHalfDAGPredicate
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) : Prop :=
  HitsDAGPredicatesAboveUniformMass generator maxSize ((1 : Rat) / 2)

/-- The witness-set version consumed directly by the MCSP density proof.
Unlike the signed-fooling premise with `epsilon < 1/2`, this asks for no
predicates of mass at or below one half. -/
def HitsDenseDAGPredicates
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat) : Prop :=
  ∀ circuit : C_DAG.Family (Pnp3.Models.Partial.tableLen n),
    C_DAG.size circuit <= maxSize ->
      DenseAboveHalf n
        (fun table : TruthTable n => C_DAG.eval circuit table = true) ->
      ∃ seed : FiniteBitTape generator.seedBits,
        C_DAG.eval circuit (generator.generate seed) = true

/-- Uniform-mass above-half hitting supplies the explicit witness-set version
without changing the size bound. -/
theorem hitsDenseDAGPredicates_of_hitsEveryAboveHalf
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat)
    (hHits : HitsEveryAboveHalfDAGPredicate generator maxSize) :
    HitsDenseDAGPredicates generator maxSize := by
  intro circuit hSize hDense
  apply hHits circuit hSize
  exact uniformPredicateAverage_gt_half_of_dense
    (fun table : TruthTable n => C_DAG.eval circuit table) hDense

/-- Signed fooling with error strictly below one half implies the sharp dense
hitting endpoint.  This direction is useful for comparing the two premises;
the converse is intentionally not asserted because signed fooling at
`epsilon < 1/2` also forces hits below the half-density threshold. -/
theorem hitsDenseDAGPredicates_of_reverseOneSidedFools
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (maxSize : Nat) (epsilon : Rat)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hFools : ReverseOneSidedFoolsDAGLocalGenerator
      generator weight maxSize epsilon) :
    HitsDenseDAGPredicates generator maxSize := by
  intro circuit hSize hDense
  have hAboveHalf : (1 : Rat) / 2 <
      uniformPredicateAverage
        (fun table : TruthTable n => C_DAG.eval circuit table) :=
    uniformPredicateAverage_gt_half_of_dense
      (fun table : TruthTable n => C_DAG.eval circuit table) hDense
  have hMass : epsilon <
      uniformPredicateAverage
        (fun table : TruthTable n => C_DAG.eval circuit table) :=
    lt_trans hEpsilon hAboveHalf
  rcases lowerWeightedApproximation_support_hits
      generator.generate weight
      (fun table : TruthTable n => C_DAG.eval circuit table)
      epsilon (hFools circuit hSize) hMass with
    ⟨seed, _hWeight, hAccepts⟩
  exact ⟨seed, hAccepts⟩

/-! ## Generator-free dense/easy intersection -/

/-- Every bounded standard-DAG predicate with an explicit above-half
accepting set accepts at least one truth table that is easy at `threshold`.

This is the generator-free semantic content of the dense-support premise. -/
def EveryDenseDAGPredicateAcceptsEasyTable
    (n threshold maxSize : Nat) : Prop :=
  ∀ circuit : C_DAG.Family (Pnp3.Models.Partial.tableLen n),
    C_DAG.size circuit <= maxSize ->
      DenseAboveHalf n
        (fun table : TruthTable n => C_DAG.eval circuit table = true) ->
      ∃ table : TruthTable n,
        HasCircuit n threshold table /\
          C_DAG.eval circuit table = true

/-- A local generator hitting every dense predicate supplies an easy accepted
table simply by exposing the hit image and its `image_easy` certificate. -/
theorem everyDenseDAGPredicateAcceptsEasyTable_of_hitsDense
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (maxSize : Nat)
    (hHits : HitsDenseDAGPredicates generator maxSize) :
    EveryDenseDAGPredicateAcceptsEasyTable n threshold maxSize := by
  intro circuit hSize hDense
  rcases hHits circuit hSize hDense with ⟨seed, hAccepts⟩
  exact ⟨generator.generate seed, generator.image_easy seed, hAccepts⟩

/-! ## One shared output-NOT gate -/

private def supportUnaryNotDAG : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input (0 : Fin 1))
  output := DagWire.gate (0 : Fin 1)

@[simp] private theorem eval_supportUnaryNotDAG (input : Bitstring 1) :
    DagCircuit.eval supportUnaryNotDAG input = !input 0 := by
  simp [supportUnaryNotDAG, DagCircuit.eval, DagCircuit.eval.evalGateAt]

private def supportNegateDAG
    {inputBits : Nat} (circuit : DagCircuit inputBits) :
    DagCircuit inputBits :=
  substInputs supportUnaryNotDAG (fun _ => circuit)

@[simp] private theorem eval_supportNegateDAG
    {inputBits : Nat} (circuit : DagCircuit inputBits)
    (input : Bitstring inputBits) :
    DagCircuit.eval (supportNegateDAG circuit) input =
      !DagCircuit.eval circuit input := by
  simp [supportNegateDAG]

@[simp] private theorem size_supportNegateDAG
    {inputBits : Nat} (circuit : DagCircuit inputBits) :
    DagCircuit.size (supportNegateDAG circuit) =
      DagCircuit.size circuit + 1 := by
  rw [supportNegateDAG, size_substInputs, bundleOfFamily_gates]
  simp [supportUnaryNotDAG, DagCircuit.size]

/-! ## Enumerating all easy tables -/

/-- A one-gate constant-true DAG in the unrestricted standard DAG class used
to quantify tested predicates.  Its frozen `C_DAG` size is two. -/
private def supportConstantTrueDAG (inputBits : Nat) :
    DagCircuit inputBits where
  gates := 1
  gate := fun _ => DagGate.const true
  output := DagWire.gate (0 : Fin 1)

@[simp] private theorem eval_supportConstantTrueDAG
    {inputBits : Nat} (input : Bitstring inputBits) :
    DagCircuit.eval (supportConstantTrueDAG inputBits) input = true := by
  simp [supportConstantTrueDAG, DagCircuit.eval, DagCircuit.eval.evalGateAt]

@[simp] private theorem size_supportConstantTrueDAG (inputBits : Nat) :
    DagCircuit.size (supportConstantTrueDAG inputBits) = 2 := by
  simp [supportConstantTrueDAG, DagCircuit.size]

private theorem supportConstantTrueDAG_dense (n : Nat) :
    DenseAboveHalf n
      (fun table : TruthTable n =>
        C_DAG.eval
          (supportConstantTrueDAG (Pnp3.Models.Partial.tableLen n)) table =
            true) := by
  classical
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_univ, truthTableSpace_card]
    have hPositive : 0 < 2 ^ (2 ^ n) := by positivity
    omega
  · intro table _
    simp [ContractExpansion.C_DAG]

/-- Given one default easy table, a noncomputable full-table seed enumerator
outputs every easy truth table unchanged and redirects hard seeds to the
default.  Its seed type is definitionally the whole truth-table cube. -/
noncomputable def easyTableEnumerator
    {n threshold : Nat} (defaultEasy : TruthTable n)
    (hDefaultEasy : HasCircuit n threshold defaultEasy) :
    DAGLocalGenerator n threshold := by
  classical
  exact
    { seedBits := 2 ^ n
      generate := fun seed =>
        if hEasy : HasCircuit n threshold seed then seed else defaultEasy
      image_easy := by
        intro seed
        split
        next hEasy => exact hEasy
        next _ => exact hDefaultEasy }

@[simp] theorem easyTableEnumerator_generate_of_easy
    {n threshold : Nat} (defaultEasy table : TruthTable n)
    (hDefaultEasy : HasCircuit n threshold defaultEasy)
    (hEasy : HasCircuit n threshold table) :
    (easyTableEnumerator defaultEasy hDefaultEasy).generate table = table := by
  simp [easyTableEnumerator, hEasy]

/-- Once size two is available for the constant-true test, existence of some
local dense-hitting generator is exactly the generator-free statement that
every dense bounded-DAG predicate accepts an easy table.

The reverse witness deliberately has the full truth-table length as its seed
length and is noncomputable.  Thus this equivalence exposes that
`DAGLocalGenerator` by itself imposes no short-seed or joint-computation
requirement. -/
theorem exists_hitsDenseDAGLocalGenerator_iff_everyDenseAcceptsEasy
    (n threshold maxSize : Nat) (hMaxSize : 2 <= maxSize) :
    (∃ generator : DAGLocalGenerator n threshold,
        HitsDenseDAGPredicates generator maxSize) ↔
      EveryDenseDAGPredicateAcceptsEasyTable n threshold maxSize := by
  constructor
  · rintro ⟨generator, hHits⟩
    exact everyDenseDAGPredicateAcceptsEasyTable_of_hitsDense
      generator maxSize hHits
  · intro hSemantic
    have hTrueSize :
        C_DAG.size
            (supportConstantTrueDAG
              (Pnp3.Models.Partial.tableLen n)) <= maxSize := by
      change DagCircuit.size
        (supportConstantTrueDAG (Pnp3.Models.Partial.tableLen n)) <= maxSize
      simpa using hMaxSize
    rcases hSemantic
        (supportConstantTrueDAG (Pnp3.Models.Partial.tableLen n))
        hTrueSize (supportConstantTrueDAG_dense n) with
      ⟨defaultEasy, hDefaultEasy, _hTrue⟩
    let generator : DAGLocalGenerator n threshold :=
      easyTableEnumerator defaultEasy hDefaultEasy
    refine ⟨generator, ?_⟩
    intro circuit hSize hDense
    rcases hSemantic circuit hSize hDense with
      ⟨table, hEasy, hAccepts⟩
    refine ⟨table, ?_⟩
    change C_DAG.eval circuit
      ((easyTableEnumerator defaultEasy hDefaultEasy).generate table) = true
    simpa [easyTableEnumerator_generate_of_easy
      defaultEasy table hDefaultEasy hEasy] using hAccepts

/-! ## Direct standard-DAG lower-bound transfer -/

/-- The sharp all-exponent dense-support premise directly excludes a
`PpolyDAG` family deciding standard-DAG MCSP on the stated slices.

For the one output-negated hypothetical decider, elementary code counting
supplies an explicit accepted set above half, and
`HitsDenseDAGPredicates` supplies one generator image in it. -/
theorem not_PpolyDAG_of_dense_DAGLocalGenerator_slices
    (L : Language) (threshold : Nat -> Nat)
    (hSlice : ∀ n : Nat, ∀ table : TruthTable n,
      L (Pnp3.Models.Partial.tableLen n) table =
        EncodedTotalSearch.referenceDecision (s := threshold n) table)
    (hDenseHits : ∀ exponent : Nat,
      ∃ n : Nat,
      ∃ generator : DAGLocalGenerator n (threshold n),
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        HitsDenseDAGPredicates generator
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) :
    Not (PpolyDAG L) := by
  intro hDAG
  have hFamily := PpolyDAG_decider_as_C_DAG_decider hDAG
  choose exponent hCircuits using hFamily
  rcases hDenseHits exponent with
    ⟨n, generator, hLength, hHits⟩
  rcases hCircuits (Pnp3.Models.Partial.tableLen n) with
    ⟨circuit, hCircuitSize, hCorrect⟩
  let complementCircuit := supportNegateDAG circuit
  have hComplementSize :
      C_DAG.size complementCircuit <=
        (Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1 := by
    change DagCircuit.size complementCircuit <= _
    change DagCircuit.size circuit <= _ at hCircuitSize
    simpa [complementCircuit] using Nat.add_le_add_right hCircuitSize 1
  have hDenseComplement : DenseAboveHalf n
      (fun table : TruthTable n =>
        C_DAG.eval complementCircuit table = true) := by
    rcases coMCSP_denseAboveHalf n (threshold n) hLength with
      ⟨witnesses, hWitnessCard, hHard⟩
    refine ⟨witnesses, hWitnessCard, ?_⟩
    intro table hMem
    have hNoCircuit : Not (HasCircuit n (threshold n) table) :=
      hHard table hMem
    have hReferenceFalse :
        EncodedTotalSearch.referenceDecision
          (s := threshold n) table = false := by
      cases hReference :
          EncodedTotalSearch.referenceDecision
            (s := threshold n) table with
      | false => rfl
      | true =>
          exact False.elim
            (hNoCircuit
              ((EncodedTotalSearch.referenceDecision_eq_true_iff table).1
                hReference))
    have hCircuitFalse : C_DAG.eval circuit table = false := by
      calc
        C_DAG.eval circuit table =
            L (Pnp3.Models.Partial.tableLen n) table := hCorrect table
        _ = EncodedTotalSearch.referenceDecision
              (s := threshold n) table := hSlice n table
        _ = false := hReferenceFalse
    change DagCircuit.eval complementCircuit table = true
    simpa [complementCircuit, hCircuitFalse]
  rcases hHits complementCircuit hComplementSize hDenseComplement with
    ⟨seed, hComplementAccepts⟩
  have hReferenceTrue :
      EncodedTotalSearch.referenceDecision (s := threshold n)
          (generator.generate seed) = true :=
    (EncodedTotalSearch.referenceDecision_eq_true_iff
      (generator.generate seed)).2 (generator.image_easy seed)
  have hCircuitTrue :
      C_DAG.eval circuit (generator.generate seed) = true := by
    calc
      C_DAG.eval circuit (generator.generate seed) =
          L (Pnp3.Models.Partial.tableLen n) (generator.generate seed) :=
        hCorrect (generator.generate seed)
      _ = EncodedTotalSearch.referenceDecision (s := threshold n)
            (generator.generate seed) :=
        hSlice n (generator.generate seed)
      _ = true := hReferenceTrue
  have hComplementFalse :
      C_DAG.eval complementCircuit (generator.generate seed) = false := by
    change DagCircuit.eval complementCircuit (generator.generate seed) = false
    simpa [complementCircuit, hCircuitTrue]
  have : (false : Bool) = true :=
    hComplementFalse.symm.trans hComplementAccepts
  cases this

/-- Uniform-mass above-half hitting is a convenient sufficient form of the
sharp witness-set premise. -/
theorem not_PpolyDAG_of_aboveHalf_DAGLocalGenerator_slices
    (L : Language) (threshold : Nat -> Nat)
    (hSlice : ∀ n : Nat, ∀ table : TruthTable n,
      L (Pnp3.Models.Partial.tableLen n) table =
        EncodedTotalSearch.referenceDecision (s := threshold n) table)
    (hAboveHalfHits : ∀ exponent : Nat,
      ∃ n : Nat,
      ∃ generator : DAGLocalGenerator n (threshold n),
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        HitsEveryAboveHalfDAGPredicate generator
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) :
    Not (PpolyDAG L) := by
  apply not_PpolyDAG_of_dense_DAGLocalGenerator_slices L threshold hSlice
  intro exponent
  rcases hAboveHalfHits exponent with
    ⟨n, generator, hLength, hHits⟩
  exact ⟨n, generator, hLength,
    hitsDenseDAGPredicates_of_hitsEveryAboveHalf generator _ hHits⟩

/-- The polynomial family size bound after adding one shared output-NOT gate
is always at least two, so it includes the constant-true circuit used by the
generator-elimination equivalence. -/
theorem two_le_ppolyDAGBound_with_outputNot (n exponent : Nat) :
    2 <= (Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1 := by
  have hPowerPositive :
      0 < (Pnp3.Models.Partial.tableLen n) ^ exponent := by
    simp [Pnp3.Models.Partial.tableLen]
  omega

/-- Generator-free direct `PpolyDAG` transfer.  It is enough that, at one suitable
slice for every polynomial exponent, every dense predicate computed by a DAG
within the output-NOT-adjusted size bound accepts some truth table having a
small standard-DAG circuit.

This formulation exposes the remaining obligation as a one-sided average-case
MCSP lower bound, without weights, epsilon, seed length, or generator syntax. -/
theorem not_PpolyDAG_of_dense_easy_intersection_slices
    (L : Language) (threshold : Nat -> Nat)
    (hSlice : ∀ n : Nat, ∀ table : TruthTable n,
      L (Pnp3.Models.Partial.tableLen n) table =
        EncodedTotalSearch.referenceDecision (s := threshold n) table)
    (hIntersection : ∀ exponent : Nat,
      ∃ n : Nat,
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        EveryDenseDAGPredicateAcceptsEasyTable n (threshold n)
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) :
    Not (PpolyDAG L) := by
  apply not_PpolyDAG_of_dense_DAGLocalGenerator_slices L threshold hSlice
  intro exponent
  rcases hIntersection exponent with ⟨n, hLength, hSemantic⟩
  have hMaxSize := two_le_ppolyDAGBound_with_outputNot n exponent
  rcases
      (exists_hitsDenseDAGLocalGenerator_iff_everyDenseAcceptsEasy
        n (threshold n)
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)
          hMaxSize).2 hSemantic with
    ⟨generator, hHits⟩
  exact ⟨n, generator, hLength, hHits⟩

end OneTapeMagnification
end Frontier
end Pnp4
