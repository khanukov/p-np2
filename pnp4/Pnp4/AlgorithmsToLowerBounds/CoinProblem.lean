import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

open scoped BigOperators

namespace Pnp4
namespace AlgorithmsToLowerBounds

/-- Weight contributed by a single Bernoulli sample with success bias `bias`. -/
def bernoulliBitWeight (bias : Rat) (b : Bool) : Rat :=
  if b then bias else 1 - bias

/--
Weight of a full bit-vector under the product distribution where each bit is 1
independently with probability `bias`.
-/
noncomputable def productBiasWeight
    (bias : Rat) {n : Nat} (x : BitVec n) : Rat :=
  ∏ i : Fin n, bernoulliBitWeight bias (x i)

/--
Acceptance probability of a Boolean algorithm under the product distribution of
 bias `bias`.
-/
noncomputable def acceptanceProbability
    (bias : Rat) {n : Nat} (A : BitVec n → Bool) : Rat :=
  ∑ x : BitVec n, if A x then productBiasWeight bias x else 0

/-- A Bernoulli bit weight is nonnegative when the bias is a probability. -/
theorem bernoulliBitWeight_nonneg
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (b : Bool) :
    0 ≤ bernoulliBitWeight bias b := by
  cases b <;> simp [bernoulliBitWeight] <;> linarith

/-- Product-distribution weights are nonnegative for valid Bernoulli biases. -/
theorem productBiasWeight_nonneg
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    {n : Nat}
    (x : BitVec n) :
    0 ≤ productBiasWeight bias x := by
  classical
  unfold productBiasWeight
  exact Finset.prod_nonneg fun i _ =>
    bernoulliBitWeight_nonneg hBias_nonneg hBias_le_one (x i)

/--
One finite coin-problem instance: distinguish `lowBias` from `highBias` on
sample strings of length `sampleBits`.
-/
structure CoinProblemInstance where
  sampleBits : Nat
  lowBias : Rat
  highBias : Rat
  low_nonneg : 0 ≤ lowBias
  high_le_one : highBias ≤ 1
  bias_gap : lowBias < highBias

/-- The low-bias side of a valid coin instance is at most one. -/
theorem CoinProblemInstance.low_le_one
    (inst : CoinProblemInstance) :
    inst.lowBias ≤ 1 :=
  le_trans (le_of_lt inst.bias_gap) inst.high_le_one

/-- The high-bias side of a valid coin instance is nonnegative. -/
theorem CoinProblemInstance.high_nonneg
    (inst : CoinProblemInstance) :
    0 ≤ inst.highBias :=
  le_trans inst.low_nonneg (le_of_lt inst.bias_gap)

/-- Acceptance-gap of an algorithm on a fixed coin-problem instance. -/
noncomputable def acceptanceGap
    (inst : CoinProblemInstance)
    (A : BitVec inst.sampleBits → Bool) : Rat :=
  acceptanceProbability inst.highBias A -
    acceptanceProbability inst.lowBias A

/--
`A` solves the coin problem with advantage at least `adv` if its acceptance
probability under the higher-bias distribution exceeds that under the
lower-bias distribution by at least `adv`.
-/
noncomputable def SolvesCoinProblem
    (inst : CoinProblemInstance)
    (A : BitVec inst.sampleBits → Bool)
    (adv : Rat) : Prop :=
  adv ≤ acceptanceGap inst A

/--
Non-uniform class version of the same notion: some circuit in the class solves
the coin problem on the given input length.
-/
noncomputable def ClassSolvesCoinProblem
    (C : CircuitFamilyClass)
    (inst : CoinProblemInstance)
    (adv : Rat) : Prop :=
  ∃ c : C.Family inst.sampleBits,
    SolvesCoinProblem inst (fun x => C.eval c x) adv

/--
Size-bounded class version of coin solving: there is a circuit of size at most
`maxSize` with the required distinguishing advantage.
-/
noncomputable def BoundedClassSolvesCoinProblem
    (C : CircuitFamilyClass)
    (inst : CoinProblemInstance)
    (adv : Rat)
    (maxSize : Nat) : Prop :=
  ∃ c : C.Family inst.sampleBits,
    C.size c ≤ maxSize ∧
      SolvesCoinProblem inst (fun x => C.eval c x) adv

/-- A size-bounded solver is in particular an unbounded class-level solver. -/
theorem classSolvesCoinProblem_of_bounded
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {maxSize : Nat} :
    BoundedClassSolvesCoinProblem C inst adv maxSize →
      ClassSolvesCoinProblem C inst adv := by
  intro h
  rcases h with ⟨c, _hcSize, hSolve⟩
  exact ⟨c, hSolve⟩

/-- Acceptance probability depends only on the extensional Boolean function. -/
theorem acceptanceProbability_congr
    {n : Nat} {bias : Rat}
    {A B : BitVec n → Bool}
    (hAB : A = B) :
    acceptanceProbability bias A = acceptanceProbability bias B := by
  cases hAB
  rfl

/-- Acceptance probability is monotone under pointwise Boolean implication. -/
theorem acceptanceProbability_mono
    {n : Nat}
    {bias : Rat}
    {A B : BitVec n → Bool}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hAB : ∀ x : BitVec n, A x = true → B x = true) :
    acceptanceProbability bias A ≤ acceptanceProbability bias B := by
  classical
  unfold acceptanceProbability
  refine Finset.sum_le_sum ?_
  intro x _hx
  cases hA : A x
  · cases hB : B x
    · simp
    · simpa using productBiasWeight_nonneg hBias_nonneg hBias_le_one x
  · have hB : B x = true := hAB x hA
    simp [hB]

/-- Low-bias specialization of `acceptanceProbability_mono`. -/
theorem acceptanceProbability_mono_lowBias
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    (hAB : ∀ x : BitVec inst.sampleBits, A x = true → B x = true) :
    acceptanceProbability inst.lowBias A ≤
      acceptanceProbability inst.lowBias B :=
  acceptanceProbability_mono inst.low_nonneg inst.low_le_one hAB

/-- High-bias specialization of `acceptanceProbability_mono`. -/
theorem acceptanceProbability_mono_highBias
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    (hAB : ∀ x : BitVec inst.sampleBits, A x = true → B x = true) :
    acceptanceProbability inst.highBias A ≤
      acceptanceProbability inst.highBias B :=
  acceptanceProbability_mono inst.high_nonneg inst.high_le_one hAB

/-- Coin-problem solvability is extensional in the underlying Boolean function. -/
theorem solvesCoinProblem_congr
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    {adv : Rat}
    (hAB : A = B)
    (hSolve : SolvesCoinProblem inst A adv) :
    SolvesCoinProblem inst B adv := by
  simpa [SolvesCoinProblem, acceptanceGap, hAB] using hSolve

/--
A reusable probability-gap criterion for solving one finite coin-problem
instance.

If the algorithm's low-bias acceptance is at most `lowAcceptanceUpper`, its
high-bias acceptance is at least `highAcceptanceLower`, and those bounds leave
the requested advantage gap, then the algorithm solves the coin problem.
-/
theorem solvesCoinProblem_of_acceptanceProbability_bounds
    {inst : CoinProblemInstance}
    {A : BitVec inst.sampleBits → Bool}
    {adv lowAcceptanceUpper highAcceptanceLower : Rat}
    (hLow :
      acceptanceProbability inst.lowBias A ≤ lowAcceptanceUpper)
    (hHigh :
      highAcceptanceLower ≤ acceptanceProbability inst.highBias A)
    (hGap :
      adv + lowAcceptanceUpper ≤ highAcceptanceLower) :
    SolvesCoinProblem inst A adv := by
  unfold SolvesCoinProblem acceptanceGap
  linarith

/--
Standard uniform-vs-biased instance:
distinguish `1/2 - ε` from `1/2` on strings of length `sampleBits`.
-/
def uniformVsBiasedCoinInstance
    (sampleBits : Nat)
    (ε : Rat)
    (hε_pos : 0 < ε)
    (hε_le_half : ε ≤ (1 : Rat) / 2) :
    CoinProblemInstance where
  sampleBits := sampleBits
  lowBias := (1 : Rat) / 2 - ε
  highBias := (1 : Rat) / 2
  low_nonneg := by
    linarith
  high_le_one := by
    norm_num
  bias_gap := by
    linarith

/--
Paper-facing regime used after the Claim 2.4 translation step in
Golovnev-Ilango-Impagliazzo-Kabanets-Kolokolova-Tal:
distinguish bias `(1 - ε) / 2` from the fair coin `1 / 2`.
-/
def halfVsFairCoinInstance
    (sampleBits : Nat)
    (ε : Rat)
    (hε_pos : 0 < ε)
    (hε_le_one : ε ≤ (1 : Rat)) :
    CoinProblemInstance where
  sampleBits := sampleBits
  lowBias := ((1 : Rat) - ε) / 2
  highBias := (1 : Rat) / 2
  low_nonneg := by
    linarith
  high_le_one := by
    norm_num
  bias_gap := by
    linarith

/-- Low-bias side of the paper-facing half-vs-fair regime is nonnegative. -/
theorem halfVsFair_lowBias_nonneg
    {ε : Rat}
    (hε_le_one : ε ≤ (1 : Rat)) :
    0 ≤ ((1 : Rat) - ε) / 2 := by
  linarith

/-- The paper-facing half-vs-fair regime has a genuine gap when `ε > 0`. -/
theorem halfVsFair_lowBias_lt_fair
    {ε : Rat}
    (hε_pos : 0 < ε) :
    ((1 : Rat) - ε) / 2 < (1 : Rat) / 2 := by
  linarith

end AlgorithmsToLowerBounds
end Pnp4
