import Complexity.DagCompose
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Finite signed support and reverse one-sided fooling

This module isolates the finite argument behind signed weighted generators.
Weights are rational, may be negative, and need not be normalized.  A reverse
one-sided approximation can hit a predicate only through a seed of nonzero
weight.  Conversely, support hitting is witnessed by one explicit nonnegative
constant weight, even when the requested error is negative.

The result is generic in the finite seed type and uses only the repository's
current `DagCircuit` model.  It has no magnification or complexity-separation
dependency.
-/

open scoped BigOperators

namespace Pnp4.Frontier.SignedSupportNoGo

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-- Embed a Boolean acceptance bit into the rationals. -/
def boolIndicator (value : Bool) : Rat :=
  if value then 1 else 0

/-- Exact uniform average of a Boolean predicate on a finite type. -/
def uniformPredicateAverage {Input : Type*} [Fintype Input]
    (predicate : Input → Bool) : Rat :=
  (∑ input : Input, boolIndicator (predicate input)) /
    (Fintype.card Input : Rat)

/-- Exact weighted seed average.  No sign or normalization condition is
imposed on `weight`. -/
def weightedGeneratorAverage
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool) : Rat :=
  (∑ seed : Seed,
      weight seed * boolIndicator (predicate (generator seed))) /
    (Fintype.card Seed : Rat)

@[simp] theorem boolIndicator_nonneg (value : Bool) :
    0 ≤ boolIndicator value := by
  cases value <;> simp [boolIndicator]

@[simp] theorem boolIndicator_le_one (value : Bool) :
    boolIndicator value ≤ 1 := by
  cases value <;> simp [boolIndicator]

/-- A Boolean uniform average lies in `[0,1]`.  This includes an empty input
type, where Lean's field convention makes the average zero. -/
theorem uniformPredicateAverage_mem_unitInterval
    {Input : Type*} [Fintype Input] (predicate : Input → Bool) :
    0 ≤ uniformPredicateAverage predicate ∧
      uniformPredicateAverage predicate ≤ 1 := by
  classical
  by_cases hCard : Fintype.card Input = 0
  · simp [uniformPredicateAverage, hCard]
  · have hDenPositive : (0 : Rat) < (Fintype.card Input : Rat) := by
      exact_mod_cast Nat.pos_of_ne_zero hCard
    have hSumNonnegative :
        (0 : Rat) ≤ ∑ input : Input, boolIndicator (predicate input) :=
      Finset.sum_nonneg fun input _ => boolIndicator_nonneg _
    have hSumAtMostCard :
        (∑ input : Input, boolIndicator (predicate input)) ≤
          (Fintype.card Input : Rat) := by
      have hTermwise := Finset.sum_le_sum fun input
        (_ : input ∈ (Finset.univ : Finset Input)) =>
          boolIndicator_le_one (predicate input)
      simpa using hTermwise
    constructor
    · exact div_nonneg hSumNonnegative hDenPositive.le
    · exact (div_le_one hDenPositive).2 hSumAtMostCard

theorem uniformPredicateAverage_le_one
    {Input : Type*} [Fintype Input] (predicate : Input → Bool) :
    uniformPredicateAverage predicate ≤ 1 :=
  (uniformPredicateAverage_mem_unitInterval predicate).2

/-- If every seed carrying nonzero weight is rejected, its weighted average is
zero. -/
theorem weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool)
    (hRejects : ∀ seed, weight seed ≠ 0 →
      predicate (generator seed) = false) :
    weightedGeneratorAverage generator weight predicate = 0 := by
  unfold weightedGeneratorAverage
  have hSum :
      (∑ seed : Seed,
        weight seed * boolIndicator (predicate (generator seed))) = 0 := by
    apply Finset.sum_eq_zero
    intro seed _
    by_cases hWeight : weight seed = 0
    · simp [hWeight]
    · simp [hRejects seed hWeight, boolIndicator]
  rw [hSum]
  simp

/-- A reverse one-sided approximation below the uniform mass has an accepting
seed of nonzero weight.  No sign, normalization, inhabitation, or error-sign
premise is needed. -/
theorem lowerWeightedApproximation_support_hits
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool) (epsilon : Rat)
    (hApprox :
      uniformPredicateAverage predicate -
        weightedGeneratorAverage generator weight predicate ≤ epsilon)
    (hMass : epsilon < uniformPredicateAverage predicate) :
    ∃ seed, weight seed ≠ 0 ∧ predicate (generator seed) = true := by
  by_contra hNoHit
  have hRejects : ∀ seed, weight seed ≠ 0 →
      predicate (generator seed) = false := by
    intro seed hWeight
    cases hValue : predicate (generator seed) with
    | false => rfl
    | true => exact False.elim (hNoHit ⟨seed, hWeight, hValue⟩)
  have hZero := weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
    generator weight predicate hRejects
  rw [hZero, sub_zero] at hApprox
  exact (not_lt_of_ge hApprox) hMass

private theorem scaledConstantWeight_nonneg
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (predicate : Input → Bool)
    (scale : Rat) (hScale : 0 ≤ scale) :
    0 ≤ weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate := by
  classical
  unfold weightedGeneratorAverage
  apply div_nonneg
  · exact Finset.sum_nonneg fun seed _ =>
      mul_nonneg (mul_nonneg (by positivity) hScale) (boolIndicator_nonneg _)
  · positivity

private theorem scale_le_scaledConstantWeight_of_hit
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (predicate : Input → Bool)
    (scale : Rat) (hScale : 0 ≤ scale)
    (hHit : ∃ seed, predicate (generator seed) = true) :
    scale ≤ weightedGeneratorAverage generator
      (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate := by
  classical
  rcases hHit with ⟨seed, hAccepts⟩
  letI : Nonempty Seed := ⟨seed⟩
  have hCard : (Fintype.card Seed : Rat) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hFormula :
      weightedGeneratorAverage generator
          (fun _ : Seed => (Fintype.card Seed : Rat) * scale) predicate =
        scale * ∑ other : Seed,
          boolIndicator (predicate (generator other)) := by
    unfold weightedGeneratorAverage
    rw [← Finset.mul_sum]
    apply (div_eq_iff hCard).2
    ring
  rw [hFormula]
  have hSingle :
      boolIndicator (predicate (generator seed)) ≤
        ∑ other : Seed, boolIndicator (predicate (generator other)) :=
    Finset.single_le_sum
      (fun other _ => boolIndicator_nonneg (predicate (generator other)))
      (Finset.mem_univ seed)
  have hOne : (1 : Rat) ≤
      ∑ other : Seed, boolIndicator (predicate (generator other)) := by
    simpa [boolIndicator, hAccepts] using hSingle
  simpa using mul_le_mul_of_nonneg_left hOne hScale

/-- Reverse one-sided fooling of every standard DAG up to an explicit size
bound. -/
def ReverseOneSidedFoolsDAG
    {Seed : Type*} [Fintype Seed] {N : Nat}
    (generator : Seed → Bitstring N) (weight : Seed → Rat)
    (maxSize : Nat) (epsilon : Rat) : Prop :=
  ∀ circuit : DagCircuit N, size circuit ≤ maxSize →
    uniformPredicateAverage (fun input : Bitstring N => eval circuit input) -
      weightedGeneratorAverage generator weight
        (fun input : Bitstring N => eval circuit input) ≤ epsilon

/-- Support-only formulation: every bounded DAG predicate of uniform mass
above `epsilon` accepts a generator output. -/
def HitsDAGPredicatesAboveUniformMass
    {Seed : Type*} [Fintype Seed] {N : Nat}
    (generator : Seed → Bitstring N) (maxSize : Nat) (epsilon : Rat) : Prop :=
  ∀ circuit : DagCircuit N, size circuit ≤ maxSize →
    epsilon < uniformPredicateAverage
      (fun input : Bitstring N => eval circuit input) →
    ∃ seed, eval circuit (generator seed) = true

/-- For every rational error, existence of arbitrary signed, unnormalized
weights is exactly support hitting above that error mass. -/
theorem exists_reverseOneSidedFoolsDAG_iff_hits
    {Seed : Type*} [Fintype Seed] {N : Nat}
    (generator : Seed → Bitstring N) (maxSize : Nat) (epsilon : Rat) :
    (∃ weight : Seed → Rat,
        ReverseOneSidedFoolsDAG generator weight maxSize epsilon) ↔
      HitsDAGPredicatesAboveUniformMass generator maxSize epsilon := by
  constructor
  · rintro ⟨weight, hFools⟩ circuit hSize hMass
    rcases lowerWeightedApproximation_support_hits generator weight
        (fun input : Bitstring N => eval circuit input) epsilon
        (hFools circuit hSize) hMass with
      ⟨seed, _, hAccepts⟩
    exact ⟨seed, hAccepts⟩
  · intro hHits
    let scale : Rat := abs epsilon + 2
    refine ⟨(fun _ : Seed => (Fintype.card Seed : Rat) * scale), ?_⟩
    intro circuit hSize
    let predicate : Bitstring N → Bool := fun input => eval circuit input
    have hScale : (0 : Rat) ≤ scale := by
      dsimp [scale]
      positivity
    by_cases hMass : epsilon < uniformPredicateAverage predicate
    · have hLarge := scale_le_scaledConstantWeight_of_hit
        generator predicate scale hScale (hHits circuit hSize hMass)
      have hAtMostOne := uniformPredicateAverage_le_one predicate
      have hAbs := neg_le_abs epsilon
      dsimp [scale] at hLarge
      linarith
    · have hUniform : uniformPredicateAverage predicate ≤ epsilon :=
        le_of_not_gt hMass
      have hWeighted := scaledConstantWeight_nonneg
        generator predicate scale hScale
      linarith

end Pnp4.Frontier.SignedSupportNoGo
