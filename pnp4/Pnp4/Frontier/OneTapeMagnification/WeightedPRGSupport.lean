import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Signed weighted approximation still yields a support hitting set

A weighted pseudorandom generator may attach negative rational weights to its
seeds.  Such weights do not directly define the ordinary seed distribution
used by a randomized PRG argument.  They nevertheless suffice for a
deterministic hitting-set endpoint.

If a Boolean predicate vanishes on every generator output, its weighted seed
average is exactly zero, regardless of the signs or magnitudes of the weights.
Consequently an additive approximation with error `epsilon` must hit every
predicate whose uniform average is strictly larger than `epsilon`.

This elementary observation is the precise bridge that makes signed WPRG
technology relevant to the deterministic local-HSG capstone.  It does not
construct a WPRG for the coherent CHMY path family, nor prove the required
fixed-seed circuit locality.
-/

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-- Embed a Boolean acceptance bit into the rationals. -/
def boolIndicator (value : Bool) : Rat :=
  if value then 1 else 0

/-- Exact uniform average of a Boolean predicate on a finite input type. -/
def uniformPredicateAverage {Input : Type*} [Fintype Input]
    (predicate : Input → Bool) : Rat :=
  (∑ input : Input, boolIndicator (predicate input)) /
    (Fintype.card Input : Rat)

/-- Exact weighted seed average.  No positivity or normalization condition is
imposed on `weight`; the support implication below needs neither. -/
def weightedGeneratorAverage
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool) : Rat :=
  (∑ seed : Seed,
      weight seed * boolIndicator (predicate (generator seed))) /
    (Fintype.card Seed : Rat)

/-- If every generator output is rejected, the weighted average is zero even
when some weights are negative. -/
theorem weightedGeneratorAverage_eq_zero_of_support_rejects
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool)
    (hRejects : ∀ seed, predicate (generator seed) = false) :
    weightedGeneratorAverage generator weight predicate = 0 := by
  simp [weightedGeneratorAverage, boolIndicator, hRejects]

/-- If every seed carrying nonzero weight is rejected, the weighted average is
zero.  Zero-weight image points are irrelevant to the weighted support. -/
theorem weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
    {Seed Input : Type*} [Fintype Seed]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool)
    (hRejects :
      ∀ seed, weight seed ≠ 0 → predicate (generator seed) = false) :
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

/-- Any signed weighted approximation with error below the uniform acceptance
mass has an accepting seed carrying nonzero weight in its support. -/
theorem weightedApproximation_support_hits
    {Seed Input : Type*} [Fintype Seed] [Fintype Input]
    [Nonempty Seed] [Nonempty Input]
    (generator : Seed → Input) (weight : Seed → Rat)
    (predicate : Input → Bool) (epsilon : Rat)
    (hEpsilon : 0 ≤ epsilon)
    (hApprox :
      abs (uniformPredicateAverage predicate -
        weightedGeneratorAverage generator weight predicate) ≤ epsilon)
    (hMass : epsilon < uniformPredicateAverage predicate) :
    ∃ seed, weight seed ≠ 0 ∧ predicate (generator seed) = true := by
  by_contra hNoHit
  have hRejects :
      ∀ seed, weight seed ≠ 0 → predicate (generator seed) = false := by
    intro seed
    intro hWeight
    cases hValue : predicate (generator seed) with
    | false => rfl
    | true => exact False.elim (hNoHit ⟨seed, hWeight, hValue⟩)
  have hWeightedZero :
      weightedGeneratorAverage generator weight predicate = 0 :=
    weightedGeneratorAverage_eq_zero_of_nonzero_support_rejects
      generator weight predicate hRejects
  have hUniformPositive : 0 < uniformPredicateAverage predicate :=
    lt_of_le_of_lt hEpsilon hMass
  rw [hWeightedZero, sub_zero, abs_of_pos hUniformPositive] at hApprox
  exact (not_lt_of_ge hApprox) hMass

end OneTapeMagnification
end Frontier
end Pnp4
