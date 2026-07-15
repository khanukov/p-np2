import Pnp4.Frontier.OneTapeMagnification.DPTWZeroTailJointLocality
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGSupport

/-!
# Exact survivor cost of deleting the DPTW packed tail

The DPTW Forbes--Kelley generator ends its restriction recursion with a
packed random tail.  `DPTWZeroTailJointLocality` deletes that tail in order to
obtain a small joint coordinate DAG.  This file proves the exact, purely
Boolean cost of that deletion.

For every fixed prefix seed, coordinate, and arbitrary terminal truth table,

`withTail = zeroTail XOR (survivesEveryBLevel AND terminalTail)`.

Thus deleting the tail can change an arbitrary Boolean test only on prefix
seeds for which some coordinate survives every `B` level.  The final theorem
bounds the exact rational difference of the two uniform test averages by the
sum of the per-coordinate survival probabilities.  It assumes no branching-
program model, independence, pseudorandomness, or lower bound.

This is the deterministic/probabilistic bookkeeping used implicitly when the
fooling proof of DPTW Theorem 4.14 bounds the probability that any variable
remains alive.  It does not formalize their restriction lemma or claim that
the canonical one-tape aggregate is a deterministic AOBP.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

open Pnp3.ComplexityInterfaces
open StreamingMagnification
open StreamingMagnification.TotalSearch

/-! ## Recursion with an arbitrary terminal tail -/

/-- The terminal-tail version of the retained DPTW `A/B` recursion.

Unlike `dptwZeroTailGenerate`, the last `B` block is semantically live: at the
last level it masks the supplied terminal truth table.  This definition is
pointwise and places no distributional restriction on that table.
-/
def dptwGenerateWithTail
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s) :
    (levelsAfterFirst : Nat) ->
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) ->
      TruthTable n -> TruthTable n
  | 0, seed, tail => fun index =>
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index && tail index)
  | levelsAfterFirst + 1, seed, tail => fun index =>
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index &&
          dptwGenerateWithTail a b levelsAfterFirst
            (dptwTailSeed seed) tail index)

/-- A coordinate survives precisely when every retained `B` block on its
recursive path is one. -/
def dptwSurvivesAllBLevels
    {n s : Nat} (b : DPTWCoordinatePrimitive n s) :
    (levelsAfterFirst : Nat) ->
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) ->
      Fin (2 ^ n) -> Bool
  | 0, seed, index =>
      b.generate (dptwFirstBSeed seed) index
  | levelsAfterFirst + 1, seed, index =>
      b.generate (dptwFirstBSeed seed) index &&
        dptwSurvivesAllBLevels b levelsAfterFirst
          (dptwTailSeed seed) index

@[simp] theorem dptwGenerateWithTail_final
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (seed : FiniteBitTape (1 * (s + s))) (tail : TruthTable n)
    (index : Fin (2 ^ n)) :
    dptwGenerateWithTail a b 0 seed tail index =
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index && tail index) :=
  rfl

@[simp] theorem dptwGenerateWithTail_step
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (tail : TruthTable n) (index : Fin (2 ^ n)) :
    dptwGenerateWithTail a b (levelsAfterFirst + 1) seed tail index =
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index &&
          dptwGenerateWithTail a b levelsAfterFirst
            (dptwTailSeed seed) tail index) :=
  rfl

@[simp] theorem dptwSurvivesAllBLevels_final
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (seed : FiniteBitTape (1 * (s + s))) (index : Fin (2 ^ n)) :
    dptwSurvivesAllBLevels b 0 seed index =
      b.generate (dptwFirstBSeed seed) index :=
  rfl

@[simp] theorem dptwSurvivesAllBLevels_step
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin (2 ^ n)) :
    dptwSurvivesAllBLevels b (levelsAfterFirst + 1) seed index =
      (b.generate (dptwFirstBSeed seed) index &&
        dptwSurvivesAllBLevels b levelsAfterFirst
          (dptwTailSeed seed) index) :=
  rfl

/-! ## Exact tail-influence identity -/

private theorem xor_and_xor_and
    (a b zero survives tail : Bool) :
    Bool.xor a (b && Bool.xor zero (survives && tail)) =
      Bool.xor (Bool.xor a (b && zero))
        ((b && survives) && tail) := by
  cases a <;> cases b <;> cases zero <;> cases survives <;>
    cases tail <;> rfl

/-- The full terminal-tail dependence is one surviving affine Boolean term.
This is the exact pointwise reason that a killed coordinate is independent of
the packed tail. -/
theorem dptwGenerateWithTail_eq_xor_zeroTail_survivor
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (tail : TruthTable n) (index : Fin (2 ^ n)) :
    dptwGenerateWithTail a b levelsAfterFirst seed tail index =
      Bool.xor
        (dptwZeroTailGenerate a b levelsAfterFirst seed index)
        (dptwSurvivesAllBLevels b levelsAfterFirst seed index &&
          tail index) := by
  induction levelsAfterFirst with
  | zero => rfl
  | succ levelsAfterFirst ih =>
      rw [dptwGenerateWithTail_step, ih,
        dptwZeroTailGenerate_step, dptwSurvivesAllBLevels_step]
      exact xor_and_xor_and _ _ _ _ _

/-- Supplying the all-zero terminal table recovers the earlier zero-tail
recursion extensionally. -/
theorem dptwGenerateWithTail_zero_eq_zeroTail
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s))) :
    dptwGenerateWithTail a b levelsAfterFirst seed (fun _ => false) =
      dptwZeroTailGenerate a b levelsAfterFirst seed := by
  funext index
  rw [dptwGenerateWithTail_eq_xor_zeroTail_survivor]
  simp

/-- If no coordinate survives, every possible terminal tail gives exactly
the zero-tail output. -/
theorem dptwGenerateWithTail_eq_zeroTail_of_all_killed
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (tail : TruthTable n)
    (hKilled : forall index,
      dptwSurvivesAllBLevels b levelsAfterFirst seed index = false) :
    dptwGenerateWithTail a b levelsAfterFirst seed tail =
      dptwZeroTailGenerate a b levelsAfterFirst seed := by
  funext index
  rw [dptwGenerateWithTail_eq_xor_zeroTail_survivor,
    hKilled index]
  simp

/-- Coordinate-level disagreement is equivalent to a surviving terminal one.
There is no cancellation hidden in the recursive XORs. -/
theorem dptwGenerateWithTail_ne_zeroTail_iff
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (tail : TruthTable n) (index : Fin (2 ^ n)) :
    dptwGenerateWithTail a b levelsAfterFirst seed tail index ≠
        dptwZeroTailGenerate a b levelsAfterFirst seed index <->
      dptwSurvivesAllBLevels b levelsAfterFirst seed index = true /\
        tail index = true := by
  rw [dptwGenerateWithTail_eq_xor_zeroTail_survivor]
  generalize
    dptwZeroTailGenerate a b levelsAfterFirst seed index = zeroValue
  generalize
    dptwSurvivesAllBLevels b levelsAfterFirst seed index = survivesValue
  generalize tail index = tailValue
  cases zeroValue <;> cases survivesValue <;> cases tailValue <;> decide

/-- Whole-output disagreement has an explicit surviving coordinate witness. -/
theorem dptwGenerateWithTail_ne_zeroTail_iff_exists
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (tail : TruthTable n) :
    dptwGenerateWithTail a b levelsAfterFirst seed tail ≠
        dptwZeroTailGenerate a b levelsAfterFirst seed <->
      exists index,
        dptwSurvivesAllBLevels b levelsAfterFirst seed index = true /\
          tail index = true := by
  constructor
  . intro hDifferent
    by_contra hNoWitness
    push_neg at hNoWitness
    apply hDifferent
    funext index
    by_contra hCoordinate
    exact hNoWitness index
      ((dptwGenerateWithTail_ne_zeroTail_iff
        a b levelsAfterFirst seed tail index).1 hCoordinate).1
      ((dptwGenerateWithTail_ne_zeroTail_iff
        a b levelsAfterFirst seed tail index).1 hCoordinate).2
  . rintro ⟨index, hSurvives, hTail⟩ hEqual
    have hCoordinate := congrFun hEqual index
    have hDifferent :=
      (dptwGenerateWithTail_ne_zeroTail_iff
        a b levelsAfterFirst seed tail index).2
          ⟨hSurvives, hTail⟩
    exact hDifferent hCoordinate

/-! ## Uniform-average disagreement bounds -/

/-- Uniform Boolean averages can differ only on inputs on which the two
predicates disagree.  The inhabited hypothesis avoids the zero-cardinality
division edge; all finite bit-tape seed spaces satisfy it. -/
theorem abs_uniformPredicateAverage_sub_le_disagreement
    {Input : Type*} [Fintype Input] [Nonempty Input]
    (left right : Input -> Bool) :
    abs (uniformPredicateAverage left -
      uniformPredicateAverage right) <=
        uniformPredicateAverage
          (fun input => Bool.xor (left input) (right input)) := by
  classical
  have hCardPositive : (0 : Rat) < (Fintype.card Input : Rat) := by
    exact_mod_cast Fintype.card_pos
  unfold uniformPredicateAverage
  rw [← sub_div, abs_div, abs_of_pos hCardPositive]
  apply (div_le_div_iff_of_pos_right hCardPositive).2
  calc
    abs ((∑ input : Input, boolIndicator (left input)) -
        ∑ input : Input, boolIndicator (right input)) =
        abs (∑ input : Input,
          (boolIndicator (left input) - boolIndicator (right input))) := by
            rw [Finset.sum_sub_distrib]
    _ <= ∑ input : Input,
        abs (boolIndicator (left input) -
          boolIndicator (right input)) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ input : Input,
        boolIndicator (Bool.xor (left input) (right input)) := by
          apply Finset.sum_congr rfl
          intro input _
          cases left input <;> cases right input <;>
            norm_num [boolIndicator]

/-- Pointwise Boolean implication is monotone for exact uniform averages. -/
theorem uniformPredicateAverage_mono
    {Input : Type*} [Fintype Input]
    {left right : Input -> Bool}
    (hImp : forall input, left input = true -> right input = true) :
    uniformPredicateAverage left <= uniformPredicateAverage right := by
  classical
  unfold uniformPredicateAverage
  apply div_le_div_of_nonneg_right
  . apply Finset.sum_le_sum
    intro input _
    cases hLeft : left input
    . cases hRight : right input <;>
        norm_num [boolIndicator, hRight]
    . have hRight := hImp input hLeft
      simp [boolIndicator, hRight]
  . positivity

/-- Union bound for exact finite uniform Boolean averages. -/
theorem uniformPredicateAverage_exists_le_sum
    {Seed Index : Type*} [Fintype Seed] [Fintype Index]
    (event : Seed -> Index -> Bool) (witness : Seed -> Bool)
    (hWitness : forall seed,
      witness seed = true <-> exists index, event seed index = true) :
    uniformPredicateAverage witness <=
      ∑ index : Index,
        uniformPredicateAverage (fun seed => event seed index) := by
  classical
  unfold uniformPredicateAverage
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_le_div_of_nonneg_right
  . apply Finset.sum_le_sum
    intro seed _
    cases hValue : witness seed
    . simp only [boolIndicator, Bool.false_eq_true, if_false]
      positivity
    . obtain ⟨index, hEvent⟩ := (hWitness seed).1 hValue
      have hTerm : (1 : Rat) <=
          ∑ index : Index, boolIndicator (event seed index) := by
        calc
          (1 : Rat) = boolIndicator (event seed index) := by
            simp [boolIndicator, hEvent]
          _ <= ∑ index : Index,
              boolIndicator (event seed index) := by
            have hNonnegative : ∀ other : Index,
                other ∈ (Finset.univ : Finset Index) ->
                  (0 : Rat) <= boolIndicator (event seed other) := by
              intro other _
              cases event seed other <;> norm_num [boolIndicator]
            exact Finset.single_le_sum hNonnegative
              (Finset.mem_univ index)
      change (1 : Rat) <=
        ∑ index : Index, boolIndicator (event seed index)
      exact hTerm
  . exact_mod_cast Nat.zero_le (Fintype.card Seed)

/-- Deleting the terminal tail changes the expectation of any Boolean test by
at most the union-bound sum of the per-coordinate survival probabilities.

The terminal table may depend arbitrarily on the prefix seed.  Dropping its
bits only enlarges the bad event, so the right side contains survival alone.
-/
theorem dptwZeroTail_test_average_sub_le_sum_survival
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (tail : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) ->
      TruthTable n)
    (test : TruthTable n -> Bool) :
    abs
        (uniformPredicateAverage (fun seed =>
            test (dptwGenerateWithTail a b levelsAfterFirst seed
              (tail seed))) -
          uniformPredicateAverage (fun seed =>
            test (dptwZeroTailGenerate a b levelsAfterFirst seed))) <=
      ∑ index : Fin (2 ^ n),
        uniformPredicateAverage (fun seed =>
          dptwSurvivesAllBLevels b levelsAfterFirst seed index) := by
  let fullTest :
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) -> Bool :=
    fun seed => test
      (dptwGenerateWithTail a b levelsAfterFirst seed (tail seed))
  let zeroTest :
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) -> Bool :=
    fun seed => test (dptwZeroTailGenerate a b levelsAfterFirst seed)
  let survivesSome :
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) -> Bool :=
    fun seed => decide (exists index,
      dptwSurvivesAllBLevels b levelsAfterFirst seed index = true)
  calc
    abs (uniformPredicateAverage fullTest -
        uniformPredicateAverage zeroTest) <=
        uniformPredicateAverage
          (fun seed => Bool.xor (fullTest seed) (zeroTest seed)) :=
      abs_uniformPredicateAverage_sub_le_disagreement fullTest zeroTest
    _ <= uniformPredicateAverage survivesSome := by
      apply uniformPredicateAverage_mono
      intro seed hDifferent
      have hOutputs :
          dptwGenerateWithTail a b levelsAfterFirst seed (tail seed) ≠
            dptwZeroTailGenerate a b levelsAfterFirst seed := by
        intro hEqual
        have hTestEqual := congrArg test hEqual
        dsimp only [fullTest, zeroTest] at hDifferent
        rw [hTestEqual] at hDifferent
        cases hResult :
            test (dptwZeroTailGenerate a b levelsAfterFirst seed) <;>
          simp [hResult] at hDifferent
      obtain ⟨index, hSurvives, _hTail⟩ :=
        (dptwGenerateWithTail_ne_zeroTail_iff_exists
          a b levelsAfterFirst seed (tail seed)).1 hOutputs
      change decide (exists index,
        dptwSurvivesAllBLevels b levelsAfterFirst seed index = true) = true
      simp only [decide_eq_true_eq]
      exact ⟨index, hSurvives⟩
    _ <= ∑ index : Fin (2 ^ n),
        uniformPredicateAverage (fun seed =>
          dptwSurvivesAllBLevels b levelsAfterFirst seed index) := by
      simpa [survivesSome] using
        (uniformPredicateAverage_exists_le_sum
          (fun seed index =>
            dptwSurvivesAllBLevels b levelsAfterFirst seed index)
          survivesSome (by
            intro seed
            simp [survivesSome]))

/-- Convenient scalar corollary.  A uniform per-coordinate survival bound
`delta` costs at most `2^n * delta` for every Boolean test. -/
theorem dptwZeroTail_test_average_sub_le_tableLength_mul
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (tail : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) ->
      TruthTable n)
    (test : TruthTable n -> Bool) (delta : Rat)
    (hSurvival : forall index,
      uniformPredicateAverage (fun seed =>
        dptwSurvivesAllBLevels b levelsAfterFirst seed index) <= delta) :
    abs
        (uniformPredicateAverage (fun seed =>
            test (dptwGenerateWithTail a b levelsAfterFirst seed
              (tail seed))) -
          uniformPredicateAverage (fun seed =>
            test (dptwZeroTailGenerate a b levelsAfterFirst seed))) <=
      (2 ^ n : Rat) * delta := by
  calc
    abs
        (uniformPredicateAverage (fun seed =>
            test (dptwGenerateWithTail a b levelsAfterFirst seed
              (tail seed))) -
          uniformPredicateAverage (fun seed =>
            test (dptwZeroTailGenerate a b levelsAfterFirst seed))) <=
      ∑ index : Fin (2 ^ n),
        uniformPredicateAverage (fun seed =>
          dptwSurvivesAllBLevels b levelsAfterFirst seed index) :=
        dptwZeroTail_test_average_sub_le_sum_survival
          a b levelsAfterFirst tail test
    _ <= ∑ _index : Fin (2 ^ n), delta := by
      exact Finset.sum_le_sum fun index _ => hSurvival index
    _ = (2 ^ n : Rat) * delta := by simp

end OneTapeMagnification
end Frontier
end Pnp4
