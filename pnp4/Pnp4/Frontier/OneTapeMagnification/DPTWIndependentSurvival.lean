import Pnp4.Frontier.OneTapeMagnification.DPTWZeroTailSurvivorBound

/-!
# Exact independent-level survival for the retained DPTW seed layout

`DPTWZeroTailSurvivorBound` reduces the cost of deleting the packed terminal
tail to the probability that a coordinate survives every `B` block.  This
file closes the elementary independence step for the explicit contiguous seed
layout used by that recursion.

If one primitive `B` block is one at a fixed coordinate with exact uniform
probability `rho`, then `levelsAfterFirst + 1` disjoint uniform blocks all
survive with exact probability `rho ^ (levelsAfterFirst + 1)`.  The proof is
finite counting over Boolean tapes; it assumes neither pseudorandomness nor a
branching-program theorem.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

open Pnp3.ComplexityInterfaces
open StreamingMagnification
open StreamingMagnification.TotalSearch

/-! ## Uniform finite products and tape splitting -/

/-- Split a Boolean tape at an additive boundary. -/
def finiteBitTapeAddEquiv (left right : Nat) :
    FiniteBitTape (left + right) ≃
      FiniteBitTape left × FiniteBitTape right where
  toFun tape :=
    (fun index => tape (Fin.castAdd right index),
      fun index => tape (Fin.natAdd left index))
  invFun pair := Fin.addCases pair.1 pair.2
  left_inv tape := by
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro leftIndex
      simp
    · intro rightIndex
      simp
  right_inv pair := by
    apply Prod.ext
    · funext leftIndex
      simp
    · funext rightIndex
      simp

/-- Exact uniform averages are invariant under a finite equivalence. -/
theorem uniformPredicateAverage_comp_equiv
    {Input Output : Type*} [Fintype Input] [Fintype Output]
    (equiv : Input ≃ Output) (predicate : Output → Bool) :
    uniformPredicateAverage (fun input => predicate (equiv input)) =
      uniformPredicateAverage predicate := by
  unfold uniformPredicateAverage
  change (∑ input : Input, boolIndicator (predicate (equiv input))) /
      (Fintype.card Input : Rat) = _
  have hSum :
      (∑ input : Input, boolIndicator (predicate (equiv input))) =
        ∑ output : Output, boolIndicator (predicate output) :=
    Fintype.sum_equiv equiv _ _ (fun _ => rfl)
  rw [hSum]
  rw [Fintype.card_congr equiv]

@[simp] theorem boolIndicator_and (left right : Bool) :
    boolIndicator (left && right) =
      boolIndicator left * boolIndicator right := by
  cases left <;> cases right <;> simp [boolIndicator]

/-- The average of the constantly true predicate is one on a nonempty finite
type. -/
theorem uniformPredicateAverage_true
    {Input : Type*} [Fintype Input] [Nonempty Input] :
    uniformPredicateAverage (fun _input : Input => true) = 1 := by
  unfold uniformPredicateAverage
  simp [boolIndicator, Fintype.card_ne_zero]

/-- Independent Boolean predicates on the two factors of a uniform product
have exactly multiplicative averages. -/
theorem uniformPredicateAverage_prod_and
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    [Nonempty Left] [Nonempty Right]
    (left : Left → Bool) (right : Right → Bool) :
    uniformPredicateAverage
        (fun pair : Left × Right => left pair.1 && right pair.2) =
      uniformPredicateAverage left * uniformPredicateAverage right := by
  unfold uniformPredicateAverage
  rw [Fintype.sum_prod_type]
  simp_rw [boolIndicator_and]
  calc
    (∑ x : Left, ∑ y : Right,
        boolIndicator (left x) * boolIndicator (right y)) /
        (Fintype.card (Left × Right) : Rat) =
      ((∑ x : Left, boolIndicator (left x)) *
        ∑ y : Right, boolIndicator (right y)) /
        (Fintype.card (Left × Right) : Rat) := by
          congr 1
          simp_rw [← Finset.mul_sum]
          rw [Finset.sum_mul]
    _ = (∑ input : Left, boolIndicator (left input)) /
          (Fintype.card Left : Rat) *
        ((∑ input : Right, boolIndicator (right input)) /
          (Fintype.card Right : Rat)) := by
      rw [Fintype.card_prod]
      push_cast
      have hLeft : (Fintype.card Left : Rat) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      have hRight : (Fintype.card Right : Rat) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- Ignoring the left factor of a uniform product does not change an exact
uniform average. -/
theorem uniformPredicateAverage_prod_ignore_left
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    [Nonempty Left] [Nonempty Right]
    (predicate : Right → Bool) :
    uniformPredicateAverage
        (fun pair : Left × Right => predicate pair.2) =
      uniformPredicateAverage predicate := by
  calc
    uniformPredicateAverage
        (fun pair : Left × Right => predicate pair.2) =
      uniformPredicateAverage
        (fun pair : Left × Right => true && predicate pair.2) := by
          rfl
    _ = uniformPredicateAverage (fun _left : Left => true) *
        uniformPredicateAverage predicate :=
      uniformPredicateAverage_prod_and
        (fun _left : Left => true) predicate
    _ = uniformPredicateAverage predicate := by
      rw [uniformPredicateAverage_true, one_mul]

/-! ## The explicit DPTW block equivalence -/

/-- Read the first pair of primitive seed blocks. -/
def dptwFirstPairSeed
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    FiniteBitTape (s + s) :=
  fun index => seed <| Fin.mk index.val <| by
    have hPositive : 0 < levelsAfterFirst + 2 := by omega
    have hBlock : s + s ≤ (levelsAfterFirst + 2) * (s + s) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (s + s) hPositive
    exact lt_of_lt_of_le index.isLt hBlock

/-- Split the first pair of primitive seed blocks from the recursive tail.
This direct equivalence exposes the same offsets as `dptwFirstBSeed` and
`dptwTailSeed`, avoiding any probabilistic identification up to a cast. -/
def dptwFirstPairTailEquiv (levelsAfterFirst s : Nat) :
    FiniteBitTape ((levelsAfterFirst + 2) * (s + s)) ≃
      FiniteBitTape (s + s) ×
        FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) where
  toFun seed := (dptwFirstPairSeed seed, dptwTailSeed seed)
  invFun pair := fun index =>
    if hFirst : index.val < s + s then
      pair.1 ⟨index.val, hFirst⟩
    else
      pair.2 ⟨index.val - (s + s), by
        have hindex := index.isLt
        simp only [Nat.add_mul, Nat.one_mul] at hindex ⊢
        omega⟩
  left_inv seed := by
    funext index
    by_cases hFirst : index.val < s + s
    · simp [hFirst, dptwFirstPairSeed]
    · simp only [hFirst, ↓reduceDIte, dptwTailSeed]
      apply congrArg seed
      apply Fin.ext
      exact Nat.add_sub_of_le (Nat.le_of_not_gt hFirst)
  right_inv pair := by
    apply Prod.ext
    · funext index
      simp [dptwFirstPairSeed]
    · funext index
      simp only [dptwTailSeed]
      have hNotFirst : ¬ (s + s + index.val < s + s) := by omega
      simp only [hNotFirst, ↓reduceDIte]
      apply congrArg pair.2
      apply Fin.ext
      simp

theorem dptwFirstPairTailEquiv_fst_apply
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin (s + s)) :
    (dptwFirstPairTailEquiv levelsAfterFirst s seed).1 index =
      dptwFirstPairSeed seed index := by
  rfl

theorem dptwFirstPairTailEquiv_snd_apply
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin ((levelsAfterFirst + 1) * (s + s))) :
    (dptwFirstPairTailEquiv levelsAfterFirst s seed).2 index =
      dptwTailSeed seed index := by
  rfl

/-- Splitting the first pair once more exposes its independent `A` and `B`
primitive blocks. -/
def dptwASeedBSeedTailEquiv (levelsAfterFirst s : Nat) :
    FiniteBitTape ((levelsAfterFirst + 2) * (s + s)) ≃
      (FiniteBitTape s × FiniteBitTape s) ×
        FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) :=
  (dptwFirstPairTailEquiv levelsAfterFirst s).trans
    (Equiv.prodCongr (finiteBitTapeAddEquiv s s) (Equiv.refl _))

theorem dptwASeedBSeedTailEquiv_b_apply
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin s) :
    (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).1.2 index =
      dptwFirstBSeed seed index := by
  rfl

theorem dptwASeedBSeedTailEquiv_tail_apply
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin ((levelsAfterFirst + 1) * (s + s))) :
    (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).2 index =
      dptwTailSeed seed index := by
  rfl

/-! ## Exact survival power -/

/-- Remove the syntactic leading factor `1` from a Boolean tape length. -/
def finiteBitTapeOneMulEquiv (length : Nat) :
    FiniteBitTape (1 * length) ≃ FiniteBitTape length where
  toFun tape := fun index =>
    tape ⟨index.val, by simpa only [Nat.one_mul] using index.isLt⟩
  invFun tape := fun index =>
    tape ⟨index.val, by simpa only [Nat.one_mul] using index.isLt⟩
  left_inv tape := by
    funext index
    apply congrArg tape
    apply Fin.ext
    rfl
  right_inv tape := by
    funext index
    apply congrArg tape
    apply Fin.ext
    rfl

/-- At the final retained level, expose its `A` and `B` seed blocks despite
the syntactic `1 * (s + s)` in the recursion's type. -/
def dptwFinalASeedBSeedEquiv (s : Nat) :
    FiniteBitTape (1 * (s + s)) ≃
      FiniteBitTape s × FiniteBitTape s :=
  (finiteBitTapeOneMulEquiv (s + s)).trans
    (finiteBitTapeAddEquiv s s)

/-- At one retained level, averaging over the unused `A` seed leaves exactly
the marginal average of the `B` primitive. -/
theorem dptwSurvivesAllBLevels_zero_average
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (index : Fin (2 ^ n)) :
    uniformPredicateAverage (fun seed : FiniteBitTape (1 * (s + s)) =>
      dptwSurvivesAllBLevels b 0 seed index) =
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) := by
  let split := dptwFinalASeedBSeedEquiv s
  calc
    uniformPredicateAverage (fun seed : FiniteBitTape (1 * (s + s)) =>
        dptwSurvivesAllBLevels b 0 seed index) =
      uniformPredicateAverage (fun pair :
          FiniteBitTape s × FiniteBitTape s =>
        b.generate pair.2 index) := by
      calc
        uniformPredicateAverage (fun seed : FiniteBitTape (1 * (s + s)) =>
            dptwSurvivesAllBLevels b 0 seed index) =
          uniformPredicateAverage (fun seed : FiniteBitTape (1 * (s + s)) =>
            b.generate (split seed).2 index) := by
              apply congrArg
                (fun predicate : FiniteBitTape (1 * (s + s)) → Bool =>
                  uniformPredicateAverage predicate)
              funext seed
              rw [dptwSurvivesAllBLevels_final]
              apply congrArg
                (fun primitiveSeed => b.generate primitiveSeed index)
              funext seedIndex
              simp [split, dptwFinalASeedBSeedEquiv,
                finiteBitTapeOneMulEquiv, finiteBitTapeAddEquiv,
                dptwFirstBSeed]
              apply congrArg seed
              apply Fin.ext
              exact Nat.add_comm s seedIndex.val
        _ = uniformPredicateAverage (fun pair :
              FiniteBitTape s × FiniteBitTape s =>
            b.generate pair.2 index) :=
          uniformPredicateAverage_comp_equiv split
            (fun pair => b.generate pair.2 index)
    _ = uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) := by
      exact uniformPredicateAverage_prod_ignore_left
        (Left := FiniteBitTape s)
        (Right := FiniteBitTape s)
        (fun seed => b.generate seed index)

/-- Disjoint uniform `B` blocks make survival exactly multiplicative. -/
theorem dptwSurvivesAllBLevels_average_eq_pow
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) (index : Fin (2 ^ n)) :
    uniformPredicateAverage (fun seed :
        FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
      dptwSurvivesAllBLevels b levelsAfterFirst seed index) =
      (uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index)) ^ (levelsAfterFirst + 1) := by
  induction levelsAfterFirst with
  | zero =>
      simpa using dptwSurvivesAllBLevels_zero_average b index
  | succ levelsAfterFirst ih =>
      let split := dptwASeedBSeedTailEquiv levelsAfterFirst s
      calc
        uniformPredicateAverage (fun seed :
            FiniteBitTape ((levelsAfterFirst + 2) * (s + s)) =>
          dptwSurvivesAllBLevels b (levelsAfterFirst + 1) seed index) =
          uniformPredicateAverage (fun pair :
              (FiniteBitTape s × FiniteBitTape s) ×
                FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
            b.generate pair.1.2 index &&
              dptwSurvivesAllBLevels b levelsAfterFirst pair.2 index) := by
            symm
            rw [← uniformPredicateAverage_comp_equiv split]
            apply congrArg uniformPredicateAverage
            funext seed
            rw [dptwSurvivesAllBLevels_step]
            congr 2
        _ = uniformPredicateAverage (fun bSeed : FiniteBitTape s =>
              b.generate bSeed index) *
            uniformPredicateAverage (fun tailSeed :
                FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
              dptwSurvivesAllBLevels b levelsAfterFirst tailSeed index) := by
            calc
              uniformPredicateAverage (fun pair :
                  (FiniteBitTape s × FiniteBitTape s) ×
                    FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
                b.generate pair.1.2 index &&
                  dptwSurvivesAllBLevels b levelsAfterFirst pair.2 index) =
                uniformPredicateAverage (fun pair :
                    FiniteBitTape s × FiniteBitTape s =>
                  b.generate pair.2 index) *
                  uniformPredicateAverage (fun tailSeed :
                      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
                    dptwSurvivesAllBLevels b levelsAfterFirst
                      tailSeed index) :=
                uniformPredicateAverage_prod_and
                  (Left := FiniteBitTape s × FiniteBitTape s)
                  (Right := FiniteBitTape
                    ((levelsAfterFirst + 1) * (s + s)))
                  (fun pair => b.generate pair.2 index)
                  (fun tailSeed => dptwSurvivesAllBLevels b
                    levelsAfterFirst tailSeed index)
              _ = uniformPredicateAverage (fun bSeed : FiniteBitTape s =>
                    b.generate bSeed index) *
                  uniformPredicateAverage (fun tailSeed :
                      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
                    dptwSurvivesAllBLevels b levelsAfterFirst
                      tailSeed index) := by
                exact congrArg
                  (fun average => average *
                    uniformPredicateAverage (fun tailSeed :
                        FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
                      dptwSurvivesAllBLevels b levelsAfterFirst
                        tailSeed index))
                  (uniformPredicateAverage_prod_ignore_left
                    (Left := FiniteBitTape s)
                    (Right := FiniteBitTape s)
                    (fun bSeed => b.generate bSeed index))
        _ = (uniformPredicateAverage (fun seed : FiniteBitTape s =>
              b.generate seed index)) ^ (levelsAfterFirst + 2) := by
            rw [ih]
            calc
              uniformPredicateAverage (fun seed : FiniteBitTape s =>
                    b.generate seed index) *
                  uniformPredicateAverage (fun seed : FiniteBitTape s =>
                    b.generate seed index) ^ (levelsAfterFirst + 1) =
                uniformPredicateAverage (fun seed : FiniteBitTape s =>
                    b.generate seed index) ^ (levelsAfterFirst + 1) *
                  uniformPredicateAverage (fun seed : FiniteBitTape s =>
                    b.generate seed index) := by
                      rw [mul_comm]
              _ = (uniformPredicateAverage (fun seed : FiniteBitTape s =>
                    b.generate seed index)) ^ (levelsAfterFirst + 2) := by
                      rw [← pow_succ]

/-- Uniform per-coordinate one-block probability `rho` therefore gives exact
survival probability `rho^(levelsAfterFirst+1)` at every coordinate. -/
theorem dptwSurvivesAllBLevels_average_eq_pow_of_marginal
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) = rho) :
    forall index,
      uniformPredicateAverage (fun seed :
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
        dptwSurvivesAllBLevels b levelsAfterFirst seed index) =
        rho ^ (levelsAfterFirst + 1) := by
  intro index
  rw [dptwSurvivesAllBLevels_average_eq_pow, hMarginal index]

/-- Combining independence with the survivor union bound: deleting the
terminal tail changes any Boolean test by at most
`2^n * rho^(levelsAfterFirst+1)` under an exact per-coordinate `B` marginal.
-/
theorem dptwZeroTail_test_average_sub_le_marginal_pow
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (tail : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) →
      TruthTable n)
    (test : TruthTable n → Bool) (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) = rho) :
    abs
        (uniformPredicateAverage (fun seed =>
            test (dptwGenerateWithTail a b levelsAfterFirst seed
              (tail seed))) -
          uniformPredicateAverage (fun seed =>
            test (dptwZeroTailGenerate a b levelsAfterFirst seed))) ≤
      (2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1) := by
  apply dptwZeroTail_test_average_sub_le_tableLength_mul
  intro index
  rw [dptwSurvivesAllBLevels_average_eq_pow, hMarginal index]

/-- The packed-tail version of the preceding estimate.  Here the terminal
table is an independent uniform factor of the seed rather than a fixed table
or a table chosen as a function of the prefix seed.  Thus the conditioning on
each packed tail and the final averaging over that tail are both internal to
the statement.

No pseudorandomness or branching-program premise is used: disagreement still
requires some output coordinate to survive every independent `B` block. -/
theorem dptwZeroTail_product_test_average_sub_le_marginal_pow
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (test : TruthTable n → Bool) (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) = rho) :
    abs
        (uniformPredicateAverage
            (fun pair : TruthTable n ×
                FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
              test (dptwGenerateWithTail a b levelsAfterFirst
                pair.2 pair.1)) -
          uniformPredicateAverage
            (fun pair : TruthTable n ×
                FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
              test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))) ≤
      (2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1) := by
  let fullTest :
      TruthTable n ×
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) → Bool :=
    fun pair => test
      (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)
  let zeroTest :
      TruthTable n ×
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) → Bool :=
    fun pair => test
      (dptwZeroTailGenerate a b levelsAfterFirst pair.2)
  let survivesSome :
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) → Bool :=
    fun seed => decide (exists index,
      dptwSurvivesAllBLevels b levelsAfterFirst seed index = true)
  calc
    abs (uniformPredicateAverage fullTest -
        uniformPredicateAverage zeroTest) ≤
        uniformPredicateAverage
          (fun pair => Bool.xor (fullTest pair) (zeroTest pair)) :=
      abs_uniformPredicateAverage_sub_le_disagreement fullTest zeroTest
    _ ≤ uniformPredicateAverage
        (fun pair : TruthTable n ×
            FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
          survivesSome pair.2) := by
      apply uniformPredicateAverage_mono
      intro pair hDifferent
      have hOutputs :
          dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1 ≠
            dptwZeroTailGenerate a b levelsAfterFirst pair.2 := by
        intro hEqual
        have hTestEqual := congrArg test hEqual
        dsimp only [fullTest, zeroTest] at hDifferent
        rw [hTestEqual] at hDifferent
        cases hResult :
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2) <;>
          simp [hResult] at hDifferent
      obtain ⟨index, hSurvives, _hTail⟩ :=
        (dptwGenerateWithTail_ne_zeroTail_iff_exists
          a b levelsAfterFirst pair.2 pair.1).1 hOutputs
      change survivesSome pair.2 = true
      simp only [survivesSome, decide_eq_true_eq]
      exact ⟨index, hSurvives⟩
    _ = uniformPredicateAverage survivesSome := by
      exact uniformPredicateAverage_prod_ignore_left survivesSome
    _ ≤ ∑ index : Fin (2 ^ n),
        uniformPredicateAverage (fun seed =>
          dptwSurvivesAllBLevels b levelsAfterFirst seed index) := by
      simpa [survivesSome] using
        (uniformPredicateAverage_exists_le_sum
          (fun seed index =>
            dptwSurvivesAllBLevels b levelsAfterFirst seed index)
          survivesSome (by
            intro seed
            simp [survivesSome]))
    _ = ∑ _index : Fin (2 ^ n),
        rho ^ (levelsAfterFirst + 1) := by
      apply Finset.sum_congr rfl
      intro index _
      exact dptwSurvivesAllBLevels_average_eq_pow_of_marginal
        b levelsAfterFirst rho hMarginal index
    _ = (2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1) := by
      simp

end OneTapeMagnification
end Frontier
end Pnp4
