/-
  pnp3/Tests/Counterexample.lean

  Formal disproof of the `shrinkage_for_AC0` axiom (as formulated in `Facts_Switching.lean`).

  The axiom asserts that *for any* family `F` of boolean functions on `n` variables,
  there exists a *single* `Shrinkage` object (encoding a common partial decision tree
  and leaf selections) that approximates every function in `F` with small error.

  We demonstrate that if `F` is the set of *all* boolean functions on `n` variables,
  this leads to an information-theoretic contradiction: the number of functions
  representable by such an atlas (capacity) is strictly smaller than `|F|` for
  sufficiently large `n`.

  This confirms that the axiom is too strong because it lacks a condition that
  functions in `F` must be "simple" (e.g., computable by small circuits).
-/

import ThirdPartyFacts.Facts_Switching
import Counting.BinomialBounds
import Counting.CapacityGap
import Counting.Atlas_to_LB_Core
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

namespace Pnp3
namespace Tests

open Core
open ThirdPartyFacts
open Counting

/--
  We fix AC0 parameters `M=1, d=1` to simulate a "small" circuit hypothesis.
  The axiom claims even for these parameters, shrinkage exists.
-/
def counterParams (n : Nat) : AC0Parameters :=
  { n := n, M := 1, d := 1 }

/--
  The family `F` consists of *all* boolean functions on `n` variables.
  Its size is `2^(2^n)`.
-/
noncomputable def allFunctions (n : Nat) : Family n :=
  (Counting.allFunctionsFinset n).toList

lemma allFunctions_len (n : Nat) :
    (allFunctions n).length = Nat.pow 2 (Nat.pow 2 n) := by
  rw [allFunctions]
  rw [Finset.length_toList]
  exact Counting.card_allFunctionsFinset n

/--
  We assume the axiom `shrinkage_for_AC0` holds.
  Then we derive `False` for `n = 10`.
-/
theorem axiom_implies_false : False := by
  -- Fix n = 10 (sufficiently large for bounds).
  let n := 10
  let params := counterParams n
  let F := allFunctions n

  -- Apply the axiom to `F`.
  have h_axiom := shrinkage_for_AC0 params F
  rcases h_axiom with ⟨t, ε, S, hF, ht, hε, ht_bound, hε0, hε1⟩

  -- Analyze the capacity of the resulting Atlas.
  -- 1. Get the atlas from the shrinkage object.
  let atlas := Atlas.fromShrinkage S
  have h_works := SAL_from_Shrinkage S

  -- 2. Bound the dictionary size `D`.
  -- From `Facts_Switching.lean`, we know `partial_from_AC0_leafDict_len_le` logic.
  -- The shrinkage object `S` has a tree of depth `t`.
  -- The number of leaves (size of dictionary R) is at most `2^t`.
  let D := atlas.dict.length
  have hD : D ≤ Nat.pow 2 t := by
    dsimp [atlas, Atlas.fromShrinkage, Atlas.ofPDT]
    exact PDT.leaves_length_le_pow_depth S.tree

  -- 3. Bound `t`.
  -- The axiom guarantees `t ≤ (log(M+2))^(d+1)`.
  -- For M=1, d=1: `(log2 3)^2 = 1^2 = 1`.
  have ht_val : t ≤ 1 := by
    have hlog : Nat.log2 (1 + 2) = 1 := by decide
    have hpow : Nat.pow 1 2 = 1 := by decide
    rw [counterParams] at ht_bound
    simp at ht_bound
    rwa [hlog, hpow] at ht_bound

  -- So D ≤ 2^1 = 2.
  have hD_bound : D ≤ 2 := le_trans hD (Nat.pow_le_pow_right (by decide) ht_val)

  -- 4. Bound `k`.
  -- The axiom doesn't explicitly bound `k` (it's implicit in `unionBound`).
  -- However, `SAL` allows any number of leaves.
  -- Wait, `CapacityGap.lean` uses `unionBound D k`.
  -- In `SAL`, the number of leaves used for a function is not explicitly bounded by `k` in the `Shrinkage` structure itself,
  -- BUT `Counting.unionBound` usually sums up to `D`.
  -- If we use *all* subsets, then `k = D`.
  -- `capacityBound` uses `unionBound D k`.
  -- Let's look at `Counting/Atlas_to_LB_Core.lean`.
  -- `capacityBound` is defined as `unionBound D k * hammingBallBound ...`.
  -- In SAL, we don't fix `k`. We just select *some* leaves.
  -- So we can take `k = D` (worst case, using all dictionary elements).
  let k := D

  -- 5. Bound the capacity.
  -- `unionBound D D` is exactly `2^D`.
  have hUnion : unionBound D D = Nat.pow 2 D := Nat.sum_range_choose D

  -- 6. Bound the Hamming Ball.
  -- ε ≤ 1/(n+2) = 1/12.
  have hε_val : ε ≤ (1 : Q) / 12 := by
    rw [counterParams] at hε1
    exact hε1

  let N := Nat.pow 2 n -- 1024
  have hN : N = 1024 := by decide

  -- We need `hammingBallBound N ε`.
  -- We know `hammingBallBound ≤ 2^N`.
  -- But we need a tighter bound to show contradiction.
  -- Use `hammingBallBound_twoPow_le_mul_pow_div_add_one`.

  have hε0_rat : (0 : Q) ≤ ε := hε0
  have hε1_rat : ε ≤ (1 : Q) / 2 := le_trans hε_val (by norm_num)

  -- To use specific bounds from `CapacityGap`, we need to match the ε condition.
  -- The axiom gives exactly `ε ≤ 1/(n+2)`.
  -- We can conservatively replace ε with `1/(n+2)` due to monotonicity.
  let ε_max : Q := (1 : Q) / 12

  have hCapMono : capacityBound D D N ε hε0_rat hε1_rat ≤ capacityBound D D N ε_max (by norm_num) (by norm_num) :=
    capacityBound_mono (le_refl _) (le_refl _) hε_val (by norm_num) (by norm_num) (le_refl _) (le_refl _) hε_val

  -- Now evaluate `capacityBound D D N ε_max`.
  -- = `unionBound D D * hammingBallBound N ε_max`.
  -- `unionBound D D = 2^D ≤ 2^2 = 4`.
  have hUnion_le : unionBound D D ≤ 4 := by
    rw [hUnion]
    exact Nat.pow_le_pow_right (by decide) hD_bound

  -- `hammingBallBound N ε_max`.
  -- Use `hammingBallBound_twoPow_lt_twoPowPow` logic manually or check values.
  -- `n=10`, `N=1024`. `ε = 1/12`.
  -- `budget = ceil(1024/12) = ceil(85.33) = 86`.
  -- `hammingBallBound` is sum of binoms `C(1024, i)` for `i=0..86`.
  -- We can use the bound `(budget+1) * N^budget`.
  -- `87 * 1024^86`.
  -- `1024 = 2^10`.
  -- `87 * (2^10)^86 = 87 * 2^860`.
  -- Total capacity ≤ `4 * 87 * 2^860`.
  -- Total capacity ≈ `2^870`.

  -- 7. Compare with `|F|`.
  -- `|F| = 2^(2^10) = 2^1024`.
  -- `2^870 < 2^1024`.
  -- Contradiction!

  -- Formalizing the contradiction:
  have h_bound_explicit :
      capacityBound D D N ε hε0_rat hε1_rat < Nat.pow 2 N := by
    -- We can use `capacityBound_twoPow_lt_twoPowPow` from `CapacityGap.lean`
    -- if we satisfy its conditions.
    apply capacityBound_twoPow_lt_twoPowPow n D D
    · decide -- 8 ≤ 10
    · norm_num -- 0 ≤ 1/12
    · norm_num -- 1/12 ≤ 1/2
    · -- unionBound D D ≤ 2^(2^n / (n+2))
      -- 4 ≤ 2^(1024 / 12) = 2^85
      -- True.
      rw [hUnion]
      have hlhs : Nat.pow 2 D ≤ 4 := Nat.pow_le_pow_right (by decide) hD_bound
      have hrhs : 4 ≤ Nat.pow 2 (Nat.pow 2 10 / 12) := by decide
      exact le_trans hlhs hrhs

  -- 8. Apply incompatibility.
  -- `h_works` implies every `f` in `F` is in `ApproxClass`.
  -- `incompatibility` theorem says if `|F| > capacity`, then False.

  -- We need to convert `F` to `Finset`.
  let Y := (Counting.allFunctionsFinset n)
  have hY_card : Y.card = Nat.pow 2 N := Counting.card_allFunctionsFinset n

  have hLarge : capacityBound D D N ε hε0_rat hε1_rat < Y.card := by
    rw [hY_card]
    exact h_bound_explicit

  have hApprox : ∀ f ∈ Y, f ∈ ApproxClass atlas.dict D ε := by
    intro f hf
    -- `h_works` says `WorksFor atlas F`.
    -- `WorksFor` definition: `∀ f ∈ F, ∃ S ⊆ atlas.dict, errU f S ≤ ε`.
    -- We need to show this implies `ApproxClass`.
    have hf_in_F : f ∈ F := by
      rw [F, allFunctions]
      simpa using hf
    rcases h_works f hf_in_F with ⟨S, hSub, hErr⟩
    apply approx_mem_of_errU_le
    use S
    refine ⟨_, hSub, hErr⟩
    -- `S` is a sublist of `atlas.dict`. Length of `S` is at most length of `dict`.
    -- We chose `k = D = atlas.dict.length`.
    exact listSubset_length_le hSub

  -- Apply incompatibility
  apply incompatibility (m := n) (D := D) (R := atlas.dict) (k := D) (ε := ε)
  · rfl -- hR
  · exact hε0_rat
  · exact hε1_rat
  · exact Y
  · exact hApprox
  · exact hLarge
