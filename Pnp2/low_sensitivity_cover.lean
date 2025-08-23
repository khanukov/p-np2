import Pnp2.BoolFunc.Sensitivity
import Pnp2.BoolFunc
import Pnp2.DecisionTree
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Aesop

open BoolFunc

-- Silence `unnecessarySimpa` linter warnings in this developing file.
set_option linter.unnecessarySimpa false
-- Temporary: ignore unused simp arguments while the development is in flux.
set_option linter.unusedSimpArgs false
-- Increase the heartbeat limit to accommodate the heavy well-founded recursion
-- used below.
set_option maxHeartbeats 1000000

namespace BoolFunc

variable {n : ℕ}

/-- Universal constant used in all depth and cover bounds.  The exact value is
chosen for convenience and does not attempt to be optimal. -/
def coverConst : Nat := 10

/--
Proposed recursion budget used in the constructive proof of
`decisionTree_cover`.  It instantiates the informal choice

\[ h = \max\Big(0, \big\lfloor s\,\log_2(n+1) - 1 - \frac{\log_2 n + \log_2(s\,\log_2(n+1)+3)}{\mathtt{coverConst}} \big\rfloor \Big) \].

The `Int.toNat` conversion implements the outer `max 0` by truncating negative
values to zero.
-/
noncomputable def decisionTreeBudget (n s : ℕ) : ℕ :=
  Int.toNat <|
    Int.floor ((s : ℝ) * Real.logb 2 (n + 1) - 1
      - (Real.logb 2 n +
          Real.logb 2 ((s : ℝ) * Real.logb 2 (n + 1) + 3)) / (coverConst : ℝ))

/--
Numerical bound for the ``large‑`$s$'' regime.

If the sensitivity parameter `s` dominates the dimension `n` (precisely,
`n + 2 ≤ s`), the crude combinatorial estimate `Cover2.mBound` for a budget
`h = n + 1` already fits under the final target `2^(coverConst * s * log₂(n+1))`.

This lemma is a minimal, yet fully formal, replacement for the false claim
`mBound n (n + 1) ≤ 2^(coverConst * s * log₂(n+1))` without any assumption on
`s`.  The inequality is easy for large `s`, and this version integrates with the
existing recursive cover construction (`buildCoverLex3`) which currently always
operates with the budget `h = n`.
-/
lemma mBound_le_pow_of_budget_choice_bigS
  {n s : ℕ} (hn : 1 ≤ n) (hs : n + 2 ≤ s) :
  Cover2.mBound n (n + 1)
      ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  -- Unfold the definition of `mBound` for the specific budget `n+1`.
  -- We keep the factors separate to reason about them individually.
  have hmb : Cover2.mBound n (n + 1)
      = n * (n + 3) * 2 ^ (10 * (n + 1)) := by
    simp [Cover2.mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      add_comm, add_left_comm, add_assoc]

  -- Bound the polynomial part `n * (n + 3)` by `(n + 1)^4`.
  -- The inequality `n + 3 ≤ (n + 1)^2` holds for `n ≥ 1`;
  -- combining it with `n ≤ (n + 1)^2` yields the desired product bound.
  have h_le_pow2 : n ≤ (n + 1) ^ 2 := by
    -- `n ≤ n+1` and `n+1 ≤ (n+1)^2`.
    have hle₁ : n ≤ n + 1 := Nat.le_succ _
    have hle₂ : n + 1 ≤ (n + 1) ^ 2 := by
      -- `(n+1)^2 = (n+1) * (n+1)` and `1 ≤ n+1` since `n ≥ 1`.
      have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
      simpa [Nat.pow_two, Nat.mul_comm] using
        (Nat.mul_le_mul_left (n + 1) hpos)
    exact le_trans hle₁ hle₂
  have h_le_pow2' : n + 3 ≤ (n + 1) ^ 2 := by
    -- Rewrite the claim as a nonnegativity statement and use that
    -- `(n - 1) * (n + 2) ≥ 0` for `n ≥ 1`.
    have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnonneg : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) + 2) := by
      have h₁ : 0 ≤ (n : ℝ) - 1 := sub_nonneg.mpr hx
      have h₂ : 0 ≤ (n : ℝ) + 2 := by linarith
      exact mul_nonneg h₁ h₂
    have : (n + 3 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
      have hdiff :
          (n + 1 : ℝ) ^ 2 - (n + 3 : ℝ) = ((n : ℝ) - 1) * ((n : ℝ) + 2) := by ring
      have hdiff_nonneg : 0 ≤ (n + 1 : ℝ) ^ 2 - (n + 3 : ℝ) := by
        simpa [hdiff] using hnonneg
      exact sub_nonneg.mp hdiff_nonneg
    exact_mod_cast this
  have hpoly : n * (n + 3) ≤ (n + 1) ^ 4 := by
    have := Nat.mul_le_mul h_le_pow2 h_le_pow2'
    -- Simplify the right-hand side into `(n+1)^4`.
    simpa [Nat.pow_two, pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using this

  -- As `n ≥ 1`, the base `n + 1` dominates `2`, hence the exponential factor
  -- `2^(10*(n+1))` is bounded by `(n+1)^(10*(n+1))`.
  have hpow : 2 ^ (10 * (n + 1)) ≤ (n + 1) ^ (10 * (n + 1)) := by
    have hbase : 2 ≤ n + 1 := Nat.succ_le_succ hn
    exact Nat.pow_le_pow_left hbase (10 * (n + 1))

  -- Combine the polynomial and exponential bounds.
  have hbound : Cover2.mBound n (n + 1)
      ≤ (n + 1) ^ 4 * (n + 1) ^ (10 * (n + 1)) := by
    -- Start from `hmb` and replace the factors.
    have := Nat.mul_le_mul hpoly hpow
    simpa [hmb] using this

  -- Collapse the product of powers into a single power.
  have hpow_add : (n + 1) ^ 4 * (n + 1) ^ (10 * (n + 1))
      = (n + 1) ^ (10 * (n + 1) + 4) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_add] using
      (Nat.pow_add (n + 1) (10 * (n + 1)) 4).symm

  -- Put everything together.
  have hmb_final :
      Cover2.mBound n (n + 1)
        ≤ (n + 1) ^ (10 * (n + 1) + 4) := by
    simpa [hpow_add] using hbound

  -- Finally, compare the exponents.  Since `s ≥ n + 2`, the right-hand side
  -- exponent dominates `10*(n+1)+4`.
  have hexp : 10 * (n + 1) + 4 ≤ coverConst * s := by
    -- `coverConst = 10`.
    have : 10 * (n + 1) + 4 ≤ 10 * s := by
      have hbase : 10 * (n + 1) + 4 ≤ 10 * (n + 2) := by
        -- Rearranged: 10*n + 14 ≤ 10*n + 20, which holds since 14 ≤ 20.
        have : 14 ≤ 20 := by decide
        -- Adding `10*n` to both sides preserves the inequality.
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (add_le_add_left this (10 * n))
      have htrans := le_trans hbase (Nat.mul_le_mul_left 10 hs)
      exact htrans
    simpa [coverConst] using this
  have hpow_exp :
      (n + 1) ^ (10 * (n + 1) + 4)
        ≤ (n + 1) ^ (coverConst * s) :=
    Nat.pow_le_pow_of_le_left (by exact Nat.succ_le_succ (Nat.zero_le _)) hexp

  -- Convert the base `(n+1)^...` into the desired `2^...` using the identity
  -- `a^k = 2^(k * log₂ a)` for `a = n + 1`.
  have hpow_base :
      (n + 1) ^ (coverConst * s)
        ≤ 2 ^ (coverConst * s * Nat.log2 (n + 1)) := by
    -- `Nat.pow_log2_le` supplies `2^(log₂ (n+1)) ≤ n+1`; raising both sides to
    -- the positive power `coverConst * s` preserves the inequality.
    have hlog : 2 ^ Nat.log2 (n + 1) ≤ n + 1 := Nat.pow_log2_le (n + 1)
    have hpos : 0 < coverConst * s := by
      have : 0 < s := lt_of_lt_of_le (Nat.succ_pos _) hs
      have : 0 < coverConst * s := Nat.mul_pos (by decide) this
      simpa [coverConst] using this
    exact
      Nat.pow_le_pow_of_le_left' hlog (coverConst * s)

  -- Final comparison in the chain of inequalities.
  have hfinal :
      Cover2.mBound n (n + 1)
        ≤ 2 ^ (coverConst * s * Nat.log2 (n + 1)) := by
    have := le_trans hmb_final hpow_exp
    exact le_trans this hpow_base

  -- Simplify `(Nat.succ n)` in the logarithm.
  simpa [Nat.succ_eq_add_one] using hfinal

-- The next lemma links explicit decision trees with the cover construction.
-- The combinatorial result of Gopalan–Moshkovitz–Oliveira shows that a single
-- decision tree of depth `O(s * log n)` suffices to compute every function in
-- the family of low-sensitivity Boolean functions.  Each leaf of such a tree
-- corresponds to a rectangular subcube on which every function is constant
-- (possibly with different colours), bounding the number of subcubes by an
-- exponential in `s * log₂ (n + 1)`.

/-!
Integrate the explicit decision tree with the cover construction.
If a tree has leaves that are monochromatic for each function individually and
covers every `1`-input, its leaf subcubes form a valid cover whose size is
bounded by `2 ^ depth`.
-/
lemma decisionTree_cover_of_tree
  {n s : Nat} (F : Family n) (t : DecisionTree n) [Fintype (Point n)]
  (hmono : ∀ f ∈ F, ∀ R ∈ DecisionTree.leaves_as_subcubes t,
      Subcube.monochromaticFor R f)
  (hcov : ∀ f ∈ F, ∀ x, f x = true →
      ∃ R ∈ DecisionTree.leaves_as_subcubes t, x ∈ₛ R)
  (hdepth : DecisionTree.depth t ≤ coverConst * s * Nat.log2 (Nat.succ n)) :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Choose the set of leaf subcubes as the cover.
  let Rset := DecisionTree.leaves_as_subcubes t
  have hcard_le : Rset.card ≤ 2 ^ DecisionTree.depth t :=
    DecisionTree.tree_depth_bound (t := t)
  have hcard : Rset.card ≤ 2 ^ (coverConst * s * Nat.log2 (Nat.succ n)) := by
    exact le_trans hcard_le
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hdepth)
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro f hf R hR; exact hmono f hf R hR
  · intro f hf x hx; exact hcov f hf x hx

lemma monochromaticFor_of_family_singleton {R : Subcube n} {f : BFunc n} :
    Subcube.monochromaticForFamily R ({f} : Family n) →
    Subcube.monochromaticFor R f := by
  classical
  intro h
  rcases h with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  -- `aesop` recognises that the desired equality is provided by `hb`.
  have hx' : f x = b := hb f (by simp) hx
  -- `aesop` discharges the goal from the available hypothesis.
  aesop

/--
Refined orientation of `non_constant_family_has_sensitive_coord`.
It produces a sensitive coordinate together with an input where the
value changes from `true` to `false`.  This direction is convenient for
the recursive cover construction, which always follows a `true` branch. -/
lemma exists_sensitive_coord_true_false (F : Family n) [Fintype (Point n)]
    (hconst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true) :
    ∃ i : Fin n, ∃ f ∈ F, ∃ x : Point n,
      f x = true ∧ f (Point.update x i (!x i)) = false := by
  classical
  -- Obtain a sensitive coordinate and a witness where the value flips.
  obtain ⟨i, f, hfF, x, hxneq⟩ :=
    non_constant_family_has_sensitive_coord (F := F) (n := n) hconst htrue
  -- Case analysis on the value of `f` at `x`.
  by_cases hfx : f x = true
  · refine ⟨i, f, hfF, x, hfx, ?_⟩
    -- The flipped point must evaluate to `false`.
    have : f (Point.update x i (!x i)) ≠ true := by
      simpa [hfx] using hxneq
    cases hflip : f (Point.update x i (!x i)) with
    | false => simpa [hflip]
    | true => simpa [hflip] using this
  · -- Otherwise `f x = false`; flip the bit to get a `true` value.
    have hfxfalse : f x = false := by
      cases hval : f x with
      | false => simpa [hval]
      | true => cases hfx hval
    -- Consider the flipped input.
    refine ⟨i, f, hfF, Point.update x i (!x i), ?_, ?_⟩
    · -- Show that the flipped input yields `true`.
      have : f (Point.update x i (!x i)) ≠ false := by
        simpa [hfxfalse] using hxneq.symm
      cases hflip : f (Point.update x i (!x i)) with
      | true => simpa [hflip]
      | false => simpa [hflip] using this
    · -- Flipping again returns to `x`, where the value is `false`.
      have hxupd :
          Point.update (Point.update x i (!x i)) i (! (Point.update x i (!x i)) i) = x := by
        -- simplify the double update
        funext j; by_cases hji : j = i
        · subst hji; simp [Point.update]
        · simp [Point.update, hji]
      have := congrArg f hxupd
      simpa [hfxfalse] using this

/--
An oriented version of `exists_sensitive_coord_in_A`.  Under the same
hypotheses, it returns a sensitive coordinate inside `A` together with a
point where some function flips from `true` to `false` when that coordinate is
toggled.  This orientation is convenient for recursive constructions that
always follow a `true` branch.
-/
lemma exists_sensitive_coord_true_false_in_A
    (F : Family n) [Fintype (Point n)] (A : Finset (Fin n))
    (hconst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true)
    (hA : ∀ j ∉ A, ∀ f ∈ F, coordSensitivity f j = 0) :
    ∃ i ∈ A, ∃ f ∈ F, ∃ x : Point n,
      f x = true ∧ f (Point.update x i (!x i)) = false := by
  classical
  obtain ⟨i, hiA, f, hfF, x, hx⟩ :=
    exists_sensitive_coord_in_A (F := F) (A := A)
      (hNonConst := hconst) (htrue := htrue) (hA := hA)
  have hx_ne : f x ≠ f (Point.update x i (!x i)) := hx
  by_cases hfx : f x = true
  ·
    have hflip : f (Point.update x i (!x i)) = false := by
      have : f (Point.update x i (!x i)) ≠ true := by
        simpa [hfx] using hx_ne
      cases hval : f (Point.update x i (!x i)) with
      | false => simpa [hval]
      | true => cases this hval
    exact ⟨i, hiA, f, hfF, x, hfx, hflip⟩
  ·
    have hfxfalse : f x = false := by
      cases hval : f x with
      | true => cases hfx hval
      | false => simpa [hval]
    have hflip : f (Point.update x i (!x i)) = true := by
      have : f (Point.update x i (!x i)) ≠ false := by
        simpa [hfxfalse] using hx_ne.symm
      cases hval : f (Point.update x i (!x i)) with
      | true => simpa [hval]
      | false => cases this hval
    let x' := Point.update x i (!x i)
    have hxupd : Point.update x' i (! x' i) = x := by
      funext j; by_cases hji : j = i
      · subst hji; simp [Point.update, x']
      · simp [Point.update, hji, x']
    refine ⟨i, hiA, f, hfF, x', hflip, ?_⟩
    have := congrArg f hxupd
    simpa [hxupd, hfxfalse] using this

/--
If a family is non-constant yet every coordinate is insensitive and each
function attains `true` somewhere, we reach a contradiction.  This helper
rules out the case `A = ∅` in the recursive cover construction: once all
coordinates are known to be insensitive, any remaining non-constant family
would exhibit a sensitive coordinate, contradicting the hypothesis.
-/
lemma nonconstant_all_insensitive_false (F : Family n) [Fintype (Point n)]
    (hconst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true)
    (hins : ∀ j : Fin n, ∀ f ∈ F, coordSensitivity f j = 0) :
    False := by
  classical
  -- A sensitive coordinate exists by non-constancy and the `true` witnesses.
  obtain ⟨i, f, hfF, x, hx⟩ :=
    non_constant_family_has_sensitive_coord (F := F)
      (n := n) (hconst := hconst) (htrue := htrue)
  -- But `hins` declares that all coordinates are insensitive, a contradiction.
  have hzero := (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 (hins i f hfF) x
  exact hx hzero

/--
If no coordinate is sensitive across the family and no function is constantly
`false`, then every function must be constantly `true`.  This lemma underpins
the constant branch of `buildCoverLex3` once all sensitive coordinates have
been eliminated.
-/
lemma all_true_of_no_sensitive_coord (F : Family n) [Fintype (Point n)]
    (hins : ∀ i : Fin n, ¬ sensitiveCoord F i)
    (hfalse : ¬ ∃ f ∈ F, ∀ x, f x = false) :
    ∀ f ∈ F, ∀ x : Point n, f x = true := by
  classical
  intro f hf x
  -- Each function attains `true` somewhere; otherwise it would be constantly
  -- `false`, contradicting `hfalse`.
  have hx0 : ∃ x0 : Point n, f x0 = true := by
    by_contra h
    have hfalsef : ∀ y, f y = false := by
      intro y
      have hy := not_exists.mp h y
      cases hfy : f y with
      | false => simpa [hfy]
      | true => cases hy hfy
    exact hfalse ⟨f, hf, hfalsef⟩
  rcases hx0 with ⟨x0, hx0⟩
  -- Show that the support of `f` is empty.
  have hsupp : support f = (∅ : Finset (Fin n)) := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiSens : sensitiveCoord F i := by
      rcases mem_support_iff.mp hi with ⟨y, hy⟩
      exact ⟨f, hf, y, hy⟩
    exact (hins i) hiSens
  -- Points trivially agree on the empty support, so `f` is constant.
  have hagree : ∀ i ∈ support f, x i = x0 i := by
    intro i hi
    have : False := by simpa [hsupp] using hi
    exact this.elim
  have hx :=
    eval_eq_of_agree_on_support (f := f) (x := x) (y := x0) hagree
  simpa [hx0] using hx

/--
The images of two rectangle sets under extension with opposite fixed values of
`i` are disjoint.  Intuitively, any point lying in an extension with `i = false`
must satisfy `x i = false`, whereas membership in an extension with
`i = true` forces `x i = true`.  The hypotheses `hi₀`/`hi₁` guarantee that `i`
was not already fixed in the original rectangles, so the extensions genuinely
record the new value of `i`.
-/
lemma disjoint_extend_images (i : Fin n) {R0 R1 : Finset (Subcube n)}
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    Disjoint (R0.image (fun R => Subcube.extend R i false))
             (R1.image (fun R => Subcube.extend R i true)) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro R hR0 hR1
  -- Decode membership of `R` in the two images.
  obtain ⟨S0, hS0, hR0'⟩ := Finset.mem_image.mp hR0
  obtain ⟨S1, hS1, hR1'⟩ := Finset.mem_image.mp hR1
  -- Consequently the same subcube arises by extending with both `false` and `true`.
  have hEq : Subcube.extend S0 i false = Subcube.extend S1 i true :=
    by simpa [hR0', hR1'] using Eq.trans hR0' (hR1'.symm)
  -- Build a point in `S0` forcing `x i = false`.
  classical
  let x : Point n := fun j => if h : j ∈ S0.idx then S0.val j h else false
  have hx0 : x ∈ₛ S0 := by
    intro j hj; dsimp [x]; simp [hj]
  have hxi : x i = false := by
    dsimp [x];
    have : i ∉ S0.idx := hi0 _ hS0
    simp [this]
  -- The point `x` lies in the extended subcube on the `false` branch.
  have hxR0 : x ∈ₛ Subcube.extend S0 i false :=
    (Subcube.mem_extend_iff (R := S0) (i := i) (b := false)
        (x := x) (hi0 _ hS0)).2 ⟨hxi, hx0⟩
  -- Due to `hEq`, it also lies in the extension on the `true` branch.
  have hxR1 : x ∈ₛ Subcube.extend S1 i true := by
    simpa [hEq] using hxR0
  have hx1 : x i = true :=
    (Subcube.mem_extend_iff (R := S1) (i := i) (b := true)
        (x := x) (hi1 _ hS1)).1 hxR1 |>.1
  -- Finally derive the contradiction `false = true`.
  have : False := by simpa [hxi] using hx1
  exact this

/-!
`disjoint_extend_images` immediately yields a convenient cardinality
statement: when extending two rectangle collections along opposite values of
the same coordinate, the resulting images are disjoint.  Consequently the size
of their union is just the sum of the original sizes.  This fact will be used
when estimating the number of rectangles produced by the recursive cover
construction.
-/
lemma card_extend_union_le (i : Fin n) {R0 R1 : Finset (Subcube n)}
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    (R0.image (fun R => Subcube.extend R i false) ∪
       R1.image (fun R => Subcube.extend R i true)).card ≤
      R0.card + R1.card := by
  classical
  have hdis :=
    disjoint_extend_images (i := i) (R0 := R0) (R1 := R1) hi0 hi1
  have hcard :=
    (Finset.card_union_of_disjoint hdis :
        (R0.image (fun R => Subcube.extend R i false) ∪
            R1.image (fun R => Subcube.extend R i true)).card =
          (R0.image (fun R => Subcube.extend R i false)).card +
            (R1.image (fun R => Subcube.extend R i true)).card)
  have h0 := Finset.card_image_le (s := R0) (f := fun R => Subcube.extend R i false)
  have h1 := Finset.card_image_le (s := R1) (f := fun R => Subcube.extend R i true)
  have hsum := Nat.add_le_add h0 h1
  simpa [hcard] using hsum

/--
If a family `F` is insensitive to coordinate `i` and a subcube `R` fixes `i`,
then removing that constraint preserves monochromaticity for `F`.
-/
lemma Subcube.monochromaticForFamily_unfix_of_insensitive {n : ℕ}
    {F : Family n} {R : Subcube n} {i : Fin n}
    (hins : ∀ f ∈ F, coordSensitivity f i = 0)
    (hi : i ∈ R.idx)
    (hmono : Subcube.monochromaticForFamily R F) :
    Subcube.monochromaticForFamily (Subcube.unfix R i) F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  let x' := Point.update x i (R.val i hi)
  have hx' : x' ∈ₛ R := by
    intro j hjR
    by_cases hji : j = i
    · subst hji; simp [x', Point.update]
    · have hjmem : j ∈ R.idx.erase i := Finset.mem_erase.mpr ⟨hji, hjR⟩
      have hxj := hx j hjmem
      simp [Subcube.unfix, hjR, hji, x', Point.update] at hxj
      simpa [x', Point.update, hji] using hxj
  have hxval : f x' = c := hc f hf (x := x') hx'
  have hins' :=
    (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 (hins f hf)
  have hxswap : f x = f x' := by
    by_cases hxi : x i = R.val i hi
    · have hxEq : x' = x := by
        funext j; by_cases hji : j = i
        · subst hji; simp [x', Point.update, hxi]
        · simp [x', Point.update, hji]
      simpa [hxEq] using (rfl : f x = f x)
    ·
      have hxflip : R.val i hi = !x i := by
        cases hxb : x i
        · cases hrb : R.val i hi
          · have : x i = R.val i hi := by simp [hxb, hrb]
            exact (hxi this).elim
          · simp [hxb, hrb]
        · cases hrb : R.val i hi
          · simp [hxb, hrb]
          · have : x i = R.val i hi := by simp [hxb, hrb]
            exact (hxi this).elim
      have := hins' x
      simpa [x', hxflip] using this
  exact hxswap.trans hxval

/--
If a Boolean function `f` does not depend on coordinate `i` and a subcube `R`
fixes that coordinate, removing the constraint preserves monochromaticity.  This
is the single-function analogue of
`Subcube.monochromaticForFamily_unfix_of_insensitive`.
-/
lemma Subcube.monochromaticFor_unfix_of_insensitive {n : ℕ}
    [Fintype (Point n)]
    {f : BFunc n} {R : Subcube n} {i : Fin n}
    (hins : coordSensitivity f i = 0)
    (hi : i ∈ R.idx)
    (hmono : Subcube.monochromaticFor R f) :
    Subcube.monochromaticFor (Subcube.unfix R i) f := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x hx
  let x' := Point.update x i (R.val i hi)
  have hx' : x' ∈ₛ R := by
    intro j hjR
    by_cases hji : j = i
    · subst hji; simp [x', Point.update]
    · have hjmem : j ∈ R.idx.erase i := Finset.mem_erase.mpr ⟨hji, hjR⟩
      have hxj := hx j hjmem
      simp [Subcube.unfix, hjR, hji, x', Point.update] at hxj
      simpa [x', Point.update, hji] using hxj
  have hxval : f x' = c := hc (x := x') hx'
  have hins' := (coordSensitivity_eq_zero_iff (f := f) (i := i)).1 hins
  have hxswap : f x = f x' := by
    by_cases hxi : x i = R.val i hi
    · have hxEq : x' = x := by
        funext j; by_cases hji : j = i
        · subst hji; simp [x', Point.update, hxi]
        · simp [x', Point.update, hji]
      simpa [hxEq] using (rfl : f x = f x)
    ·
      have hxflip : R.val i hi = !x i := by
        cases hxb : x i
        · cases hrb : R.val i hi
          · have : x i = R.val i hi := by simp [hxb, hrb]
            exact (hxi this).elim
          · simp [hxb, hrb]
        · cases hrb : R.val i hi
          · simp [hxb, hrb]
          · have : x i = R.val i hi := by simp [hxb, hrb]
            exact (hxi this).elim
      have := hins' x
      simpa [x', hxflip] using this
  exact hxswap.trans hxval

/--
Normalise a cover of the branch `F_b` so that none of its rectangles
fixes the splitting coordinate `i`.  Rectangles that already avoid `i`
are kept as is, whereas those fixing `i = b` are "unfixed" via
`Subcube.unfix`.  Rectangles fixing `i` to the opposite Boolean value do
not contain any point with `x i = b` and are therefore discarded.  The
resulting collection still covers all relevant inputs, its size does not
exceed the original one, and every rectangle avoids `i`.
-/
lemma cover_normalize_branch {F_b : Family n} (i : Fin n) (b : Bool)
    {Rb : Finset (Subcube n)}
    (hmono : ∀ R ∈ Rb, Subcube.monochromaticForFamily R F_b)
    (hcov : ∀ f ∈ F_b, ∀ x, x i = b → f x = true → ∃ R ∈ Rb, x ∈ₛ R)
    (hins : ∀ f ∈ F_b, coordSensitivity f i = 0) :
    ∃ Rb' : Finset (Subcube n),
      (∀ R ∈ Rb', Subcube.monochromaticForFamily R F_b) ∧
      (∀ f ∈ F_b, ∀ x, x i = b → f x = true → ∃ R ∈ Rb', x ∈ₛ R) ∧
      (∀ R ∈ Rb', i ∉ R.idx) ∧
      Rb'.card ≤ Rb.card := by
  classical
  -- Split the original collection into rectangles that already avoid `i`
  -- and those that fix `i = b`.
  let S0 := Rb.filter fun R => i ∉ R.idx
  let S1 := Rb.filter fun R => if h : i ∈ R.idx then R.val i h = b else False
  -- Normalised collection: keep `S0` and unfix the rectangles from `S1`.
  let Rb' := S0 ∪ S1.image (fun R => Subcube.unfix R i)
  refine ⟨Rb', ?mono, ?cov, ?hi, ?card⟩
  · -- Monochromaticity is preserved for all rectangles in the normalised set.
    intro R hR
    rcases Finset.mem_union.mp hR with hS0 | hS1
    · -- Case: `R` comes from `S0` and already avoids `i`.
      have hRb : R ∈ Rb := (Finset.mem_filter.mp hS0).1
      exact hmono R hRb
    · -- Case: `R` arises by unfixing some `S` in `S1`.
      rcases Finset.mem_image.mp hS1 with ⟨S, hS, rfl⟩
      have hRbS : S ∈ Rb := (Finset.mem_filter.mp hS).1
      -- The predicate defining `S1` ensures `i` is fixed in `S`.
      have hiS : i ∈ S.idx := by
        have hp := (Finset.mem_filter.mp hS).2
        by_cases h : i ∈ S.idx
        · exact h
        · have : (if h : i ∈ S.idx then S.val i h = b else False) := hp
          simp [h] at this
      have hmonoS := hmono S hRbS
      -- Unfixing maintains monochromaticity because `F_b` ignores `i`.
      exact Subcube.monochromaticForFamily_unfix_of_insensitive
        (F := F_b) (R := S) (i := i) (hins := hins) hiS hmonoS
  · -- Coverage of all inputs with `x i = b` is preserved.
    intro f hf x hxi hx
    obtain ⟨R, hR, hxR⟩ := hcov f hf x hxi hx
    by_cases hiR : i ∈ R.idx
    · -- The rectangle fixes `i`; it must be to `b` because `x i = b`.
      have hval : R.val i hiR = b := by
        have := hxR i hiR
        simpa [hxi] using this.symm
      -- `R` lies in `S1`.
      have hS1 : R ∈ S1 := by
        refine Finset.mem_filter.mpr ?_
        have hpred : (if h : i ∈ R.idx then R.val i h = b else False) := by
          simp [hiR, hval]
        exact ⟨hR, hpred⟩
      -- Use the unfixed rectangle to cover `x`.
      refine ⟨Subcube.unfix R i, ?_, ?_⟩
      · refine Finset.mem_union.mpr ?_
        refine Or.inr ?_
        exact Finset.mem_image.mpr ⟨R, hS1, rfl⟩
      · exact Subcube.mem_unfix_of_mem (i := i) (R := R) hxR
    · -- The rectangle already avoids `i` and is kept unchanged.
      have hS0 : R ∈ S0 := by
        refine Finset.mem_filter.mpr ⟨hR, ?_⟩
        exact hiR
      refine ⟨R, ?_, hxR⟩
      exact Finset.mem_union.mpr (Or.inl hS0)
  · -- No rectangle in the normalised collection fixes `i`.
    intro R hR
    rcases Finset.mem_union.mp hR with hS0 | hS1
    · exact (Finset.mem_filter.mp hS0).2
    · rcases Finset.mem_image.mp hS1 with ⟨S, hS, rfl⟩
      -- `Subcube.unfix` explicitly removes `i`.
      simpa using Subcube.idx_unfix (R := S) (i := i)
  · -- Cardinality does not increase.
    -- First bound the size of `Rb'` by the sizes of `S0` and `S1`.
    have hcard_union : Rb'.card ≤ S0.card + (S1.image (fun R => Subcube.unfix R i)).card :=
      Finset.card_union_le (s := S0) (t := S1.image (fun R => Subcube.unfix R i))
    have hcard_image : (S1.image (fun R => Subcube.unfix R i)).card ≤ S1.card :=
      Finset.card_image_le (s := S1) (f := fun R => Subcube.unfix R i)
    have hcard₁ : Rb'.card ≤ S0.card + S1.card :=
      le_trans hcard_union (by exact add_le_add_left hcard_image _)
    -- Relate `S0.card + S1.card` back to the original collection `Rb`.
    have hsubset : S0 ∪ S1 ⊆ Rb := by
      intro R hR
      rcases Finset.mem_union.mp hR with hR0 | hR1
      · exact (Finset.mem_filter.mp hR0).1
      · exact (Finset.mem_filter.mp hR1).1
    have hdis : Disjoint S0 S1 := by
      refine Finset.disjoint_left.mpr ?_
      intro R hR0 hR1
      have hi0 : i ∉ R.idx := (Finset.mem_filter.mp hR0).2
      have hi1' := (Finset.mem_filter.mp hR1).2
      -- The predicate in `S1` implies `i ∈ R.idx`.
      have hi1 : i ∈ R.idx := by
        by_cases h : i ∈ R.idx
        · exact h
        · have : (if h : i ∈ R.idx then R.val i h = b else False) := hi1'
          simp [h] at this
      exact False.elim (hi0 hi1)
    have hcard_subset : (S0 ∪ S1).card ≤ Rb.card :=
      Finset.card_le_card hsubset
    have hcard_union_eq : (S0 ∪ S1).card = S0.card + S1.card :=
      Finset.card_union_of_disjoint hdis
    have hbound : S0.card + S1.card ≤ Rb.card := by
      simpa [hcard_union_eq] using hcard_subset
    exact le_trans hcard₁ hbound

/--
Pointwise variant of `cover_normalize_branch`.  Here monochromaticity is
tracked per function in the branch family rather than for the entire family at
once.  This formulation prepares the ground for refactoring the recursive
cover construction to carry pointwise colour information.
-/
lemma cover_normalize_branch_pointwise {F_b : Family n} (i : Fin n) (b : Bool)
    [Fintype (Point n)]
    {Rb : Finset (Subcube n)}
    (hmono : ∀ R ∈ Rb, ∀ g ∈ F_b, Subcube.monochromaticFor R g)
    (hcov  : ∀ f ∈ F_b, ∀ x, x i = b → f x = true → ∃ R ∈ Rb, x ∈ₛ R)
    (hins  : ∀ f ∈ F_b, coordSensitivity f i = 0) :
    ∃ Rb' : Finset (Subcube n),
      (∀ R ∈ Rb', ∀ g ∈ F_b, Subcube.monochromaticFor R g) ∧
      (∀ f ∈ F_b, ∀ x, x i = b → f x = true → ∃ R ∈ Rb', x ∈ₛ R) ∧
      (∀ R ∈ Rb', i ∉ R.idx) ∧
      Rb'.card ≤ Rb.card := by
  classical
  -- As before, split rectangles into those already avoiding `i` and those
  -- fixing `i = b`.
  let S0 := Rb.filter fun R => i ∉ R.idx
  let S1 := Rb.filter fun R => if h : i ∈ R.idx then R.val i h = b else False
  let Rb' := S0 ∪ S1.image (fun R => Subcube.unfix R i)
  refine ⟨Rb', ?mono, ?cov, ?hi, ?card⟩
  · -- Pointwise monochromaticity for every rectangle in the normalised set.
    intro R hR g hg
    rcases Finset.mem_union.mp hR with hS0 | hS1
    · -- `R` was untouched and already avoided `i`.
      have hRb : R ∈ Rb := (Finset.mem_filter.mp hS0).1
      exact hmono R hRb g hg
    · -- `R` results from unfixing some `S` in `S1`.
      rcases Finset.mem_image.mp hS1 with ⟨S, hS, rfl⟩
      have hRbS : S ∈ Rb := (Finset.mem_filter.mp hS).1
      -- `S` fixes `i`, so `Subcube.unfix` may be applied.
      have hiS : i ∈ S.idx := by
        have hp := (Finset.mem_filter.mp hS).2
        by_cases h : i ∈ S.idx
        · exact h
        · have : (if h : i ∈ S.idx then S.val i h = b else False) := hp
          simp [h] at this
      have hmonoS := hmono S hRbS g hg
      have hinsg : coordSensitivity g i = 0 := hins g hg
      -- Use the single-function unfix lemma.
      exact Subcube.monochromaticFor_unfix_of_insensitive
        (f := g) (R := S) (i := i) hinsg hiS hmonoS
  · -- Coverage mirrors the family-level version.
    intro f hf x hxi hx
    obtain ⟨R, hR, hxR⟩ := hcov f hf x hxi hx
    by_cases hiR : i ∈ R.idx
    · have hval : R.val i hiR = b := by
        have := hxR i hiR; simpa [hxi] using this.symm
      have hS1 : R ∈ S1 := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨hR, by simp [hiR, hval]⟩
      refine ⟨Subcube.unfix R i, ?_, ?_⟩
      · refine Finset.mem_union.mpr ?_
        refine Or.inr ?_
        exact Finset.mem_image.mpr ⟨R, hS1, rfl⟩
      · exact Subcube.mem_unfix_of_mem (i := i) (R := R) hxR
    · have hS0 : R ∈ S0 := by
        refine Finset.mem_filter.mpr ⟨hR, ?_⟩; exact hiR
      refine ⟨R, ?_, hxR⟩
      exact Finset.mem_union.mpr (Or.inl hS0)
  · -- All rectangles in the result avoid `i`.
    intro R hR
    rcases Finset.mem_union.mp hR with hS0 | hS1
    · exact (Finset.mem_filter.mp hS0).2
    · rcases Finset.mem_image.mp hS1 with ⟨S, hS, rfl⟩
      simpa using Subcube.idx_unfix (R := S) (i := i)
  · -- Cardinality does not increase (same argument as before).
    have hcard_union : Rb'.card ≤ S0.card + (S1.image (fun R => Subcube.unfix R i)).card :=
      Finset.card_union_le (s := S0) (t := S1.image (fun R => Subcube.unfix R i))
    have hcard_image : (S1.image (fun R => Subcube.unfix R i)).card ≤ S1.card :=
      Finset.card_image_le (s := S1) (f := fun R => Subcube.unfix R i)
    have hcard₁ : Rb'.card ≤ S0.card + S1.card :=
      hcard_union.trans (by exact add_le_add_left hcard_image _)
    have hsubset : S0 ∪ S1 ⊆ Rb := by
      intro R hR; rcases Finset.mem_union.mp hR with hR0 | hR1
      · exact (Finset.mem_filter.mp hR0).1
      · exact (Finset.mem_filter.mp hR1).1
    have hdis : Disjoint S0 S1 := by
      refine Finset.disjoint_left.mpr ?_
      intro R hR0 hR1
      have hi0 : i ∉ R.idx := (Finset.mem_filter.mp hR0).2
      have hi1' := (Finset.mem_filter.mp hR1).2
      have hi1 : i ∈ R.idx := by
        by_cases h : i ∈ R.idx
        · exact h
        · have : (if h : i ∈ R.idx then R.val i h = b else False) := hi1'
          simp [h] at this
      exact False.elim (hi0 hi1)
    have hcard_subset : (S0 ∪ S1).card ≤ Rb.card :=
      Finset.card_le_card hsubset
    have hcard_union_eq : (S0 ∪ S1).card = S0.card + S1.card :=
      Finset.card_union_of_disjoint hdis
    have hbound : S0.card + S1.card ≤ Rb.card := by
      simpa [hcard_union_eq] using hcard_subset
    exact hcard₁.trans hbound

/--
If two collections of subcubes cover all `1`-inputs of the restricted families
`F.restrict i false` and `F.restrict i true` respectively, then after extending
each subcube with the fixed value of `i` their union covers every `1`-input of
the original family `F`.  The hypothesis `hi₀`/`hi₁` ensures that the
coordinate `i` is not already fixed in the rectangles before extension.
-/
lemma cover_all_inputs_extend_union (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true → ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true,  ∀ x, x i = true  → f x = true → ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    ∀ f ∈ F, ∀ x, f x = true →
      ∃ R ∈ (R0.image (fun R => Subcube.extend R i false) ∪
              R1.image (fun R => Subcube.extend R i true)),
        x ∈ₛ R := by
  classical
  intro f hf x hx
  cases hxi : x i
  ·
    -- Case `x i = false`: use the cover for the `false` branch.
    have hg : BFunc.restrictCoord f i false ∈ F.restrict i false :=
      (Family.mem_restrict).2 ⟨f, hf, rfl⟩
    have hx' : BFunc.restrictCoord f i false x = true := by
      simpa [restrictCoord_agrees (f := f) (j := i) (b := false)
              (x := x) hxi] using hx
    obtain ⟨R, hR, hxR⟩ := hcov0 _ hg x hxi hx'
    refine ⟨Subcube.extend R i false, ?_, ?_⟩
    · refine Finset.mem_union.mpr ?_
      refine Or.inl ?_
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    ·
      have hiR : i ∉ R.idx := hi0 R hR
      have : x ∈ₛ Subcube.extend R i false :=
        (Subcube.mem_extend_iff (R := R) (i := i) (b := false)
            (x := x) hiR).2 ⟨hxi, hxR⟩
      simpa using this
  ·
    -- Case `x i = true`.
    have hg : BFunc.restrictCoord f i true ∈ F.restrict i true :=
      (Family.mem_restrict).2 ⟨f, hf, rfl⟩
    have hx' : BFunc.restrictCoord f i true x = true := by
      simpa [restrictCoord_agrees (f := f) (j := i) (b := true)
              (x := x) hxi] using hx
    obtain ⟨R, hR, hxR⟩ := hcov1 _ hg x hxi hx'
    refine ⟨Subcube.extend R i true, ?_, ?_⟩
    · refine Finset.mem_union.mpr ?_
      refine Or.inr ?_
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    ·
      have hiR : i ∉ R.idx := hi1 R hR
      have : x ∈ₛ Subcube.extend R i true :=
        (Subcube.mem_extend_iff (R := R) (i := i) (b := true)
            (x := x) hiR).2 ⟨hxi, hxR⟩
      simpa using this

/-‐-
Convenience wrappers for dropping and re‑introducing a fixed coordinate.
`restrictDrop` limits the family to a Boolean branch and ignores the supplied
set of free coordinates, while `extendDrop` reinstates the fixed coordinate in a
subcube.  These operations mirror the steps of the recursive cover
construction.
-/

/-- Restrict the family `F` to the Boolean branch fixing coordinate `i` to `b`.
The argument `_A` records the set of remaining coordinates and is presently
unused. -/
noncomputable def restrictDrop (F : Family n) (i : Fin n) (b : Bool)
    (_A : Finset (Fin n)) : Family n :=
  F.restrict i b

/-- Extend a subcube from the smaller branch by reintroducing the fixed
coordinate `i` with value `b`.  This is the geometric counterpart to
`restrictDrop`. -/
def extendDrop (R : Subcube n) (i : Fin n) (b : Bool) : Subcube n :=
  Subcube.extend R i b

/-- Membership in the extended subcube corresponds to membership in the original
subcube together with the fixed coordinate. -/
lemma mem_extendDrop_iff {R : Subcube n} {i : Fin n} {b : Bool}
    {x : Point n} (hi : i ∉ R.idx) :
    (extendDrop (R := R) (i := i) (b := b)).mem x ↔ x i = b ∧ R.mem x := by
  simpa [extendDrop] using
    (Subcube.mem_extend_iff (R := R) (i := i) (b := b) (x := x) (hi := hi))

/--
Combines covers of the restricted families `F.restrict i false` and
`F.restrict i true` into a cover of the original family `F`.  Each subcube in
the branch covers is assumed not to fix the splitting coordinate `i`; after
extension with the corresponding value of `i`, their union forms a cover for
`F`, and its size is bounded by the sum of branch sizes.
-/
lemma extend_union_cover (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hmono0 : ∀ R ∈ R0, Subcube.monochromaticForFamily R (F.restrict i false))
    (hmono1 : ∀ R ∈ R1, Subcube.monochromaticForFamily R (F.restrict i true))
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true → ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true,  ∀ x, x i = true  → f x = true → ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ R0.card + R1.card := by
  classical
  -- The final cover extends rectangles from both branches via `extendDrop`
  -- and unites the results.
  let Rset :=
    R0.image (fun R => extendDrop (R := R) (i := i) (b := false)) ∪
      R1.image (fun R => extendDrop (R := R) (i := i) (b := true))
  refine ⟨Rset, ?mono, ?cov, ?card⟩
  · -- Monochromaticity transfers from each branch to the corresponding extension.
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · -- Case: `R` comes from the `false` branch.
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hmonoS := hmono0 S hS
      have hiS : i ∉ S.idx := hi0 S hS
      -- Extend monochromaticity to the original family.
      -- `extendDrop` is definitionally `Subcube.extend`.
      simpa [extendDrop] using
        (Subcube.monochromaticForFamily_extend_restrict (F := F)
          (R := S) (i := i) (b := false) hiS hmonoS)
    · -- Case: `R` comes from the `true` branch.
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hmonoS := hmono1 S hS
      have hiS : i ∉ S.idx := hi1 S hS
      simpa [extendDrop] using
        (Subcube.monochromaticForFamily_extend_restrict (F := F)
          (R := S) (i := i) (b := true) hiS hmonoS)
  · -- Coverage follows from the branch covers via `cover_all_inputs_extend_union`.
    exact cover_all_inputs_extend_union (F := F) (i := i)
      (R0 := R0) (R1 := R1) hcov0 hcov1 hi0 hi1
  · -- The cardinality of the combined cover is bounded by the sum of branch sizes.
    -- Rewrite the definition of `Rset` to reuse the disjointness bound.
    simpa [Rset, extendDrop] using
      (card_extend_union_le (i := i) (R0 := R0) (R1 := R1) hi0 hi1)

/--
Pointwise version of `extend_union_cover`.  The monochromaticity assumptions
are now per function in the respective branch families.  After extending and
uniting the branch rectangles we obtain a cover of the original family where
every function is constant on every resulting rectangle.
-/
lemma extend_union_cover_pointwise (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hmono0 : ∀ R ∈ R0, ∀ g ∈ F.restrict i false,
        Subcube.monochromaticFor R g)
    (hmono1 : ∀ R ∈ R1, ∀ g ∈ F.restrict i true,
        Subcube.monochromaticFor R g)
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true →
        ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true,  ∀ x, x i = true  → f x = true →
        ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ R0.card + R1.card := by
  classical
  -- Final cover is the same union, now expressed via `extendDrop`.
  let Rset :=
    R0.image (fun R => extendDrop (R := R) (i := i) (b := false)) ∪
      R1.image (fun R => extendDrop (R := R) (i := i) (b := true))
  refine ⟨Rset, ?mono, ?cov, ?card⟩
  · -- Pointwise monochromaticity: treat rectangles coming from each branch.
    intro f hf R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hiS : i ∉ S.idx := hi0 S hS
      -- The restriction of `f` belongs to the false branch.
      have hf0 : BFunc.restrictCoord f i false ∈ F.restrict i false :=
        (Family.mem_restrict).2 ⟨f, hf, rfl⟩
      have hmonoS := hmono0 S hS _ hf0
      -- Convert `extendDrop` back to `Subcube.extend` to apply the lemma.
      simpa [extendDrop] using
        (Subcube.monochromaticFor_extend_restrict
          (f := f) (R := S) (i := i) (b := false) hiS hmonoS)
    · rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hiS : i ∉ S.idx := hi1 S hS
      have hf1 : BFunc.restrictCoord f i true ∈ F.restrict i true :=
        (Family.mem_restrict).2 ⟨f, hf, rfl⟩
      have hmonoS := hmono1 S hS _ hf1
      simpa [extendDrop] using
        (Subcube.monochromaticFor_extend_restrict
          (f := f) (R := S) (i := i) (b := true) hiS hmonoS)
  · -- Coverage: reuse the previous lemma.
    exact cover_all_inputs_extend_union (F := F) (i := i)
      (R0 := R0) (R1 := R1) hcov0 hcov1 hi0 hi1
  · -- Cardinality bound identical to the family-level case.
    simpa [Rset, extendDrop] using
      (card_extend_union_le (i := i) (R0 := R0) (R1 := R1) hi0 hi1)

/--
`CoverRes F k` bundles a collection of rectangles together with proofs that
each is monochromatic for the family `F`, that all `1`-inputs of `F` lie in some
rectangle, and that the total number of rectangles does not exceed `k`.
This record will streamline reasoning about the recursive cover construction.
-/
structure CoverRes (F : Family n) (k : ℕ) where
  rects   : Finset (Subcube n)
  mono    : ∀ R ∈ rects, Subcube.monochromaticForFamily R F
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ rects, x ∈ₛ R
  card_le : rects.card ≤ k

/--
Package the union step of two branch covers into a `CoverRes`.  Given covers of
the restricted families `F.restrict i false` and `F.restrict i true` that avoid
fixing the splitting coordinate `i`, the resulting cover for `F` has at most
`|R0| + |R1|` rectangles.
-/
noncomputable def glue_step (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hmono0 : ∀ R ∈ R0, Subcube.monochromaticForFamily R (F.restrict i false))
    (hmono1 : ∀ R ∈ R1, Subcube.monochromaticForFamily R (F.restrict i true))
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true → ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true,  ∀ x, x i = true  → f x = true → ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    CoverRes (F := F) (R0.card + R1.card) := by
  classical
  -- Use classical choice to extract the explicit cover from the existence proof.
  let h :=
    extend_union_cover (F := F) (i := i) (R0 := R0) (R1 := R1)
      hmono0 hmono1 hcov0 hcov1 hi0 hi1
  refine
    { rects   := Classical.choose h
      , mono    := (Classical.choose_spec h).1
      , covers  := (Classical.choose_spec h).2.1
      , card_le := (Classical.choose_spec h).2.2 }

/--
Glue two branch covers after normalising them to forget the splitting
coordinate.  The hypotheses `hins₀`/`hins₁` state that every function in
the respective branch is insensitive to `i`, allowing
`cover_normalize_branch` to drop `i` from all rectangles.  The resulting
cover contains at most `k₀ + k₁` rectangles.  This lemma will be the
workhorse for the recursive construction of `buildCoverLex3` once full
monochromaticity and coverage proofs are threaded through the recursion.-/
noncomputable def glue_branch_covers (F : Family n) (i : Fin n)
    {k₀ k₁ : ℕ}
    (cover₀ : CoverRes (F := F.restrict i false) k₀)
    (cover₁ : CoverRes (F := F.restrict i true)  k₁)
    (hins₀ : ∀ f ∈ F.restrict i false, coordSensitivity f i = 0)
    (hins₁ : ∀ f ∈ F.restrict i true,  coordSensitivity f i = 0) :
    CoverRes (F := F) (k₀ + k₁) := by
  classical
  -- Normalise both branch covers so that no rectangle fixes the coordinate `i`.
  let hnorm₀ :=
    cover_normalize_branch (F_b := F.restrict i false) (i := i) (b := false)
      (Rb := cover₀.rects) cover₀.mono
      (by
        intro f hf x hxi hx
        exact cover₀.covers f hf x hx)
      (hins := hins₀)
  let R₀ := Classical.choose hnorm₀
  have hnorm₀_spec := Classical.choose_spec hnorm₀
  have hmono₀ : ∀ R ∈ R₀, Subcube.monochromaticForFamily R (F.restrict i false) :=
    hnorm₀_spec.1
  have hcov₀ : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true → ∃ R ∈ R₀, x ∈ₛ R :=
    hnorm₀_spec.2.1
  have hi₀ : ∀ R ∈ R₀, i ∉ R.idx := hnorm₀_spec.2.2.1
  have hcard₀ : R₀.card ≤ cover₀.rects.card := hnorm₀_spec.2.2.2
  let hnorm₁ :=
    cover_normalize_branch (F_b := F.restrict i true) (i := i) (b := true)
      (Rb := cover₁.rects) cover₁.mono
      (by
        intro f hf x hxi hx
        exact cover₁.covers f hf x hx)
      (hins := hins₁)
  let R₁ := Classical.choose hnorm₁
  have hnorm₁_spec := Classical.choose_spec hnorm₁
  have hmono₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R (F.restrict i true) :=
    hnorm₁_spec.1
  have hcov₁ : ∀ f ∈ F.restrict i true, ∀ x, x i = true → f x = true → ∃ R ∈ R₁, x ∈ₛ R :=
    hnorm₁_spec.2.1
  have hi₁ : ∀ R ∈ R₁, i ∉ R.idx := hnorm₁_spec.2.2.1
  have hcard₁ : R₁.card ≤ cover₁.rects.card := hnorm₁_spec.2.2.2
  -- Glue the normalised covers and propagate the cardinality bound.
  let glued :=
    glue_step (F := F) (i := i) (R0 := R₀) (R1 := R₁)
      hmono₀ hmono₁ hcov₀ hcov₁ hi₀ hi₁
  have hbound₀ : R₀.card ≤ k₀ :=
    le_trans hcard₀ cover₀.card_le
  have hbound₁ : R₁.card ≤ k₁ :=
    le_trans hcard₁ cover₁.card_le
  have hsum : R₀.card + R₁.card ≤ k₀ + k₁ :=
    add_le_add hbound₀ hbound₁
  refine
    { rects   := glued.rects
      , mono    := glued.mono
      , covers  := glued.covers
      , card_le := le_trans glued.card_le hsum }

/--
Build a `CoverRes` for the empty family.  With no functions present there are
no `1`-inputs to cover, so the empty set of rectangles suffices.
-/
noncomputable def CoverRes.empty (n : ℕ) :
    CoverRes (F := (∅ : Family n)) 0 := by
  classical
  refine
    { rects := ∅
      , mono := ?_
      , covers := ?_
      , card_le := by simp }
  · intro R hR; cases hR
  · intro f hf; cases hf

/--
Build a `CoverRes` for a constant family: the full cube is the sole rectangle.
Every function in `F` evaluates to the same Boolean `b` on all inputs, so that
rectangle trivially covers all `1`-inputs and is monochromatic for the family.
-/
noncomputable def CoverRes.const (F : Family n) (b : Bool)
    (hconst : ∀ f ∈ F, ∀ x, f x = b) :
    CoverRes (F := F) 1 := by
  classical
  -- The full cube as a subcube with no fixed coordinates.
  let R : Subcube n :=
    { idx := ∅
      , val := by
          intro i hi
          exact False.elim (Finset.notMem_empty _ hi) }
  -- Membership in `R` is trivial for any point.
  have hmem : ∀ x : Point n, x ∈ₛ R := by
    intro x i hi; cases hi
  refine
    { rects := {R}
      , mono := ?_
      , covers := ?_
      , card_le := by simp }
  · intro R' hR'
    have hR : R' = R := by simpa using Finset.mem_singleton.mp hR'
    subst hR
    refine ⟨b, ?_⟩
    intro f hf x hx
    simpa using hconst f hf x
  · intro f hf x hx
    exact ⟨R, by simp, hmem x⟩

/-
`CoverResP` relaxes `CoverRes` by requiring only
*pointwise* monochromaticity.  Each function in the family is
constant on every rectangle in `rects`, but different functions may
take different constant values.  This weaker invariant is enough for
later constructions that only query rectangles for the presence of a
`true` function value and avoids contradictions when constantly `false`
functions coexist with `true` ones.-/
structure CoverResP (F : Family n) (k : ℕ) where
  /-- Collection of rectangles forming the cover. -/
  rects   : Finset (Subcube n)
  /-- Every function of the family is constant on every rectangle
      in the cover. -/
  monoPw  : ∀ f ∈ F, ∀ R ∈ rects, Subcube.monochromaticFor R f
  /-- Every `1`-input of every function is contained in some
      rectangle of the cover. -/
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ rects, x ∈ₛ R
  /-- Cardinality bound on the number of rectangles. -/
  card_le : rects.card ≤ k

/--
Trivial cover for the empty family using no rectangles.  All fields are
discharged by empty‑set reasoning.-/
noncomputable def CoverResP.empty (n : ℕ) :
    CoverResP (F := (∅ : Family n)) 0 := by
  classical
  refine
    { rects := ∅
      , monoPw := ?_
      , covers := ?_
      , card_le := by simp }
  · intro f hf R hR; cases hf
  · intro f hf x hx; cases hf

/--
Cover consisting of the full cube for a family of functions all
constant with the same Boolean `b`.-/
noncomputable def CoverResP.const (F : Family n) (b : Bool)
    (hconst : ∀ f ∈ F, ∀ x, f x = b) :
    CoverResP (F := F) 1 := by
  classical
  -- The full cube as a subcube with no fixed coordinates.
  let R : Subcube n :=
    { idx := ∅
      , val := by
          intro i hi
          exact False.elim (Finset.notMem_empty _ hi) }
  have hmem : ∀ x : Point n, x ∈ₛ R := by
    intro x i hi; cases hi
  refine
    { rects := {R}
      , monoPw := ?_
      , covers := ?_
      , card_le := by simp }
  · intro f hf R' hR'
    have hR : R' = R := by simpa using Finset.mem_singleton.mp hR'
    subst hR
    refine ⟨b, ?_⟩
    intro x hx
    simpa using hconst f hf x
  · intro f hf x hx
    exact ⟨R, by simp, hmem x⟩

/--
Cover consisting of the full cube for a family where each function is
individually constant (potentially with different Boolean values).  All
functions are constant on the unique rectangle `R`, so the cover contains
exactly one subcube.
-/
noncomputable def CoverResP.constFamily (F : Family n)
    (hconst : ∀ f ∈ F, ∀ x y, f x = f y) :
    CoverResP (F := F) 1 := by
  classical
  -- The full cube without fixed coordinates.
  let R : Subcube n :=
    { idx := ∅
      , val := by
          intro i hi
          exact False.elim (Finset.notMem_empty _ hi) }
  have hmem : ∀ x : Point n, x ∈ₛ R := by
    intro x i hi; cases hi
  -- Use the all-false point to pin down the constant value of each function.
  let x₀ : Point n := fun _ => false
  refine
    { rects := {R}
      , monoPw := ?_
      , covers := ?_
      , card_le := by simp }
  · intro f hf R' hR'
    have hR : R' = R := by simpa using Finset.mem_singleton.mp hR'
    subst hR
    refine ⟨f x₀, ?_⟩
    intro x hx
    simpa [x₀] using hconst f hf x x₀
  · intro f hf x hx
    exact ⟨R, by simp, hmem x⟩

namespace CoverRes

variable {n : ℕ} {F : Family n} {k : ℕ}

/--
Convert a cover with family-level monochromaticity into a pointwise cover.  The
resulting `CoverResP` retains the original rectangles and coverage proof while
allowing each function to have its own colour on the rectangles.
-/
noncomputable def toCoverResP (cover : CoverRes F k) :
    CoverResP F k := by
  classical
  refine
    { rects := cover.rects
      , monoPw := ?_
      , covers := cover.covers
      , card_le := cover.card_le }
  intro f hf R hR
  rcases cover.mono R hR with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  exact hb f hf hx

end CoverRes

/--
Exhaustive cover obtained by listing all points of the Boolean cube as
zero‑dimensional subcubes.  This serves as the base case for the recursive
construction when the dimension `n` is sufficiently small compared to the
entropy budget `h`.  Every rectangle is a singleton cube and hence
monochromatic for each function individually.  The cardinality bound follows
from `card_subcube_le_mBound`.
-/
noncomputable def CoverResP.pointCover (F : Family n) (h : ℕ)
    (hn : 0 < n) (hbase : n ≤ 5 * h) :
    CoverResP (F := F) (k := Cover2.mBound n h) := by
  classical
  refine
    { rects := (Finset.univ : Finset (Point n)).image
        (fun x : Point n =>
          { idx := Finset.univ
            , val := fun i _ => x i })
      , monoPw := ?_
      , covers := ?_
      , card_le := ?_ }
  · intro f hf R hR
    rcases Finset.mem_image.mp hR with ⟨x, -, rfl⟩
    refine ⟨f x, ?_⟩
    intro y hy
    -- Membership in the fully frozen cube forces equality with `x`.
    have hxy : y = x := by
      funext i
      have := hy i (by simp)
      simpa using this
    simpa [hxy]
  · intro f hf x hx
    refine ⟨{ idx := Finset.univ, val := fun i _ => x i }, ?_, ?_⟩
    · refine Finset.mem_image.mpr ?_
      exact ⟨x, by simp, rfl⟩
    · -- The point `x` satisfies all fixed coordinates of its cube.
      intro i hi; simp
  · -- Cardinality bound: first bound the number of point subcubes by the
    -- number of points `2^n`, then compare against the total number of
    -- subcubes `3^n` and finally apply `card_subcube_le_mBound`.
    have hpts :
        ((Finset.univ : Finset (Point n)).image
            (fun x : Point n =>
              ({ idx := Finset.univ
                  , val := fun i _ => x i } : Subcube n))).card
          ≤ (Finset.univ : Finset (Point n)).card :=
      Finset.card_image_le
        (s := (Finset.univ : Finset (Point n)))
        (f := fun x : Point n => ({ idx := Finset.univ, val := fun i _ => x i } : Subcube n))
    have hpoint : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
      classical
      simpa [Fintype.card_fun, Fintype.card_fin] using
        (Finset.card_univ : (Finset.univ : Finset (Point n)).card = Fintype.card (Point n))
    have hsubcube : Fintype.card (Boolcube.Subcube n) = 3 ^ n :=
      Cover2.card_subcube (n := n)
    have h2le3 : 2 ^ n ≤ 3 ^ n := by
      have : (2 : ℕ) ≤ 3 := by decide
      exact Nat.pow_le_pow_left this n
    have hsub : Fintype.card (Boolcube.Subcube n) ≤ Cover2.mBound n h :=
      Cover2.card_subcube_le_mBound (n := n) (h := h) hn hbase
    -- Chain the inequalities together.
    have hpts_le_subcube :
        ((Finset.univ : Finset (Point n)).image
            (fun x : Point n => ({ idx := Finset.univ, val := fun i _ => x i } : Subcube n))).card
          ≤ Fintype.card (Boolcube.Subcube n) := by
      -- Start from `hpts` and use `2^n ≤ 3^n` to replace points by subcubes.
      have hpoints_le_sub :
          (Finset.univ : Finset (Point n)).card ≤ Fintype.card (Boolcube.Subcube n) := by
        simpa [hpoint, hsubcube] using h2le3
      exact hpts.trans hpoints_le_sub
    exact hpts_le_subcube.trans hsub

/--
Upgrade the point enumeration cover to the next entropy budget.  This wrapper
reuses `CoverResP.pointCover` but expresses its cardinality bound in terms of
`Cover2.mBound n (h + 1)`, which will match the recursive construction once
branching is introduced.
-/
noncomputable def CoverResP.pointCover_succ (F : Family n) (h : ℕ)
    (hn : 0 < n) (hbase : n ≤ 5 * h) :
    CoverResP (F := F) (k := Cover2.mBound n (h + 1)) := by
  classical
  -- Start from the basic point cover.
  let cover := CoverResP.pointCover (F := F) (h := h) hn hbase
  -- Upgrade the cardinality bound using monotonicity of `mBound`.
  have hle : Cover2.mBound n h ≤ Cover2.mBound n (h + 1) :=
    Cover2.mBound_le_succ (n := n) (h := h)
  refine
    { rects := cover.rects
      , monoPw := cover.monoPw
      , covers := cover.covers
      , card_le := le_trans cover.card_le hle }
/--
Lift a cover for the subfamily obtained by erasing a constantly `false`
function back to the original family.  Since the erased function never takes
the value `true`, the rectangles and their cardinality bound are reused
verbatim.  Pointwise monochromaticity extends to the deleted function because
it is itself constant `false` on every rectangle.-/
noncomputable def CoverResP.lift_erase_false
    {F : Family n} {f₀ : BFunc n} {k : ℕ}
    (hf₀F : f₀ ∈ F) (hf₀false : ∀ x, f₀ x = false)
    (cover' : CoverResP (F := F.erase f₀) k) :
    CoverResP (F := F) k := by
  classical
  refine
    { rects := cover'.rects
      , monoPw := ?_
      , covers := ?_
      , card_le := by simpa using cover'.card_le }
  · intro f hf R hR
    by_cases hf0 : f = f₀
    · subst hf0
      refine ⟨false, ?_⟩
      intro x hx; simpa using hf₀false x
    ·
      have hf' : f ∈ F.erase f₀ := Finset.mem_erase.mpr ⟨hf0, hf⟩
      exact cover'.monoPw f hf' R hR
  · intro f hf x hx
    by_cases hf0 : f = f₀
    · subst hf0
      have : False := by simpa [hf₀false x] using hx
      exact False.elim this
    ·
      have hf' : f ∈ F.erase f₀ := Finset.mem_erase.mpr ⟨hf0, hf⟩
      exact cover'.covers f hf' x hx

/--
Upgrade a constant-family cover to the next entropy budget.  Starting from the
singleton cover produced by `CoverResP.const`, this wrapper merely inflates the
cardinality bound to `Cover2.mBound n (h + 1)`.
-/
noncomputable def CoverResP.const_mBound (F : Family n) (b : Bool) (h : ℕ)
    (hconst : ∀ f ∈ F, ∀ x, f x = b) (hn : 0 < n) :
    CoverResP (F := F) (k := Cover2.mBound n (h + 1)) := by
  classical
  -- Begin with the basic constant cover.
  let cover := CoverResP.const (F := F) (b := b) hconst
  -- Any positive `mBound` dominates the singleton bound.
  have hk : 1 ≤ Cover2.mBound n (h + 1) :=
    Nat.succ_le_of_lt (Cover2.mBound_pos (n := n) (h := h + 1) hn)
  refine
    { rects := cover.rects
      , monoPw := cover.monoPw
      , covers := cover.covers
      , card_le := le_trans cover.card_le hk }

/--
Upgrade a constant-family cover to an arbitrary entropy budget `h` without
adding any rectangles.  Starting from the singleton cover `CoverResP.const`,
this simply enlarges the cardinality bound to `Cover2.mBound n h`.
-/
noncomputable def CoverResP.const_mBound_exact (F : Family n) (b : Bool) (h : ℕ)
    (hconst : ∀ f ∈ F, ∀ x, f x = b) (hn : 0 < n) :
    CoverResP (F := F) (k := Cover2.mBound n h) := by
  classical
  -- Begin with the basic constant cover of size one.
  let cover := CoverResP.const (F := F) (b := b) hconst
  -- Show that the requested `mBound` budget dominates the singleton.
  have hk : 1 ≤ Cover2.mBound n h :=
    Nat.succ_le_of_lt (Cover2.mBound_pos (n := n) (h := h) hn)
  -- Repackage the cover under the larger cardinality bound.
  refine
    { rects := cover.rects
      , monoPw := cover.monoPw
      , covers := cover.covers
      , card_le := le_trans cover.card_le hk }

/--
Specialised orientation of `exists_branch_measure_drop_of_sensitive` to the
full coordinate set.  Whenever the family `F` has a sensitive coordinate,
restricting along that coordinate strictly decreases the three-component
measure `measureLex3` in both Boolean branches.  This lemma records the
measure drop that will justify recursive calls in `buildCoverLex3` once
sensitive branching replaces the current placeholder implementation.
-/
lemma exists_branch_measure_drop_univ {n : ℕ} (F : Family n)
    (hsens : ∃ i : Fin n, sensitiveCoord F i) :
    ∃ i : Fin n, ∀ b : Bool,
        measureLex3Rel (measureLex3 (F.restrict i b) (Finset.univ.erase i))
          (measureLex3 F Finset.univ) := by
  classical
  -- Choose a sensitive coordinate and apply the general branching lemma on
  -- the universal set of coordinates.
  rcases hsens with ⟨i, hi⟩
  have hiA : (i : Fin n) ∈ (Finset.univ : Finset (Fin n)) := by simp
  obtain ⟨j, _hjA, hdrop⟩ :=
    exists_branch_measure_drop_of_sensitive
      (F := F) (A := (Finset.univ : Finset (Fin n))) ⟨i, hiA, hi⟩
  exact ⟨j, hdrop⟩

/--
Convenient reformulation of `exists_branch_measure_drop_univ` using
`restrictDrop`.  This emphasises the explicit coordinate removal that will
drive the upcoming recursive branch in `buildCoverLex3`.
-/
lemma exists_branch_measure_drop_restrictDrop_univ {n : ℕ} (F : Family n)
    (hsens : ∃ i : Fin n, sensitiveCoord F i) :
    ∃ i : Fin n, ∀ b : Bool,
        measureLex3Rel
          (measureLex3 (restrictDrop (F := F) (i := i) (b := b)
              (Finset.univ : Finset (Fin n)))
            ((Finset.univ : Finset (Fin n)).erase i))
          (measureLex3 F (Finset.univ : Finset (Fin n))) := by
  simpa [restrictDrop] using
    (exists_branch_measure_drop_univ (F := F) (hsens := hsens))

/-- If a sensitive coordinate lies inside a set `A` whose size does not exceed
the available budget `h`, then the budget is necessarily positive.  This
elementary lemma serves as a building block for eliminating the temporary
axiom `no_sensitive_at_zero` in the recursive cover construction. -/
lemma budget_pos_of_sensitive {n : ℕ} (F : Family n) (A : Finset (Fin n))
    {h : ℕ} (hcard : A.card ≤ h)
    (hsens : ∃ i ∈ A, sensitiveCoord F i) : 0 < h := by
  classical
  rcases hsens with ⟨i, hiA, _⟩
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
  exact lt_of_lt_of_le hApos hcard

/--
If the available budget `h` is zero, a sensitive coordinate cannot remain inside
`A`.  This is an immediate corollary of `budget_pos_of_sensitive` and formally
replaces the former axiom `no_sensitive_at_zero` in termination arguments.
-/
lemma no_sensitive_of_budget_zero {n : ℕ} (F : Family n) (A : Finset (Fin n))
    {h : ℕ} (hcard : A.card ≤ h) (hzero : h = 0) :
    ¬ ∃ i ∈ A, sensitiveCoord F i := by
  intro hsens
  have hpos : 0 < h :=
    budget_pos_of_sensitive (F := F) (A := A) (h := h)
      (hcard := hcard) hsens
  simpa [hzero] using hpos

/--
Specialised version of `no_sensitive_of_budget_zero` for the full set of
coordinates.  If the entropy budget `h` has been exhausted and still dominates
the dimension `n`, then the family cannot possess a sensitive coordinate.
This tiny wrapper is convenient when working with `buildCoverLex3`, which
always starts from the universal coordinate set.
-/
lemma no_sensitive_of_budget_zero_univ {n : ℕ} (F : Family n) {h : ℕ}
    (hcard : n ≤ h) (hzero : h = 0) :
    ¬ ∃ i : Fin n, sensitiveCoord F i := by
  -- Convert the numeric constraint `n ≤ h` into the form expected by
  -- `no_sensitive_of_budget_zero` and specialise that lemma to `A = univ`.
  have hcard' : (Finset.univ : Finset (Fin n)).card ≤ h := by
    simpa [Finset.card_univ] using hcard
  have haux :=
    no_sensitive_of_budget_zero (F := F)
      (A := (Finset.univ : Finset (Fin n))) (hcard := hcard') (hzero := hzero)
  -- Repackage the statement without the explicit membership proof.
  simpa using haux

/--
Fixing a sensitive coordinate strictly decreases the three‑component
measure `measureLex3`.  The set of available coordinates loses `i`,
ensuring progress in the third component of the lexicographic measure.
-/
lemma measureLex3_restrictDrop_lt {n : ℕ} (F : Family n)
    (A : Finset (Fin n)) {i : Fin n} (hi : i ∈ A) (b : Bool) :
      measureLex3Rel
        (measureLex3 (restrictDrop (F := F) (i := i) (b := b) A)
          (A.erase i))
        (measureLex3 F A) := by
  -- This is a direct application of `measureLex3_restrict_lt_dim`.
  simpa [restrictDrop] using
    (measureLex3_restrict_lt_dim (F := F) (A := A) (i := i) hi (b := b))

/-- Specialised version of `measureLex3_restrictDrop_lt` for the full coordinate
set.  Fixing a sensitive coordinate strictly decreases the three-component
measure on `Finset.univ`.  This variant will streamline termination arguments
for recursive constructions that always operate on the full set of remaining
coordinates. -/
lemma measureLex3_restrictDrop_univ_lt {n : ℕ} (F : Family n)
    {i : Fin n} (b : Bool) :
      measureLex3Rel
        (measureLex3 (restrictDrop (F := F) (i := i) (b := b)
            (Finset.univ : Finset (Fin n)))
          ((Finset.univ : Finset (Fin n)).erase i))
        (measureLex3 F (Finset.univ : Finset (Fin n))) := by
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := by simp
  simpa using
    (measureLex3_restrictDrop_lt (F := F)
      (A := (Finset.univ : Finset (Fin n))) (i := i) (hi := hi) (b := b))

/--
Starting with rectangle collections for the restricted families that avoid the
splitting coordinate `i`, extending and uniting them yields a cover of the
original family with at most `|R0| + |R1|` rectangles.
-/
noncomputable def glue_step_pw (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hmono0 : ∀ R ∈ R0, ∀ g ∈ F.restrict i false,
        Subcube.monochromaticFor R g)
    (hmono1 : ∀ R ∈ R1, ∀ g ∈ F.restrict i true,
        Subcube.monochromaticFor R g)
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true →
        ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true,  ∀ x, x i = true  → f x = true →
        ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    CoverResP (F := F) (R0.card + R1.card) := by
  classical
  let h :=
    extend_union_cover_pointwise (F := F) (i := i) (R0 := R0) (R1 := R1)
      hmono0 hmono1 hcov0 hcov1 hi0 hi1
  refine
    { rects := Classical.choose h
      , monoPw := (Classical.choose_spec h).1
      , covers := (Classical.choose_spec h).2.1
      , card_le := (Classical.choose_spec h).2.2 }

/--
Glue two branch covers after normalising them to forget the splitting
coordinate.  The hypotheses `hins₀`/`hins₁` state that every function in the
respective branch is insensitive to `i`, allowing `cover_normalize_branch_pointwise`
to drop `i` from all rectangles.  The resulting cover contains at most
`k₀ + k₁` rectangles.
-/
noncomputable def glue_branch_coversPw (F : Family n) (i : Fin n)
    [Fintype (Point n)]
    {k₀ k₁ : ℕ}
    (cover₀ : CoverResP (F := F.restrict i false) k₀)
    (cover₁ : CoverResP (F := F.restrict i true)  k₁)
    (hins₀ : ∀ f ∈ F.restrict i false, coordSensitivity f i = 0)
    (hins₁ : ∀ f ∈ F.restrict i true,  coordSensitivity f i = 0) :
    CoverResP (F := F) (k₀ + k₁) := by
  classical
  -- Normalise both branch covers to eliminate the splitting coordinate.
  let hnorm₀ :=
    cover_normalize_branch_pointwise (F_b := F.restrict i false) (i := i) (b := false)
      (Rb := cover₀.rects) (by
        intro R hR g hg; exact cover₀.monoPw g hg R hR)
      (by
        intro f hf x hxi hx; exact cover₀.covers f hf x hx)
      (hins := hins₀)
  let R₀ := Classical.choose hnorm₀
  have hnorm₀_spec := Classical.choose_spec hnorm₀
  let hnorm₁ :=
    cover_normalize_branch_pointwise (F_b := F.restrict i true) (i := i) (b := true)
      (Rb := cover₁.rects) (by
        intro R hR g hg; exact cover₁.monoPw g hg R hR)
      (by
        intro f hf x hxi hx; exact cover₁.covers f hf x hx)
      (hins := hins₁)
  let R₁ := Classical.choose hnorm₁
  have hnorm₁_spec := Classical.choose_spec hnorm₁
  -- Extract components of the normalisation results.
  have hmono₀ : ∀ R ∈ R₀, ∀ g ∈ F.restrict i false,
      Subcube.monochromaticFor R g := hnorm₀_spec.1
  have hcov₀ : ∀ f ∈ F.restrict i false, ∀ x, x i = false → f x = true →
      ∃ R ∈ R₀, x ∈ₛ R := hnorm₀_spec.2.1
  have hi₀ : ∀ R ∈ R₀, i ∉ R.idx := hnorm₀_spec.2.2.1
  have hcard₀ : R₀.card ≤ cover₀.rects.card := hnorm₀_spec.2.2.2
  have hmono₁ : ∀ R ∈ R₁, ∀ g ∈ F.restrict i true,
      Subcube.monochromaticFor R g := hnorm₁_spec.1
  have hcov₁ : ∀ f ∈ F.restrict i true, ∀ x, x i = true → f x = true →
      ∃ R ∈ R₁, x ∈ₛ R := hnorm₁_spec.2.1
  have hi₁ : ∀ R ∈ R₁, i ∉ R.idx := hnorm₁_spec.2.2.1
  have hcard₁ : R₁.card ≤ cover₁.rects.card := hnorm₁_spec.2.2.2
  -- Glue the normalised covers and propagate cardinality bounds.
  let glued :=
    glue_step_pw (F := F) (i := i) (R0 := R₀) (R1 := R₁)
      hmono₀ hmono₁ hcov₀ hcov₁ hi₀ hi₁
  have hbound₀ : R₀.card ≤ k₀ := le_trans hcard₀ cover₀.card_le
  have hbound₁ : R₁.card ≤ k₁ := le_trans hcard₁ cover₁.card_le
  have hsum : R₀.card + R₁.card ≤ k₀ + k₁ := add_le_add hbound₀ hbound₁
  exact
    { rects := glued.rects
      , monoPw := glued.monoPw
      , covers := glued.covers
      , card_le := le_trans glued.card_le hsum }

/--
Gluing branch covers bounded by `mBound n h` yields a cover of the whole
family bounded by `mBound n (h + 1)`.  This lemma packages the cardinality
growth of `glue_branch_coversPw` into a convenient form for later use in the
recursive constructor.
-/
noncomputable def glue_branch_coversPw_mBound (F : Family n) (i : Fin n) (h : ℕ)
    [Fintype (Point n)]
    (cover₀ : CoverResP (F := F.restrict i false) (Cover2.mBound n h))
    (cover₁ : CoverResP (F := F.restrict i true)  (Cover2.mBound n h))
    (hins₀ : ∀ f ∈ F.restrict i false, coordSensitivity f i = 0)
    (hins₁ : ∀ f ∈ F.restrict i true,  coordSensitivity f i = 0) :
    CoverResP (F := F) (k := Cover2.mBound n (h + 1)) := by
  classical
  -- Glue the covers and upgrade the cardinality bound via `two_mul_mBound_le_succ`.
  let glued :=
    glue_branch_coversPw (F := F) (i := i)
      (cover₀ := cover₀) (cover₁ := cover₁) hins₀ hins₁
  -- The result is bounded by the sum of the branch cardinalities.
  have hsum : glued.rects.card ≤ 2 * Cover2.mBound n h := by
    simpa [two_mul] using glued.card_le
  -- Upgrade the estimate to the next entropy budget.
  have hbound : glued.rects.card ≤ Cover2.mBound n (h + 1) :=
    le_trans hsum (Cover2.two_mul_mBound_le_succ (n := n) (h := h))
  refine
    { rects := glued.rects
      , monoPw := glued.monoPw
      , covers := glued.covers
      , card_le := hbound }

-- `buildCoverLex3A` constructs a pointwise cover of a family `F` given a set
-- of available coordinates `A`.  Besides the insensitivity hypothesis `hA` on
-- coordinates outside `A`, we maintain the combinatorial budget invariant
-- `A.card ≤ h`.  This relation ensures that whenever a sensitive coordinate is
-- discovered, the remaining budget is necessarily positive, allowing recursive
-- calls with `h - 1`.
noncomputable def buildCoverLex3A (F : Family n) (A : Finset (Fin n)) (h : ℕ)
    [Fintype (Point n)] (hn : 0 < n)
    (hA : ∀ j ∉ A, ∀ f ∈ F, coordSensitivity f j = 0)
    (hcard : A.card ≤ h) :
    CoverResP (F := F) (k := Cover2.mBound n (h + 1)) := by
  classical
  by_cases hfalse : ∃ f ∈ F, ∀ x, f x = false
  ·
    -- Remove a constantly `false` function and recurse on the smaller family.
    let f₀ := Classical.choose hfalse
    have hf₀ := Classical.choose_spec hfalse
    have hf₀F : f₀ ∈ F := hf₀.1
    have hf₀false : ∀ x, f₀ x = false := hf₀.2
    have hA' : ∀ j ∉ A, ∀ f ∈ F.erase f₀, coordSensitivity f j = 0 := by
      intro j hj f hf
      exact hA j hj f (Finset.mem_of_mem_erase hf)
    refine
      CoverResP.lift_erase_false (F := F) (f₀ := f₀)
        (hf₀F := hf₀F) (hf₀false := hf₀false)
        (cover' := buildCoverLex3A (F := F.erase f₀) (A := A)
          (h := h) (hn := hn) (hA := hA') (hcard := hcard))
  ·
    -- No constantly `false` functions remain.
    by_cases hzero : h = 0
    ·
      -- With no budget left, the available coordinate set is empty.
      have hA0 : A = ∅ := by
        apply Finset.card_eq_zero.mp
        have : A.card ≤ 0 := by simpa [hzero] using hcard
        exact Nat.le_antisymm this (Nat.zero_le _)
      -- Specialise `no_sensitive_of_budget_zero` to conclude the absence of
      -- sensitive coordinates within `A` and combine with `hA` outside `A`.
      have hins : ∀ j : Fin n, ¬ sensitiveCoord F j := by
        intro j
        by_cases hjA : j ∈ A
        · have : False := by simpa [hA0] using hjA
          exact this.elim
        ·
          have hz := hA j hjA
          intro hcontr
          rcases hcontr with ⟨f, hfF, x, hx⟩
          have hzero' :=
            (coordSensitivity_eq_zero_iff (f := f) (i := j)).1 (hz f hfF) x
          exact hx hzero'
      have hconst : ∀ f ∈ F, ∀ x, f x = true :=
        all_true_of_no_sensitive_coord (F := F) (hins := hins)
          (hfalse := hfalse)
      -- With `h = 0`, the bound simplifies to `Cover2.mBound n 1`.
      have : h + 1 = 1 := by simpa [hzero]
      simpa [this] using
        (CoverResP.const_mBound (F := F) (b := true) (h := 0) hconst hn)
    ·
      -- Budget is still positive; obtain `0 < h` for recursive calls.
      have hpos : 0 < h := Nat.pos_of_ne_zero hzero
      by_cases hsens : ∃ i ∈ A, sensitiveCoord F i
      ·
        -- Choose a sensitive coordinate `i ∈ A` and branch on its value.
        classical
        let i := Classical.choose hsens
        have hiData := Classical.choose_spec hsens
        rcases hiData with ⟨hiA, hi⟩

        -- Prepare insensitivity hypotheses for recursive calls on each branch.
        have hA' :
            ∀ b, ∀ j ∉ A.erase i, ∀ f ∈ F.restrict i b,
              coordSensitivity f j = 0 := by
          intro b j hj f hf
          by_cases hji : j = i
          · subst hji
            exact coordSensitivity_family_restrict_self_zero (F := F) (i := i)
              (b := b) f hf
          ·
            rcases Family.mem_of_mem_restrict hf with ⟨f', hf'F, rfl⟩
            have hzero' :=
              hA j (by simpa [Finset.mem_erase, hji] using hj) f' hf'F
            exact
              coordSensitivity_restrict_eq_zero (f := f') (i := i) (j := j)
                (b := b) hzero'

        -- Both branches are insensitive to the chosen coordinate itself.
        have hins₀ : ∀ f ∈ F.restrict i false, coordSensitivity f i = 0 :=
          coordSensitivity_family_restrict_self_zero (F := F) (i := i)
            (b := false)
        have hins₁ : ∀ f ∈ F.restrict i true, coordSensitivity f i = 0 :=
          coordSensitivity_family_restrict_self_zero (F := F) (i := i)
            (b := true)
        have cover₀ :
            CoverResP (F := F.restrict i false) (k := Cover2.mBound n h) := by
          have hcard' : (A.erase i).card ≤ h - 1 := by
            -- From `A.card ≤ h` deduce `(A.erase i).card ≤ h - 1`.
            have hsucc' : (A.erase i).card.succ ≤ h := by
              have htmp : (A.erase i).card + 1 ≤ h := by
                simpa [← Finset.card_erase_add_one hiA] using hcard
              simpa [Nat.succ_eq_add_one] using htmp
            have hsucc'' : (A.erase i).card.succ ≤ (h - 1).succ := by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] using hsucc'
            exact Nat.succ_le_succ_iff.mp hsucc''
          have cover :=
            buildCoverLex3A
              (F := F.restrict i false) (A := A.erase i)
              (h := h - 1) (hn := hn) (hA := hA' false) (hcard := hcard')
          have : h - 1 + 1 = h := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
          simpa [this] using cover
        have cover₁ :
            CoverResP (F := F.restrict i true) (k := Cover2.mBound n h) := by
          have hcard' : (A.erase i).card ≤ h - 1 := by
            have hsucc' : (A.erase i).card.succ ≤ h := by
              have htmp : (A.erase i).card + 1 ≤ h := by
                simpa [← Finset.card_erase_add_one hiA] using hcard
              simpa [Nat.succ_eq_add_one] using htmp
            have hsucc'' : (A.erase i).card.succ ≤ (h - 1).succ := by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] using hsucc'
            exact Nat.succ_le_succ_iff.mp hsucc''
          have cover :=
            buildCoverLex3A
              (F := F.restrict i true) (A := A.erase i)
              (h := h - 1) (hn := hn) (hA := hA' true) (hcard := hcard')
          have : h - 1 + 1 = h := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
          simpa [this] using cover
        -- Glue the recursively obtained covers, upgrading the budget to `h + 1`.
        exact
          glue_branch_coversPw_mBound (F := F) (i := i) (h := h)
            (cover₀ := cover₀) (cover₁ := cover₁) hins₀ hins₁
      ·
        -- All remaining coordinates are insensitive; every function is constant.
        have hins_all : ∀ j : Fin n, ¬ sensitiveCoord F j := by
          intro j
          by_cases hjA : j ∈ A
          ·
            have haux := (not_exists.mp hsens) j
            exact fun h => haux ⟨hjA, h⟩
          ·
            have hz := hA j hjA
            intro hcontr
            rcases hcontr with ⟨f, hfF, x, hx⟩
            have hzero' :=
              (coordSensitivity_eq_zero_iff (f := f) (i := j)).1 (hz f hfF) x
            exact hx hzero'
        have hconst : ∀ f ∈ F, ∀ x, f x = true :=
          all_true_of_no_sensitive_coord (F := F) (hins := hins_all)
            (hfalse := hfalse)
        exact
          CoverResP.const_mBound (F := F) (b := true) (h := h) hconst hn

  termination_by
    measureLex3 F A
  decreasing_by
    classical
    -- Removing a constantly `false` function decreases the measure.
    let f₀ := Classical.choose hfalse
    have hf₀ := Classical.choose_spec hfalse
    have hf₀F : f₀ ∈ F := hf₀.1
    have hdrop₀ :
        measureLex3Rel (measureLex3 (F.erase f₀) A) (measureLex3 F A) :=
      measureLex3_erase_lt (F := F) (A := A) (f := f₀) hf₀F
    simpa using hdrop₀
    -- Restricting on the chosen sensitive coordinate strictly decreases.
    have hdrop_false :
        measureLex3Rel (measureLex3 (F.restrict i false) (A.erase i))
          (measureLex3 F A) :=
      measureLex3_restrict_lt_dim (F := F) (A := A) (i := i)
        (hi := hiA) (b := false)
    simpa using hdrop_false
    have hdrop_true :
        measureLex3Rel (measureLex3 (F.restrict i true) (A.erase i))
          (measureLex3 F A) :=
      measureLex3_restrict_lt_dim (F := F) (A := A) (i := i)
        (hi := hiA) (b := true)
    simpa using hdrop_true

noncomputable def buildCoverLex3 (F : Family n) (h : ℕ)
    [Fintype (Point n)] (hn : 0 < n) (hcard : n ≤ h) :
    CoverResP (F := F) (k := Cover2.mBound n (h + 1)) :=
  buildCoverLex3A (F := F) (A := (Finset.univ : Finset (Fin n))) (h := h)
    (hn := hn)
    (hA := by
      intro j hj f hf
      exact False.elim (hj (Finset.mem_univ j)))
    (hcard := by
      simpa [Finset.card_univ] using hcard)


/--
Expose the underlying rectangle set of a pointwise cover, relaxing the
cardinality bound from `k` to any `k' ≥ k`.  This mirrors `CoverRes.as_cover`
for the pointwise version `CoverResP` and will be convenient when presenting
`CoverResP` as an existential result.-/
lemma CoverResP.as_cover {n : ℕ} {F : Family n} {k k' : ℕ}
    (cover : CoverResP (F := F) k) (hk : k ≤ k') :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ k' := by
  refine ⟨cover.rects, ?_, cover.covers, ?_⟩
  · intro f hf R hR; exact cover.monoPw f hf R hR
  · exact le_trans cover.card_le hk

/--
  Present the cover constructed by `buildCoverLex3` in existential form.
  This wrapper exposes the set of rectangles together with their pointwise
  monochromaticity, coverage of all `true` inputs and the `mBound` cardinality
  bound.  It serves as a convenient interface for downstream developments that
  prefer an explicit witness over the structured `CoverResP` record.
-/
lemma cover_exists_mBound
  {n : ℕ} (F : Family n) (h : ℕ)
  [Fintype (Point n)] (hn : 0 < n) (hcard : n ≤ h) :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Cover2.mBound n (h + 1) := by
  classical
  -- Obtain the structured cover from the recursive constructor.
  let cover := buildCoverLex3 (F := F) (h := h) hn hcard
  -- Unpack it using `CoverResP.as_cover` while keeping the same bound.
  simpa using
    (CoverResP.as_cover (n := n) (F := F)
      (cover := cover) (hk := le_rfl))

/-
  A convenience variant of `cover_exists_mBound` that chooses a suitable
  budget `h` automatically.  Taking `h = n` satisfies the required constraint
  `n ≤ h`.
-/
lemma cover_exists_mBound_choose_h
  {n : ℕ} (F : Family n) [Fintype (Point n)] (hn : 0 < n) :
  ∃ h : ℕ, ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Cover2.mBound n (h + 1) := by
  classical
  -- Choose `h = n` and invoke the main existence lemma.
  refine ⟨n, ?_⟩
  simpa using
    (cover_exists_mBound (n := n) (F := F) (h := n)
      (hn := hn) (hcard := le_rfl))

/--
Turn the abstract cover packaged in a `CoverRes` into a concrete decision tree.
The resulting tree queries the rectangles in `cover.rects` in an arbitrary
order and returns `true` as soon as one of them matches the input.  Inputs not
belonging to any rectangle evaluate to `false`.
-/
noncomputable def CoverRes.toDecisionTree
    {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) : DecisionTree n :=
  DecisionTree.ofRectCover (n := n) false (F := F)
    cover.rects cover.mono

/--
Evaluating the tree produced from a `CoverRes` yields `true` on every input
`x` where some function `f ∈ F` outputs `true`.  This is the crucial bridge
between abstract covers and executable decision trees.
-/
lemma CoverRes.eval_true {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) {f : BFunc n} (hf : f ∈ F)
    {x : Point n} (hx : f x = true) :
    DecisionTree.eval_tree
        (CoverRes.toDecisionTree (n := n) (F := F) cover) x = true := by
  classical
  -- Assemble the list of coloured rectangles used by `ofRectCover`.
  let colored := cover.rects.attach.toList.map
    (fun R => (Classical.choose (cover.mono R.1 R.2), R.1))
  -- Prove that every rectangle containing `x` is coloured `true`.
  have hall : ∀ p ∈ colored, Subcube.mem p.2 x → p.1 = true := by
    intro p hp hxR
    -- Extract the source rectangle `R` from the mapped list.
    rcases List.mem_map.1 hp with ⟨r, hr, hpair⟩
    rcases r with ⟨R, hR⟩
    -- Identify the colour of the rectangle.
    have hb : Classical.choose (cover.mono R hR) = p.1 := by
      simpa [Prod.ext_iff] using congrArg Prod.fst hpair
    have hRe : R = p.2 := by
      simpa [Prod.ext_iff] using congrArg Prod.snd hpair
    -- On rectangle `R` all functions of `F` agree with the chosen colour.
    have hmono := cover.mono R hR
    have hxR' : Subcube.mem R x := by simpa [hRe] using hxR
    have hbval := (Classical.choose_spec hmono) f hf (x := x) hxR'
    subst hRe
    have hbtrue : Classical.choose hmono = true := by
      simpa [hbval] using hx
    simpa [hb] using hbtrue
  -- There exists at least one rectangle containing `x` thanks to `covers`.
  obtain ⟨R0, hR0, hxR0⟩ := cover.covers f hf x hx
  let p0 : Bool × Subcube n := (Classical.choose (cover.mono R0 hR0), R0)
  have hp0_mem : p0 ∈ colored := by
    have hattach' :
        (⟨R0, hR0⟩ : {R : Subcube n // R ∈ cover.rects}) ∈ cover.rects.attach := by
      simpa using (Finset.mem_attach (s := cover.rects) hR0)
    have hattach :
        (⟨R0, hR0⟩ : {R : Subcube n // R ∈ cover.rects}) ∈
            cover.rects.attach.toList := by
      simpa using (List.mem_toList.mpr hattach')
    exact List.mem_map.2 ⟨⟨R0, hR0⟩, hattach, rfl⟩
  have hex : ∃ p ∈ colored, Subcube.mem p.2 x := ⟨p0, hp0_mem, hxR0⟩
  -- Apply the generic list-based evaluation lemma.
  simpa [CoverRes.toDecisionTree, DecisionTree.ofRectCover, colored] using
    (DecisionTree.eval_ofRectCoverList_true_of_mem (n := n)
      (default := false) (colored := colored) (x := x) hex hall)

/--
Evaluating the tree produced from a `CoverRes` yields `false` on any input
where the chosen function evaluates to `false`.  Every rectangle containing
such a point must be coloured `false`, so the resulting decision tree returns
`false`.
-/
lemma CoverRes.eval_false {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) {f : BFunc n} (hf : f ∈ F)
    {x : Point n} (hx : f x = false) :
    DecisionTree.eval_tree
        (CoverRes.toDecisionTree (n := n) (F := F) cover) x = false := by
  classical
  -- Assemble the list of coloured rectangles as in `eval_true`.
  let colored := cover.rects.attach.toList.map
    (fun R => (Classical.choose (cover.mono R.1 R.2), R.1))
  -- Prove that every rectangle containing `x` carries the colour `false`.
  have hall : ∀ p ∈ colored, Subcube.mem p.2 x → p.1 = false := by
    intro p hp hxR
    rcases List.mem_map.1 hp with ⟨r, hr, hpair⟩
    rcases r with ⟨R, hR⟩
    -- Identify the colour chosen for rectangle `R`.
    have hb : Classical.choose (cover.mono R hR) = p.1 := by
      simpa [Prod.ext_iff] using congrArg Prod.fst hpair
    have hRe : R = p.2 := by
      simpa [Prod.ext_iff] using congrArg Prod.snd hpair
    -- Monochromaticity forces the colour to be `false` on `x`.
    have hmono := cover.mono R hR
    have hxR' : Subcube.mem R x := by simpa [hRe] using hxR
    have hbval := (Classical.choose_spec hmono) f hf (x := x) hxR'
    subst hRe
    have hbfalse : Classical.choose hmono = false := by
      simpa [hbval] using hx
    simpa [hb] using hbfalse
  -- Apply the generic list-based evaluation lemma specialised to `false`.
  simpa [CoverRes.toDecisionTree, DecisionTree.ofRectCover, colored] using
    (DecisionTree.eval_ofRectCoverList_false_of_forall
      (n := n) (colored := colored) (x := x) hall)

/--
The general leaf-count bound for `DecisionTree.ofRectCover` specialises to the
tree extracted from a `CoverRes`.
-/
lemma CoverRes.leaf_count_le {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) :
    DecisionTree.leaf_count
        (CoverRes.toDecisionTree (n := n) (F := F) cover) ≤
      List.foldr
        (fun R acc => ((Subcube.toList (n := n) R.1).length.succ) * acc)
        1 cover.rects.attach.toList := by
  classical
  simpa [CoverRes.toDecisionTree] using
    (DecisionTree.leaf_count_ofRectCover_le
      (n := n) (default := false) (F := F)
      (Rset := cover.rects) (hmono := cover.mono))

/--
The depth of the tree obtained from a `CoverRes` is bounded by the sum of the
lengths of the assignment lists of its rectangles.  This is a direct
specialisation of `DecisionTree.depth_ofRectCover_le`.
-/
lemma CoverRes.depth_le {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) :
    DecisionTree.depth
        (CoverRes.toDecisionTree (n := n) (F := F) cover) ≤
      List.foldr
        (fun R acc => (Subcube.toList (n := n) R.1).length + acc)
        0 cover.rects.attach.toList := by
  classical
  simpa [CoverRes.toDecisionTree] using
    (DecisionTree.depth_ofRectCover_le
      (n := n) (default := false) (F := F)
      (Rset := cover.rects) (hmono := cover.mono))

/--
Summing the lengths of the assignment lists of a list of rectangles is bounded by
`n` times the length of that list.  This technical lemma underpins the global
depth estimate for decision trees extracted from a cover.
-/
private lemma fold_length_le {n : ℕ}
    {P : Subcube n → Prop} :
    ∀ l : List {R : Subcube n // P R},
      List.foldr
          (fun R acc => (Subcube.toList (n := n) R.1).length + acc)
          0 l ≤ n * l.length
  | [] => by simpa
  | r :: l =>
      -- Bound the contribution of the head and use the inductive hypothesis for
      -- the tail.
      have hR : (Subcube.toList (n := n) r.1).length ≤ n :=
        Subcube.toList_length_le (n := n) (R := r.1)
      have htail := fold_length_le l
      -- Combine the two estimates and rewrite into the desired form.
      have hsum :
          (Subcube.toList (n := n) r.1).length +
              List.foldr
                (fun R acc => (Subcube.toList (n := n) R.1).length + acc) 0 l
              ≤ n + n * l.length :=
        Nat.add_le_add hR htail
        have hmul : n * l.length + n = n * (l.length + 1) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.mul_comm,
                Nat.mul_left_comm, Nat.mul_assoc] using
            (Nat.mul_succ n l.length).symm
        -- Translate the RHS into the cardinality of `r :: l` and simplify.
        have hfinal : n + n * l.length = n * (r :: l).length := by
          -- Start from `hmul` and rewrite step by step.
          calc
            n + n * l.length
                = n * l.length + n := by
                    simpa [Nat.add_comm, Nat.add_left_comm]
            _ = n * (l.length + 1) := hmul
            _ = n * (r :: l).length := by simp
      -- Combine all inequalities with the rewriting of the target.
      have hgoal :
          (Subcube.toList (n := n) r.1).length +
              List.foldr
                (fun R acc => (Subcube.toList (n := n) R.1).length + acc) 0 l
              ≤ n * (r :: l).length := by
        simpa [hfinal] using hsum
      hgoal

/--
The depth of the decision tree extracted from a cover is at most `n` times the
number of rectangles in that cover.
-/
lemma CoverRes.depth_le_card_mul {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverRes (F := F) k) :
    DecisionTree.depth
        (CoverRes.toDecisionTree (n := n) (F := F) cover) ≤ n * k := by
  classical
  -- Start from the generic bound involving the sum of assignment lengths.
  have hdepth := CoverRes.depth_le (n := n) (F := F) (k := k) cover
  -- Estimate the sum by `n * cover.rects.card`.
  have hfold :=
    fold_length_le (n := n)
      (P := fun R : Subcube n => R ∈ cover.rects)
      (l := cover.rects.attach.toList)
  -- Translate the list length of attached rectangles into the set cardinality.
  have hlen : cover.rects.attach.toList.length = cover.rects.card := by
    classical
    simpa using Finset.length_attach cover.rects
  -- Combine all inequalities and replace `cover.rects.card` by the bound `k`.
  have hsum :
      List.foldr
          (fun R acc => (Subcube.toList (n := n) R.1).length + acc) 0
          cover.rects.attach.toList ≤ n * cover.rects.card := by
    simpa [hlen] using hfold
  have hbound := le_trans hdepth hsum
  exact le_trans hbound (Nat.mul_le_mul_left _ cover.card_le)

/--
If `k ≤ k'`, a cover bounded by `k` rectangles also yields a depth bound of
`n * k'` for the associated decision tree.  This lemma is a convenient corollary
of `CoverRes.depth_le_card_mul` allowing one to substitute a larger cardinality
estimate.
-/
lemma CoverRes.depth_le_of_card_le {n : ℕ} {F : Family n} {k k' : ℕ}
    (cover : CoverRes (F := F) k) (hk : k ≤ k') :
    DecisionTree.depth
        (CoverRes.toDecisionTree (n := n) (F := F) cover) ≤ n * k' := by
  -- The original bound is `n * k`; monotonicity of multiplication upgrades it
  -- to `n * k'` under the assumption `k ≤ k'`.
  have := CoverRes.depth_le_card_mul (n := n) (F := F) (k := k) cover
  exact le_trans this <| Nat.mul_le_mul_left _ hk

/--
Specialised depth bound using the global `coverConst`.  If a cover is known to
contain at most `2^{coverConst * s * log₂ (n+1)}` rectangles, then the depth of
the tree produced by `CoverRes.toDecisionTree` is bounded accordingly.
-/
lemma CoverRes.depth_le_coverConst {n s : ℕ} {F : Family n}
    (cover : CoverRes (F := F)
        (Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))) :
    DecisionTree.depth
        (CoverRes.toDecisionTree (n := n) (F := F) cover)
          ≤ n * Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  -- This is a direct specialisation of `CoverRes.depth_le_card_mul` with
  -- `k = 2^{coverConst * s * log₂ (n+1)}`.
  simpa using
      (CoverRes.depth_le_card_mul (n := n) (F := F)
      (k := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) cover)

/--
Extract the underlying rectangle set from a `CoverRes`, allowing the
cardinality bound to be relaxed from `k` to any `k' ≥ k`.  This will be
useful when plugging a concrete cover into the final existential statement
about low-sensitivity families.
-/
lemma CoverRes.as_cover {n : ℕ} {F : Family n} {k k' : ℕ}
    (cover : CoverRes (F := F) k) (hk : k ≤ k') :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ k' := by
  -- The rectangle set packaged in `cover` already satisfies the desired
  -- monochromaticity and coverage properties, so it witnesses the existential
  -- claim directly.
  refine ⟨cover.rects, cover.mono, cover.covers, ?_⟩
  exact le_trans cover.card_le hk

/--
Specialisation of `CoverRes.as_cover` using the global `coverConst` bound.  A
`CoverRes` whose cardinality is already bounded by `2^{coverConst * s * log₂
(n+1)}` immediately yields the corresponding cover statement.
-/
lemma CoverRes.as_cover_coverConst {n s : ℕ} {F : Family n}
    (cover : CoverRes (F := F)
        (Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  -- Here the desired bound coincides with the one stored in `cover`, so we can
  -- reuse `CoverRes.as_cover` with `k' = k`.
  simpa using
    (CoverRes.as_cover (n := n) (F := F)
      (k := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))
      (k' := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))
      cover le_rfl)

/--
Turn a pointwise cover into a decision tree for a specific function `f` in the
family.  Each rectangle of the cover is coloured using the witness that `f` is
constant on it, and the resulting tree searches through the rectangles in an
arbitrary order, returning `true` as soon as one matches the input.
-/
noncomputable def CoverResP.toDecisionTree_for
    {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F) :
    DecisionTree n :=
  -- Specialise `ofRectCover` to the singleton family `{f}`; this only requires
  -- a monochromaticity proof for `f` on each rectangle.
  DecisionTree.ofRectCover (n := n) false (F := ({f} : Family n)) cover.rects
    (by
      intro R hR
      -- Obtain the colour of `f` on `R`.
      rcases cover.monoPw f hf R hR with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      intro g hg x hx
      -- Any function in the singleton family must be `f` itself.
      have : g = f := by
        simpa [Finset.mem_singleton] using hg
      subst this
      -- `f` agrees with the colour `b` on every point of `R`.
      simpa using hb hx)

/--
Evaluating the decision tree obtained from a pointwise cover yields `true` on
every input where the designated function outputs `true`.
-/
lemma CoverResP.eval_true {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F)
    {x : Point n} (hx : f x = true) :
    DecisionTree.eval_tree
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) x = true := by
  classical
  -- Assemble the list of coloured rectangles used by `ofRectCover`.
  let colored := cover.rects.attach.toList.map
    (fun R => (Classical.choose (cover.monoPw f hf R.1 R.2), R.1))
  -- Prove that every rectangle containing `x` is coloured `true`.
  have hall : ∀ p ∈ colored, Subcube.mem p.2 x → p.1 = true := by
    intro p hp hxR
    -- Extract the source rectangle `R` from the mapped list.
    rcases List.mem_map.1 hp with ⟨r, hr, hpair⟩
    rcases r with ⟨R, hR⟩
    -- Identify the colour of the rectangle.
    have hb : Classical.choose (cover.monoPw f hf R hR) = p.1 := by
      simpa [Prod.ext_iff] using congrArg Prod.fst hpair
    have hRe : R = p.2 := by
      simpa [Prod.ext_iff] using congrArg Prod.snd hpair
    -- On rectangle `R` the function `f` agrees with the chosen colour.
    have hmono := cover.monoPw f hf R hR
    have hxR' : Subcube.mem R x := by simpa [hRe] using hxR
    have hbval := (Classical.choose_spec hmono) hxR'
    subst hRe
    have hbtrue : Classical.choose hmono = true := by
      simpa [hbval] using hx
    simpa [hb] using hbtrue
  -- There exists at least one rectangle containing `x` thanks to `covers`.
  obtain ⟨R0, hR0, hxR0⟩ := cover.covers f hf x hx
  let p0 : Bool × Subcube n := (Classical.choose (cover.monoPw f hf R0 hR0), R0)
  have hp0_mem : p0 ∈ colored := by
    have hattach' :
        (⟨R0, hR0⟩ : {R : Subcube n // R ∈ cover.rects}) ∈ cover.rects.attach := by
      simpa using (Finset.mem_attach (s := cover.rects) hR0)
    have hattach :
        (⟨R0, hR0⟩ : {R : Subcube n // R ∈ cover.rects}) ∈
            cover.rects.attach.toList := by
      simpa using (List.mem_toList.mpr hattach')
    exact List.mem_map.2 ⟨⟨R0, hR0⟩, hattach, rfl⟩
  have hex : ∃ p ∈ colored, Subcube.mem p.2 x := ⟨p0, hp0_mem, hxR0⟩
  -- Apply the generic list-based evaluation lemma.
  simpa [CoverResP.toDecisionTree_for, DecisionTree.ofRectCover, colored]
    using (DecisionTree.eval_ofRectCoverList_true_of_mem (n := n)
      (default := false) (colored := colored) (x := x) hex hall)

/--
Evaluating the decision tree extracted from a pointwise cover yields `false` on
any input where the chosen function evaluates to `false`.  This complements
`CoverResP.eval_true` and follows from the fact that every rectangle containing
such an input is coloured `false`.
-/
lemma CoverResP.eval_false {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F)
    {x : Point n} (hx : f x = false) :
    DecisionTree.eval_tree
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) x = false := by
  classical
  -- Assemble the coloured rectangles as in the `eval_true` case.
  let colored := cover.rects.attach.toList.map
    (fun R => (Classical.choose (cover.monoPw f hf R.1 R.2), R.1))
  -- Show that every rectangle containing `x` is coloured `false`.
  have hall : ∀ p ∈ colored, Subcube.mem p.2 x → p.1 = false := by
    intro p hp hxR
    rcases List.mem_map.1 hp with ⟨r, hr, hpair⟩
    rcases r with ⟨R, hR⟩
    have hb : Classical.choose (cover.monoPw f hf R hR) = p.1 := by
      simpa [Prod.ext_iff] using congrArg Prod.fst hpair
    have hRe : R = p.2 := by
      simpa [Prod.ext_iff] using congrArg Prod.snd hpair
    have hmono := cover.monoPw f hf R hR
    have hxR' : Subcube.mem R x := by simpa [hRe] using hxR
    have hbval := (Classical.choose_spec hmono) hxR'
    subst hRe
    have hbfalse : Classical.choose hmono = false := by
      simpa [hbval] using hx
    simpa [hb] using hbfalse
  -- Invoke the list-based evaluation lemma specialised to `false` colours.
  simpa [CoverResP.toDecisionTree_for, DecisionTree.ofRectCover, colored]
    using (DecisionTree.eval_ofRectCoverList_false_of_forall
      (n := n) (colored := colored) (x := x) hall)

/--
Combine the specialised evaluation lemmas to show that the decision tree
extracted from a pointwise cover computes the designated function exactly on
every input.
-/
lemma CoverResP.eval {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F)
    {x : Point n} :
    DecisionTree.eval_tree
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) x = f x := by
  classical
  -- Branch on the value of `f x` and invoke the corresponding lemma.
  by_cases hx : f x = true
  · -- When `f x = true`, the tree evaluates to `true` as well.
    simpa [hx] using
      (CoverResP.eval_true (n := n) (F := F) (k := k)
        (cover := cover) (f := f) hf (x := x) hx)
  · -- Otherwise `f x` must be `false`.
    have hxfalse : f x = false := by
      -- The Boolean value `f x` can only be `true` or `false`; the former
      -- contradicts `hx`.
      cases hx' : f x with
      | false => simpa [hx']
      | true  => exact (False.elim (hx hx'))
    simpa [hxfalse] using
      (CoverResP.eval_false (n := n) (F := F) (k := k)
        (cover := cover) (f := f) hf (x := x) hxfalse)

/--
The general leaf-count bound for `DecisionTree.ofRectCover` specialises to the
tree extracted from a pointwise cover.
-/
lemma CoverResP.leaf_count_le {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F) :
    DecisionTree.leaf_count
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) ≤
      List.foldr
        (fun R acc => ((Subcube.toList (n := n) R.1).length.succ) * acc)
        1 cover.rects.attach.toList := by
  classical
  simpa [CoverResP.toDecisionTree_for]
    using (DecisionTree.leaf_count_ofRectCover_le (n := n) (default := false)
      (F := ({f} : Family n)) (Rset := cover.rects)
      (hmono := by
        intro R hR
        rcases cover.monoPw f hf R hR with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        intro g hg x hx
        have : g = f := by simpa [Finset.mem_singleton] using hg
        subst this
        simpa using hb hx))

/--
The depth of the tree obtained from a pointwise cover is bounded by the sum of
the lengths of the assignment lists of its rectangles.
-/
lemma CoverResP.depth_le {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F) :
    DecisionTree.depth
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) ≤
      List.foldr
        (fun R acc => (Subcube.toList (n := n) R.1).length + acc)
        0 cover.rects.attach.toList := by
  classical
  simpa [CoverResP.toDecisionTree_for]
    using (DecisionTree.depth_ofRectCover_le (n := n) (default := false)
      (F := ({f} : Family n)) (Rset := cover.rects)
      (hmono := by
        intro R hR
        rcases cover.monoPw f hf R hR with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        intro g hg x hx
        have : g = f := by simpa [Finset.mem_singleton] using hg
        subst this
        simpa using hb hx))

/--
The depth of the decision tree extracted from a pointwise cover is at most `n`
times the number of rectangles in that cover.
-/
lemma CoverResP.depth_le_card_mul {n : ℕ} {F : Family n} {k : ℕ}
    (cover : CoverResP (F := F) k) {f : BFunc n} (hf : f ∈ F) :
    DecisionTree.depth
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) ≤ n * k := by
  classical
  -- Start from the generic bound involving the sum of assignment lengths.
  have hdepth :=
    CoverResP.depth_le (n := n) (F := F) (k := k) (cover := cover)
      (f := f) hf
  -- Estimate the sum by `n * cover.rects.card`.
  have hfold :
      List.foldr
          (fun R acc => (Subcube.toList (n := n) R.1).length + acc) 0
          cover.rects.attach.toList ≤ n * cover.rects.card := by
    have :=
      fold_length_le (n := n)
        (P := fun R : Subcube n => R ∈ cover.rects)
        (l := cover.rects.attach.toList)
    -- Translate the list length of attached rectangles into the set cardinality.
    have hlen : cover.rects.attach.toList.length = cover.rects.card := by
      simpa using Finset.length_attach cover.rects
    simpa [hlen] using this
  -- Combine the inequalities and replace `cover.rects.card` by the bound `k`.
  have hbound := le_trans hdepth hfold
  exact le_trans hbound (Nat.mul_le_mul_left _ cover.card_le)

/--
If `k ≤ k'`, a pointwise cover bounded by `k` rectangles also yields a depth
bound of `n * k'` for the associated decision tree.  This lemma mirrors
`CoverRes.depth_le_of_card_le`.
-/
lemma CoverResP.depth_le_of_card_le {n : ℕ} {F : Family n} {k k' : ℕ}
    (cover : CoverResP (F := F) k) (hk : k ≤ k') {f : BFunc n}
    (hf : f ∈ F) :
    DecisionTree.depth
        (CoverResP.toDecisionTree_for (n := n) (F := F) (k := k)
          cover (f := f) hf) ≤ n * k' := by
  have := CoverResP.depth_le_card_mul (n := n) (F := F) (k := k)
    (cover := cover) (f := f) hf
  exact le_trans this <| Nat.mul_le_mul_left _ hk

/--
Specialised depth bound using the global `coverConst`.  If a pointwise cover is
known to contain at most `2^{coverConst * s * log₂ (n+1)}` rectangles, then the
depth of its associated decision tree is bounded accordingly.
-/
lemma CoverResP.depth_le_coverConst {n s : ℕ} {F : Family n}
    (cover : CoverResP (F := F)
        (Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))) {f : BFunc n}
    (hf : f ∈ F) :
    DecisionTree.depth
        (CoverResP.toDecisionTree_for (n := n) (F := F)
          (k := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))
          cover (f := f) hf) ≤
      n * Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  -- This is a direct specialisation of `CoverResP.depth_le_card_mul` with
  -- `k = 2^{coverConst * s * log₂ (n+1)}`.
  simpa using (CoverResP.depth_le_card_mul (n := n) (F := F)
    (k := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)))
    (cover := cover) (f := f) hf)

/--
Expose a pointwise cover as the existential statement used by
`decisionTree_cover`.  Given a cover with at most `k` rectangles, any larger
bound `k'` also suffices for the final inequality.
-/
lemma decisionTree_cover_of_coverResP {n s k : Nat} {F : Family n}
    [Fintype (Point n)]
    (cover : CoverResP (F := F) k)
    (hk : k ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  -- Reveal the rectangle set and relax the cardinality bound via `CoverResP.as_cover`.
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    CoverResP.as_cover (n := n) (F := F) (k := k)
      (k' := Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) cover hk
  exact ⟨Rset, hmono, hcov, hcard⟩

/--
Variant of `decisionTree_cover_of_coverResP` that accepts a cover with
family-level monochromaticity.  Such a cover is first reinterpreted as a
pointwise cover via `CoverRes.toCoverResP` and then exposed as an existential
cover satisfying the required cardinality bound.
-/
lemma decisionTree_cover_of_coverRes {n s k : Nat} {F : Family n}
    [Fintype (Point n)]
    (cover : CoverRes (F := F) k)
    (hk : k ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Convert to the pointwise structure and invoke the previous lemma.
  have coverP : CoverResP (F := F) k := CoverRes.toCoverResP (F := F) (k := k) cover
  exact
    decisionTree_cover_of_coverResP (n := n) (s := s) (F := F)
      (cover := coverP) (hk := hk)

/-/
Expose the cover produced by `cover_exists_mBound` in the `decisionTree_cover`
format.  The number of rectangles is bounded explicitly by
`Cover2.mBound n (n + 1)`.
-/
lemma decisionTree_cover_mBound {n : Nat} (F : Family n) [Fintype (Point n)]
    (hn : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Cover2.mBound n (n + 1) := by
  classical
  -- Instantiate `cover_exists_mBound` with `h = n` to match the requested bound.
  simpa using
    (cover_exists_mBound (n := n) (F := F) (h := n)
      (hn := hn) (hcard := le_rfl))

/--
Use the recursive constructor `buildCoverLex3` to obtain a pointwise cover and
immediately expose it through `decisionTree_cover_of_coverResP`.  The numeric
bound `hk` translates the cardinality guarantee `mBound` into the final bound
required by `decisionTree_cover`.
-/
lemma decisionTree_cover_of_buildCover {n s h : Nat} (F : Family n)
    [Fintype (Point n)] (hn : 0 < n) (hcard : n ≤ h)
    (hk : Cover2.mBound n (h + 1)
      ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Construct the structured cover via `buildCoverLex3` and expose it.
  let cover := buildCoverLex3 (F := F) (h := h) hn hcard
  exact
    decisionTree_cover_of_coverResP (n := n) (s := s) (F := F)
      (cover := cover) (hk := hk)

/--
A convenience variant of `decisionTree_cover_of_buildCover` that fixes the
budget to `h = n`.  This automatically satisfies the technical requirement
`n ≤ h` needed by the recursive constructor.
-/
lemma decisionTree_cover_of_buildCover_choose_h_pos {n s : Nat} (F : Family n)
    [Fintype (Point n)] (hn : 0 < n)
    (hk : Cover2.mBound n (n + 1)
      ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Instantiate `h` with `n` in the general lemma.
  simpa using
    (decisionTree_cover_of_buildCover (n := n) (s := s) (F := F)
      (h := n) (hn := hn) (hcard := le_rfl) (hk := hk))
/-- Trivial base case: if all functions in the family are constant on the full
cube, we can cover all ones with just that cube.  This lemma acts as a base case
for the eventual recursive construction of `decisionTree_cover`. -/
lemma decisionTree_cover_of_constant
  {n : Nat} (F : Family n) (s : Nat) [Fintype (Point n)]
  (hconst : ∃ b, ∀ f ∈ F, ∀ x, f x = b) :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Package the full-cube cover and discharge the cardinality constraint.
  rcases hconst with ⟨b, hb⟩
  let cover := CoverResP.const (F := F) (b := b) hb
  have hpow : 1 ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
    have hpos : 0 < Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
      pow_pos (by decide) _
    exact Nat.succ_le_of_lt hpos
  -- Invoke the generic wrapper to obtain the final existential cover.
  exact decisionTree_cover_of_coverResP (n := n) (s := s)
    (F := F) (cover := cover) hpow

/--
Base case handling families where every function is individually constant,
possibly with different outputs.  A single full‑cube rectangle covers all
`true` inputs and is monochromatic for every function.
-/
lemma decisionTree_cover_of_constFamily
  {n : Nat} (F : Family n) (s : Nat) [Fintype (Point n)]
  (hconst : ∀ f ∈ F, ∀ x y, f x = f y) :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Build the singleton cover and lift it through the generic wrapper.
  let cover := CoverResP.constFamily (F := F) hconst
  have hpow : 1 ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
    have hpos : 0 < Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
      pow_pos (by decide) _
    exact Nat.succ_le_of_lt hpos
  exact
    decisionTree_cover_of_coverResP (n := n) (s := s) (F := F)
      (cover := cover) (hk := hpow)

/--
  Degenerate base case: the empty family has no `1`-inputs to cover.
  Returning the empty set of rectangles trivially satisfies the
  monochromaticity and coverage requirements.
-/
lemma decisionTree_cover_empty
  {n s : Nat} [Fintype (Point n)] :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ (∅ : Family n), ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ (∅ : Family n), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Use the universal empty cover and apply the wrapper.
  let cover := CoverResP.empty (n := n)
  have hpow : 0 ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
    Nat.zero_le _
  exact decisionTree_cover_of_coverResP (n := n) (s := s)
    (F := (∅ : Family n)) (cover := cover) hpow

/--
A wrapper around `decisionTree_cover_of_buildCover` that selects the budget
`h = n` and also handles the degenerate case `n = 0` by reducing to
`decisionTree_cover_of_constFamily`.  This removes the technical assumption
`0 < n` required by `buildCoverLex3`.
-/
lemma decisionTree_cover_of_buildCover_choose_h {n s : Nat} (F : Family n)
    [Fintype (Point n)]
    (hk : Cover2.mBound n (n + 1)
      ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  by_cases hzero : n = 0
  · -- With no variables all functions are constant; use the dedicated lemma.
    subst hzero
    -- Any two points of the empty cube are equal.
    have hconst : ∀ f ∈ F, ∀ x y, f x = f y := by
      intro f hf x y
      have : x = y := Subsingleton.elim _ _
      simpa [this]
    -- Apply the constant-family cover.
    simpa using
      (decisionTree_cover_of_constFamily (n := 0) (F := F) (s := s) hconst)
  · -- Positive dimension: fall back to the specialised wrapper.
    have hn : 0 < n := Nat.pos_of_ne_zero hzero
    simpa [hzero] using
      (decisionTree_cover_of_buildCover_choose_h_pos
        (n := n) (s := s) (F := F) (hn := hn) (hk := hk))

  /-!
    This theorem encapsulates the desired conclusion of the decision-tree
    construction.  It handles the trivial cases—empty families and families of
    pointwise constant functions—directly via previously established lemmas,
    and treats the remaining nontrivial case via the recursive cover
    construction provided by `decisionTree_cover_of_buildCover_choose_h`.
  -/
theorem decisionTree_cover
  {n : Nat} (F : Family n) (s : Nat) [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Handle the trivial cases up front.
  by_cases hF : F = (∅ : Family n)
  · subst hF
    -- The empty family admits the empty cover.
    simpa using (decisionTree_cover_empty (n := n) (s := s))
  -- If every function is constant, a single full cube suffices.
  by_cases hconst : ∀ f ∈ F, ∀ x y, f x = f y
  · exact decisionTree_cover_of_constFamily (n := n) (F := F) (s := s) hconst
  -- Nontrivial family: extract the required bounds and invoke the recursive
  -- construction.
  -- The ambient dimension must be positive; otherwise every function would be
  -- constant, contradicting `hconst`.
  have hn : 0 < n := by
    by_contra hnzero
    have hzero : n = 0 := Nat.le_zero.mp (Nat.not_lt.mp hnzero)
    subst hzero
    have hconst' : ∀ f ∈ F, ∀ x y, f x = f y := by
      intro f hf x y
      have hx : x = y := Subsingleton.elim _ _
      simpa [hx]
    exact hconst hconst'
  -- Choose a function in the family that is not constant.
  classical
  obtain ⟨f₀, hf₀F, hnonconst⟩ : ∃ f ∈ F, ¬ ∀ x y, f x = f y := by
    classical
    have := Classical.not_forall.mp hconst
    rcases this with ⟨f, hf⟩
    have hf' := Classical.not_imp.mp hf
    exact ⟨f, hf'.1, hf'.2⟩
  -- Its sensitivity is positive, hence `s` is also positive.
  have hsens_pos : 0 < sensitivity f₀ := by
    by_contra hzero
    have hsens_zero : sensitivity f₀ = 0 := by
      have hle : sensitivity f₀ ≤ 0 := Nat.not_lt.mp hzero
      exact Nat.le_antisymm hle (Nat.zero_le _)
    have hsupp :=
      support_eq_empty_of_sensitivity_zero (f := f₀) hsens_zero
    have hconstf : ∀ x y, f₀ x = f₀ y := by
      intro x y
      have hagree : ∀ i ∈ support f₀, x i = y i := by
        intro i hi
        have : i ∈ (∅ : Finset (Fin n)) := by simpa [hsupp] using hi
        cases this
      simpa using
        eval_eq_of_agree_on_support (f := f₀) (x := x) (y := y) hagree
    exact hnonconst hconstf
  have hs : 0 < s :=
    lt_of_lt_of_le hsens_pos (Hsens f₀ hf₀F)
  -- Apply the combinatorial cover construction.  For large `s` we can bound
  -- the rectangle count via `mBound_le_pow_of_budget_choice_bigS`.  The case
  -- `s ≤ n + 1` remains open and requires a refined recursive analysis.
  by_cases hbig : n + 2 ≤ s
  ·
    have hk :=
      mBound_le_pow_of_budget_choice_bigS (n := n) (s := s)
        (hn := Nat.succ_le_of_lt hn) (hs := hbig)
    exact
      decisionTree_cover_of_buildCover_choose_h (n := n) (s := s) (F := F)
        (hk := hk)
  ·
    -- TODO: implement the small‑`s` case using a refined decision tree
    -- argument that avoids `mBound`.
    admit

-- Auxiliary structure bundling all invariants required during the recursive
-- construction of the cover.  For a pair `(F, A)` it stores the sensitivity
-- bound for every function in `F`, the entropy bound for `F`, and the fact that
-- functions are insensitive outside the coordinate set `A`.

/-- **Low-sensitivity cover** (statement only).  If every function in the
    family has sensitivity at most `s`, then there exists a small set of
    subcubes covering all ones of the family.  The proof will use decision
    trees or the Gopalan--Moshkovitz--Oliveira bound.  Here we only record the
    statement. -/
lemma low_sensitivity_cover (F : Family n) (s : ℕ)
    [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ F, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using decisionTree_cover (F := F) (s := s) Hsens

/-/ Variant of `low_sensitivity_cover` for a single Boolean function.
    This skeleton assumes a suitable decision tree for `f` of depth
    `O(s * log n)`.  All remaining steps are placeholders. -/

lemma low_sensitivity_cover_single
  (n s : ℕ) (f : BoolFunc.BFunc n)
    [Fintype (BoolFunc.Point n)]
    (Hsens : BoolFunc.sensitivity f ≤ s) :
  ∃ Rset : Finset (BoolFunc.Subcube n),
    (∀ R ∈ Rset, BoolFunc.Subcube.monochromaticFor R f) ∧
    (∀ x : BoolFunc.Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Treat `{f}` as a family and apply `decisionTree_cover`.
  have hfamily : ∀ g ∈ ({f} : Family n), sensitivity g ≤ s := by
    intro g hg
    have hg' : g = f := by simpa [Finset.mem_singleton] using hg
    simpa [hg'] using Hsens
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    decisionTree_cover (F := ({f} : Family n)) (s := s) hfamily
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro R hR
    simpa using hmono f (by simp) R hR
  · intro x hx
    simpa using hcov f (by simp) x hx



/-- Specialized version of `low_sensitivity_cover` for the empty family.
    This is a small convenience wrapper around `decisionTree_cover_empty`. -/
lemma low_sensitivity_cover_empty (n s : ℕ)
    [Fintype (Point n)] :
  ∃ Rset : Finset (Subcube n),
    (∀ f ∈ (∅ : Family n), ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ f ∈ (∅ : Family n), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using
    (decisionTree_cover_empty (n := n) (s := s))

end BoolFunc
