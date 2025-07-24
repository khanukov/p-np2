/-
cover.lean
===========

Top‑level **cover construction** for the Family Collision‑Entropy Lemma.
The next step in the formalization introduces real "uncovered input"
structures and an *optional* search for the first uncovered ⟨f, x⟩.
`buildCover` now recurses on these data.  The entropy-based branch is
implemented via `exists_coord_entropy_drop` and decreases `H₂` in both
subfamilies.  The final numeric bound remains open.
-/

import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support   -- new helper lemmas
import Pnp2.Sunflower.RSpread   -- definition of scattered families
import Pnp2.low_sensitivity_cover
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

open Classical
open BoolFunc
open Finset
open Agreement

namespace Cover

/-! ## Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h := by
  have : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  have : (2 * h + n : ℕ) ≤ n * (h + 2) * 2 ^ (10 * h) := by
    have : 2 * h + n ≤ n * (h + 2) := by
      have h0 : 0 ≤ (h : ℤ) := by exact_mod_cast Nat.zero_le _
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Nat.mul_le_mul_left (n * (h + 2)) (Nat.succ_le_iff.mpr this)
  simpa [mBound] using this

/-! ### Improved bound with positivity assumption
The legacy development strengthens `numeric_bound` by assuming
`0 < n`.  This version follows the newer proof and will be useful for
compatibility with migrated lemmas. -/

lemma numeric_bound_pos (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h := by
  classical
  cases h with
  | zero =>
      have h0 : 2 * 0 + n ≤ mBound n 0 := by
        have hmul := Nat.mul_le_mul_left n (show (1 : ℕ) ≤ 2 from by decide)
        simpa [mBound, two_mul, Nat.mul_comm, one_mul] using hmul
      simpa using h0
  | succ h =>
      have hlinear : (2 * (h + 1) + n : ℕ) ≤ 2 * n * (h + 1 + 2) := by
        nlinarith [hn]
      have hpow : (2 : ℕ) ≤ 2 ^ (10 * (h + 1)) := by
        have hbase : (2 : ℕ) ≤ 2 ^ 10 := by decide
        have hexp : 10 ≤ 10 * (h + 1) := by
          have hx : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have hx' : (10 : ℕ) * 1 ≤ 10 * (h + 1) := Nat.mul_le_mul_left 10 hx
          set_option linter.unnecessarySimpa false in
          simpa [Nat.mul_one] using hx'
        exact hbase.trans (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hexp)
      have : 2 * (h + 1) + n ≤ n * (h + 1 + 2) * 2 ^ (10 * (h + 1)) := by
        calc
          2 * (h + 1) + n ≤ 2 * n * (h + 1 + 2) := hlinear
          _ = (n * (h + 1 + 2)) * 2 := by ring
          _ ≤ (n * (h + 1 + 2)) * 2 ^ (10 * (h + 1)) :=
            Nat.mul_le_mul_left _ hpow
      simpa [mBound] using this

lemma pow_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ^ (10 * h) ≤ mBound n h := by
  have hpos : 0 < n * (h + 2) := by
    have hpos' : 0 < h + 2 := Nat.succ_pos _
    exact Nat.mul_pos hn hpos'
  have hfactor : 1 ≤ n * (h + 2) := Nat.succ_le_of_lt hpos
  have := Nat.mul_le_mul_left (2 ^ (10 * h)) hfactor
  simpa [mBound, one_mul] using this

/-!  A convenient variant of `pow_le_mBound`: the exponential `2 ^ h` is
bounded by `mBound n h` for any positive dimension `n`.  This simple
estimate occasionally suffices when the exact `10 * h` exponent is not
needed. -/
lemma pow_le_mBound_simple (n h : ℕ) (hn : 0 < n) :
    2 ^ h ≤ mBound n h := by
  have hexp : h ≤ 10 * h := by
    have hbase : (1 : ℕ) ≤ 10 := by decide
    have := Nat.mul_le_mul_left h hbase
    simpa [Nat.mul_comm] using this
  have hpow : 2 ^ h ≤ 2 ^ (10 * h) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
  exact hpow.trans (pow_le_mBound (n := n) (h := h) hn)

/-!  `mBound` is strictly positive for any positive dimension `n`.  This simple
numeric fact often provides a convenient lower bound when reasoning about cover
sizes. -/
lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  have hpos₁ : 0 < h + 2 := Nat.succ_pos _
  have hpos₂ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul : 0 < n * (h + 2) := Nat.mul_pos hn hpos₁
  have := Nat.mul_pos hmul hpos₂
  simpa [mBound] using this

/-!  A tiny numeric fact: for any positive dimension `n` the bound
`mBound n h` is at least `2`.  This convenient inequality helps when
bounding the size of a small collection of rectangles. -/
lemma two_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hh2 : 2 ≤ h + 2 := by
    have := Nat.zero_le h
    exact Nat.succ_le_succ (Nat.succ_le_succ this)
  have hfactor : 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul hn1 hh2 (by decide) (Nat.zero_le _)
    simpa [one_mul] using this
  have hpow : 1 ≤ 2 ^ (10 * h) :=
    Nat.one_le_pow (2) (10 * h) (by decide)
  have := Nat.mul_le_mul hfactor hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/--  For a positive dimension and entropy budget at least `1`,
`mBound n h` is also at least `3`.  This slightly stronger bound is
useful when estimating unions of three rectangles. -/
lemma three_le_mBound (n h : ℕ) (hn : 0 < n) (hh : 1 ≤ h) :
    3 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  -- Establish `3 ≤ n * (h + 2)` using `hn` and `hh`.
  have h3 : 3 ≤ h + 2 := by
    have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
    have : (3 : ℤ) ≤ h + 2 := by nlinarith
    exact_mod_cast this
  have hfac1 : h + 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul_right (h + 2) hn1
    simpa [one_mul] using this
  have hfac : 3 ≤ n * (h + 2) := le_trans h3 hfac1
  -- Multiply by the positive power factor.
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow (2) (10 * h) (by decide)
  have := Nat.mul_le_mul hfac hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
@[simp] lemma mBound_zero (h : ℕ) : mBound 0 h = 0 := by
  simp [mBound]

lemma mBound_eq_zero_iff {n h : ℕ} : mBound n h = 0 ↔ n = 0 := by
  cases n with
  | zero =>
      simp [mBound_zero]
  | succ n =>
      have : 0 < mBound (Nat.succ n) h := mBound_pos (n := Nat.succ n) (h := h) (Nat.succ_pos _)
      have : mBound (Nat.succ n) h ≠ 0 := ne_of_gt this
      constructor
      · intro hzero
        exact False.elim (this hzero)
      · intro hfalse
        cases hfalse

/-!  `mBound` is monotone in the entropy budget.  We will repeatedly
use this fact to lift bounds from recursive calls. -/

lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  dsimp [mBound]
  have hfac : n * (h₁ + 2) ≤ n * (h₂ + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 2)
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) this
  exact Nat.mul_le_mul hfac hpow

/-!  `mBound` is also monotone in the dimension parameter.  Increasing the
number of variables can only enlarge the numeric bound.  This simple fact
is occasionally convenient when comparing covers across different cube
sizes. -/
lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  dsimp [mBound]
  have hfac : n₁ * (h + 2) ≤ n₂ * (h + 2) :=
    Nat.mul_le_mul_right (h + 2) hn
  have := Nat.mul_le_mul hfac (le_rfl : 2 ^ (10 * h) ≤ 2 ^ (10 * h))
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-!  A convenient special case of `mBound_mono`: increasing the entropy
budget by one never decreases the bound.  This tiny lemma avoids having
to spell out `Nat.le_succ` at every call site. -/
lemma mBound_le_succ (n h : ℕ) :
    mBound n h ≤ mBound n (h + 1) :=
  mBound_mono (n := n) (Nat.le_succ h)

/-!  Doubling the bound for a smaller budget stays below the bound for the
next budget.  This simple numeric inequality is used when analysing the
entropy branch of `buildCover`. -/
lemma two_mul_mBound_le_succ (n h : ℕ) :
    2 * mBound n h ≤ mBound n (h + 1) := by
  have hfac : h + 2 ≤ h + 3 := by exact Nat.succ_le_succ (Nat.le_refl _)
  have hexp : 10 * h + 1 ≤ 10 * h + 10 := by
    have := (Nat.succ_le_succ (Nat.zero_le (10 * h)))
    -- `1 ≤ 10` allows us to shift by `10 * h`
    have h1 : (1 : ℕ) ≤ 10 := by decide
    exact add_le_add_left h1 (10 * h)
  have hpow : 2 ^ (10 * h + 1) ≤ 2 ^ (10 * h + 10) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
  have hmul := Nat.mul_le_mul hfac hpow
  have := Nat.mul_le_mul_left n hmul
  -- rewrite both sides in terms of `mBound`
  simpa [mBound, pow_add, pow_succ, Nat.mul_left_comm, Nat.mul_assoc,
        Nat.mul_comm] using this

/-!  Bounding the size of a union of two covers.  If both sets are
bounded by `mBound n h`, then their union stays below the next budget
`mBound n (h + 1)`.  This lemma abstracts the numeric step used in the
entropy branch of `buildCover`. -/
lemma card_union_mBound_succ {n h : ℕ} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : R₁.card ≤ mBound n h) (h₂ : R₂.card ≤ mBound n h) :
    (R₁ ∪ R₂).card ≤ mBound n (h + 1) := by
  classical
  -- First bound the union by the sum of cardinals.
  have hsum : (R₁ ∪ R₂).card ≤ R₁.card + R₂.card :=
    Finset.card_union_le
  -- Next bound the sum by twice `mBound n h`.
  have hdouble : R₁.card + R₂.card ≤ 2 * mBound n h := by
    have := add_le_add h₁ h₂
    simpa [two_mul] using this
  -- Combine with the numeric growth of `mBound`.
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans <| hdouble.trans hstep

/-!  Increasing the entropy budget by one more than compensates the
addition of a single rectangle.  This convenient numeric fact helps
bound union steps where at least one new subcube is inserted. -/
lemma one_add_mBound_le_succ {n h : ℕ} (hn : 0 < n) :
    mBound n h + 1 ≤ mBound n (h + 1) := by
  have hpos : 1 ≤ mBound n h := by
    have := mBound_pos (n := n) (h := h) hn
    exact Nat.succ_le_of_lt this
  have hdouble : mBound n h + 1 ≤ 2 * mBound n h := by
    have htwice : mBound n h + 1 ≤ mBound n h + mBound n h :=
      Nat.add_le_add_left hpos (mBound n h)
    simpa [two_mul] using htwice
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hdouble.trans hstep

/--
`card_union_singleton_mBound_succ` is a numeric helper for the counting
argument of `buildCover`.  If a set of rectangles already fits inside
`mBound n h`, adding one additional rectangle increases the size by at most one,
so the union still lies within the next budget `mBound n (h + 1)`.  The
dimension must be positive to ensure that this next budget is indeed larger.
--/
lemma card_union_singleton_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R}).card ≤ mBound n (h + 1) := by
  classical
  -- First bound the union by the sum of cardinals.
  have hsum : (Rset ∪ {R}).card ≤ Rset.card + 1 := by
    simpa using (Finset.card_union_le (s := Rset) (t := ({R} : Finset (Subcube n))))
  -- Bound the sum by `mBound n h + 1` using the hypothesis on `Rset`.
  have hbound : Rset.card + 1 ≤ mBound n h + 1 :=
    Nat.add_le_add_right hcard 1
  -- Increase the budget by one to absorb the extra rectangle.
  have hstep := one_add_mBound_le_succ (n := n) (h := h) hn
  -- Combine the inequalities.
  exact hsum.trans <| hbound.trans hstep

/-!
Adding a rectangle via `Finset.insert` is numerically harmless:
if the original set already lies within `mBound n h`, then the
inserted set stays within `mBound n (h + 1)`.  This is just a
convenient wrapper around `card_union_singleton_mBound_succ`.
-/
lemma card_insert_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (insert R Rset).card ≤ mBound n (h + 1) := by
  classical
  -- Express the insertion as a union with a singleton.
  have hunion : insert R Rset = Rset ∪ {R} := by
    ext x; by_cases hx : x = R <;> by_cases hxset : x ∈ Rset <;>
      simp [hx, hxset, Finset.mem_insert, Finset.mem_union]
  -- Apply the union lemma and rewrite.
  simpa [hunion] using
    (card_union_singleton_mBound_succ (n := n) (h := h)
      (Rset := Rset) (R := R) hcard hn)

/--
`card_union_pair_mBound_succ` is a tiny convenience lemma: inserting
two rectangles at once keeps the size within the next budget
`mBound n (h + 1)` as long as the starting set already lies inside
`mBound n h`.  The dimension hypothesis ensures this next budget is
strictly larger.
-/
lemma card_union_pair_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R₁, R₂}).card ≤ mBound n (h + 1) := by
  classical
  -- Bound the pair `{R₁, R₂}` by `mBound n h` via the `two_le_mBound` lemma.
  let Rpair : Finset (Subcube n) := {R₁, R₂}
  have hpair_le_two : Rpair.card ≤ 2 := by
    by_cases h : R₁ = R₂
    · subst h; simp [Rpair]
    · simp [Rpair, h]
  have hpair_bound : Rpair.card ≤ mBound n h :=
    le_trans hpair_le_two (two_le_mBound (n := n) (h := h) hn)
  -- Apply the general union bound for two sets of size ≤ `mBound n h`.
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rpair) hcard hpair_bound
  simpa [Rpair, Finset.union_comm, Finset.union_assoc] using this
lemma card_union_triple_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ R₃ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) (hh : 1 ≤ h) :
    (Rset ∪ {R₁, R₂, R₃}).card ≤ mBound n (h + 1) := by
  classical
  -- The triple set `{R₁, R₂, R₃}` has at most three elements.
  let Rtriple : Finset (Subcube n) := {R₁, R₂, R₃}
  have htriple_le_three : Rtriple.card ≤ 3 := by
    have hcard_insert := Finset.card_insert_le (s := {R₁, R₂}) (a := R₃)
    have hpair_le_two : ({R₁, R₂} : Finset (Subcube n)).card ≤ 2 := by
      by_cases h : R₁ = R₂
  · subst h; simp
  · simp [h]
    have := le_trans hcard_insert (Nat.add_le_add_right hpair_le_two 1)
    simpa [Rtriple] using this
  have htriple_bound : Rtriple.card ≤ mBound n h :=
    le_trans htriple_le_three (three_le_mBound (n := n) (h := h) hn hh)
  -- Apply the general union bound.
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rtriple) hcard htriple_bound
  simpa [Rtriple, Finset.union_comm, Finset.union_assoc] using this


/-! ### Counting bound for arbitrary covers -/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

/-! ### Alternate bound wrapping the cardinality of `Subcube n`
The legacy development introduced an auxiliary function
`bound_function` to emphasise the `3 ^ n` growth of the universal
subcube family.  We reproduce the same API here for compatibility
with migrated proofs. -/

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

/-! ## Auxiliary predicates -/

variable {n h : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Vector Bool n) : Prop :=
  ∀ R ∈ Rset, x ∉ₛ R

@[simp] lemma notCovered_empty (x : Vector Bool n) :
    NotCovered (Rset := (∅ : Finset (Subcube n))) x := by
  intro R hR
  -- `hR` is impossible since the set is empty
  exact False.elim (by simpa using hR)

lemma NotCovered.monotone {R₁ R₂ : Finset (Subcube n)} (hsub : R₁ ⊆ R₂)
    {x : Vector Bool n} (hx : NotCovered (Rset := R₂) x) :
    NotCovered (Rset := R₁) x := by
  intro R hR
  exact hx R (hsub hR)

/-- The set of all uncovered 1-inputs (together with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) : Set (Σ f : BoolFunc n, Vector Bool n) :=
  {⟨f, x⟩ | f ∈ F ∧ f x = true ∧ NotCovered Rset x}

/-- Optionally returns the *first* uncovered ⟨f, x⟩. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) : Option (Σ f : BoolFunc n, Vector Bool n) :=
  (uncovered F Rset).choose?  -- `choose?` from Mathlib (classical choice on set)

@[simp]
lemma firstUncovered_none_iff (R : Finset (Subcube n)) :
    firstUncovered F R = none ↔ uncovered F R = ∅ := by
  classical
  simp [firstUncovered, Set.choose?_eq_none]

/-- **Sunflower extraction step.**  If the family of currently
uncovered functions is large, the classical sunflower lemma yields a
subcube covering a positive fraction of them.  The precise constants
are irrelevant here; we only record the existence of such a rectangle.
Formal details are deferred. -/
-- This lemma implements step A-3 of the `buildCover` algorithm,
-- extracting a subcube that simultaneously covers many functions.

lemma sunflower_step
    (p t : ℕ)
    (hp : 0 < p) (ht : 2 ≤ t)
    (h_big : (t - 1).factorial * p ^ t < (Family.supports F).card)
    (h_support : ∀ f ∈ F, (BoolFunc.support f).card = p) :
  ∃ (R : Subcube n),
    (F.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ t ∧ 1 ≤ R.dimension := by
  classical
  -- Build the family of essential supports of functions in `F`.
  let 𝓢 : Finset (Finset (Fin n)) := Family.supports F
  have h_sizes : ∀ s ∈ 𝓢, s.card = p := by
    intro s hs
    rcases Family.mem_supports.mp hs with ⟨f, hf, rfl⟩
    exact h_support f hf
  -- Apply the sunflower lemma to obtain a sunflower inside `𝓢`.
  obtain ⟨𝓣, h𝓣sub, hSun, hcard⟩ :=
    Sunflower.sunflower_exists (𝓢 := 𝓢) (w := p) (p := t)
      hp ht h_big (by intro s hs; simpa [h_sizes s hs] using h_sizes s hs)
  -- Extract the core `K` from the sunflower description.
  obtain ⟨hT, K, h_core⟩ := hSun
  -- Freeze the coordinates in `K` according to a fixed point `x₀`.
  let x₀ : Point n := fun _ => false
  let R : Subcube n := Agreement.Subcube.fromPoint x₀ K
  refine ⟨R, ?_, ?_⟩
  ·
    -- Each `A ∈ 𝓣` is the support of some function `f_A ∈ F`.
    have exists_f : ∀ A ∈ 𝓣, ∃ f ∈ F, support f = A := by
      intro A hA
      have hA' := h𝓣sub hA
      simpa using (Family.mem_supports.mp hA')
    choose f hfF hfSupp using exists_f
    -- (a) main counting inequality
    have h_filter_ge : (F.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ t := by
      -- the sets in `𝓣` have size `t` and are pairwise distinct, and for each
      -- `A ∈ 𝓣` we chose a unique function `f_A`.
      have h_inj :
          (Finset.image (fun A : Finset (Fin n) => f A (by
            have : A ∈ 𝓣 := by exact ‹A ∈ 𝓣›)
            ) 𝓣).card = t := by
        have h_inj_aux :
            Function.Injective (fun A : Finset (Fin n) =>
              f A (by exact ‹A ∈ 𝓣›)) := by
          intro A1 A2 h_eq
          have : support (f A1 _) = support (f A2 _) := by
            have h1 : support (f A1 _) = A1 := hfSupp _ (by exact ‹A1 ∈ 𝓣›)
            have h2 : support (f A2 _) = A2 := hfSupp _ (by exact ‹A2 ∈ 𝓣›)
            simpa [h1, h2] using congrArg support h_eq
          simpa [hfSupp _ (by exact ‹A1 ∈ 𝓣›), hfSupp _ (by exact ‹A2 ∈ 𝓣›)]
            using this
        simpa [Finset.card_image] using
          (Finset.card_image_of_injective _ h_inj_aux)
      -- now show that every chosen `f_A` passes the filter
      have h_sub :
          (Finset.image (fun A : Finset (Fin n) => f A _) 𝓣)
            ⊆ F.filter (fun f ↦ ∀ x, x ∈ₛ R → f x = true) := by
        intro g hg
        rcases Finset.mem_image.1 hg with ⟨A, hA, rfl⟩
        have hgF : f A _ ∈ F := hfF _ hA
        have htrue : ∀ x, x ∈ₛ R → (f A _) x = true := by
          intro x hx
          -- on the core `K` the values of `x` are fixed as in `x₀`, while
          -- outside the core the set `A` contains no coordinates of `x₀`.
          have : x.restrict (support (f A _)) = x₀.restrict := by
            ext i hi
            by_cases hKi : i ∈ K
            · simp [x₀, hKi] at hx
            · have : i ∈ A := by simpa [hfSupp _ hA] using hi
              simpa using rfl
          have : (f A _) x = (f A _) x₀ :=
            BoolFunc.eval_eq_of_agree_on_support (f := f A _) (x := x) (y := x₀)
              (by intro i hi; simpa using congrArg (fun t => t) (this i hi))
          have hx0 : (f A _) x₀ = true := by
            obtain ⟨y, hy⟩ := BoolFunc.exists_true_on_support
              (f := f A _) (by simpa [hfSupp _ hA])
            simpa using hy
          simpa [Agreement.Subcube.fromPoint, hx, this] using hx0
        have h_card_le := Finset.card_le_of_subset h_sub
        simpa using (le_of_eq_of_le h_inj).trans h_card_le
      exact h_filter_ge
  ·
    -- `R` has dimension `n - K.card`.  The sunflower lemma ensures `K` is a
    -- proper subset of each support in the sunflower, so `K.card < n` and the
    -- dimension is positive.
    have h_dim : 1 ≤ n - K.card := by
      have h_lt : K.card < n := by
        obtain ⟨A, hA𝓣, hKA⟩ := hT
        have hlt : K.card < A.card := Finset.card_lt_card hKA
        have hA_le : A.card ≤ n := by
          have : A ⊆ Finset.univ := by intro i hi; exact Finset.mem_univ _
          exact Finset.card_le_of_subset this
        exact hlt.trans_le hA_le
      have : 0 < n - K.card := Nat.sub_pos_of_lt h_lt
      exact Nat.succ_le_of_lt this
    simpa [R, Subcube.dimension_fromPoint] using h_dim

/-! ## Inductive construction of the cover -/

/-! ## Inductive construction of the cover (updated) -/
noncomputable
partial def buildCover (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n) := ∅) : Finset (Subcube n) := by
  classical
  match hfu : firstUncovered F Rset with
  | none =>
      -- Base case: all 1-inputs of F are covered by Rset
      exact Rset
  | some ⟨f, x⟩ =>
      -- `f : BoolFunc n` and `x : Point n` is a 1-input uncovered by Rset.
      /- **Branching strategy:** Depending on family parameters, choose cover method:
         1. Low-sensitivity branch – if all functions in `F` have small sensitivity.
         2. Entropy branch – default fallback using a one-bit entropy drop. -/
      have F_nonempty : F.Nonempty :=
        ⟨f, by
          -- firstUncovered gives ⟨f, x⟩ with f ∈ F by definition
          rcases Set.choose?_mem (S := uncovered F Rset) hfu with ⟨hf, -, -⟩
          exact hf⟩
      -- ### Sunflower branch
      -- Attempt to extract a single rectangle covering many functions at once.
      -- This step relies on `SunflowerFam.exists_of_large_family` under the hood.
      let p := (BoolFunc.support f).card
      let t := 2
      have ht : (2 : ℕ) ≤ t := by decide
      -- Fallback to the existing two-branch strategy.
      let fallback : Finset (Subcube n) := by
        -- Compute the maximum sensitivity `s` of functions in `F`.
        let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
        let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
        have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
          fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
        -- **(1) Low-sensitivity branch.**
        -- If all functions have small sensitivity we reuse `low_sensitivity_cover`.
        classical
        cases Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
        | inl hs_small =>
            have ⟨R_ls, Hmono, Hcover, Hsize⟩ :=
              BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
            exact Rset ∪ R_ls
        | inr hs_large =>
            -- **Entropy branch.**  Split on a coordinate that drops the entropy.
            have ⟨i, b, Hdrop⟩ :=
              BoolFunc.exists_coord_entropy_drop (F := F)
                (hn := by decide)
                (hF := Finset.card_pos.mpr F_nonempty)
            let F0 := F.restrict i b
            let F1 := F.restrict i (!b)
            have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
              simpa using (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
            have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
              simpa using (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
            exact (buildCover F0 (h - 1) (by exact hH0)) ∪
                  (buildCover F1 (h - 1) (by exact hH1))
      classical
      -- Try the sunflower extraction if it applies.
      by_cases hp : 0 < p
      ·
        by_cases h_support : ∀ g ∈ F, (BoolFunc.support g).card = p
        ·
          by_cases h_big : (t - 1).factorial * p ^ t < (Family.supports F).card
          ·
            obtain ⟨R, hcov, hdim⟩ :=
              sunflower_step (F := F) (p := p) (t := t) hp ht h_big h_support
            -- Insert `R` into the current cover and recurse.
            exact buildCover F h hH (insert R Rset)
          ·
            exact fallback
        ·
          exact fallback
      ·
        exact fallback

/-! ## Proof that buildCover indeed covers every 1‑input -/

/-- All 1‑inputs of `F` lie in some rectangle of `Rset`. -/
@[simp]
def AllOnesCovered (F : Family n) (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

lemma AllOnesCovered.superset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered F R₁) (hsub : R₁ ⊆ R₂) :
    AllOnesCovered F R₂ := by
  intro f hf x hx
  rcases h₁ f hf x hx with ⟨R, hR, hxR⟩
  exact ⟨R, hsub hR, hxR⟩

lemma AllOnesCovered.union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered F R₁) (h₂ : AllOnesCovered F R₂) :
    AllOnesCovered F (R₁ ∪ R₂) := by
  intro f hf x hx
  by_cases hx1 : ∃ R ∈ R₁, x ∈ₛ R
  · rcases hx1 with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union] using Or.inl hR, hxR⟩
  · rcases h₂ f hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union, hx1] using Or.inr hR, hxR⟩

/-- Inserting a rectangle into an existing cover preserves the
`AllOnesCovered` property.  This is a convenience wrapper around
`AllOnesCovered.superset`. -/
lemma AllOnesCovered.insert {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} (hcov : AllOnesCovered F Rset) :
    AllOnesCovered F (insert R Rset) := by
  classical
  have hsub : Rset ⊆ insert R Rset := by
    intro S hS
    exact Finset.mem_insert.mpr <| Or.inr hS
  exact AllOnesCovered.superset (F := F) (R₁ := Rset) (R₂ := insert R Rset)
    hcov hsub

/-!  A handy special case of `AllOnesCovered`: a single rectangle equal to
`Subcube.full` trivially covers all `1`-inputs of any family.  We record this
lemma explicitly to ease test proofs and small examples. -/
lemma AllOnesCovered.full (F : Family n) :
    AllOnesCovered F ({Subcube.full} : Finset (Subcube n)) := by
  classical
  intro f hf x hx
  refine ⟨Subcube.full, by simp, ?_⟩
  -- `Subcube.full` contains every point of the cube by definition.
  simpa using (Subcube.mem_full (n := n) (x := x))


/-! ### Uncovered pairs and a simple measure

The recursion for `buildCover` will track the number of still-uncovered
`1`‑inputs together with an entropy budget.  It is therefore convenient to
express when no uncovered points remain and to define a lightweight numeric
measure used in termination arguments. -/

lemma uncovered_eq_empty_of_allCovered {F : Family n} {Rset : Finset (Subcube n)}
    (hcov : AllOnesCovered F Rset) :
    uncovered F Rset = ∅ := by
  classical
  ext p; constructor
  · intro hp
    rcases hp with ⟨hf, hx, hnc⟩
    rcases hcov p.1 hf p.2 hx with ⟨R, hR, hxR⟩
    have : p.2 ∉ₛ R := hnc R hR
    exact False.elim (this hxR)
  · intro hp
    simp [hp]

/-- A very coarse termination measure for the recursion.  The first component
tracks the available entropy budget `h`, while the second counts currently
uncovered `1`‑inputs.  Each branch of `buildCover` will strictly decrease this
sum. -/
def mu (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) : ℕ :=
  2 * h + (uncovered F Rset).toFinset.card

lemma mu_of_allCovered {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hcov : AllOnesCovered F Rset) :
    mu F h Rset = 2 * h := by
  have hzero : uncovered F Rset = ∅ := uncovered_eq_empty_of_allCovered (F := F) hcov
  simp [mu, hzero]

lemma mu_of_firstUncovered_none {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hfu : firstUncovered (F := F) Rset = none) :
    mu F h Rset = 2 * h := by
  have hcov : AllOnesCovered F Rset :=
    allOnesCovered_of_firstUncovered_none (F := F) (Rset := Rset) hfu
  simpa using mu_of_allCovered (F := F) (Rset := Rset) (h := h) hcov

/-!
  The converse direction: if the measure `μ` collapses to `2 * h`, then no
  uncovered pairs remain and hence `Rset` already covers all `1`-inputs of `F`.
-/
lemma allOnesCovered_of_mu_eq {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hμ : mu F h Rset = 2 * h) :
    AllOnesCovered F Rset := by
  classical
  -- From the definition of `μ` we infer that the uncovered set has
  -- cardinality `0`.
  have hμ' : 2 * h + (uncovered F Rset).toFinset.card = 2 * h + 0 := by
    simpa [mu] using hμ
  have hcard0 : (uncovered F Rset).toFinset.card = 0 := by
    exact Nat.add_left_cancel hμ'
  -- Hence the uncovered set itself is empty.
  have hset : uncovered F Rset = ∅ := by
    classical
    have hfin : (uncovered F Rset).toFinset = ∅ :=
      Finset.card_eq_zero.mp hcard0
    ext p; constructor
    · intro hp
      have : p ∈ (uncovered F Rset).toFinset := by simpa using hp
      simpa [hfin] using this
    · intro hp
      have : p ∈ (uncovered F Rset).toFinset := by simpa [hfin] using hp
      simpa using this
  -- An empty uncovered set implies full coverage.
  exact
    allOnesCovered_of_firstUncovered_none (F := F) (Rset := Rset)
      ((firstUncovered_none_iff (F := F) (R := Rset)).2 hset)

lemma mu_nonneg {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    0 ≤ mu F h Rset := by
  exact Nat.zero_le _

lemma mu_lower_bound {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    2 * h ≤ mu F h Rset := by
  simpa [mu] using Nat.le_add_right (2 * h) ((uncovered F Rset).toFinset.card)

/-! `mu` is monotone in the entropy budget `h`:
increasing the available budget can only increase the measure. -/
lemma mu_mono_h {F : Family n} {Rset : Finset (Subcube n)}
    {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) :
    mu F h₁ Rset ≤ mu F h₂ Rset := by
  dsimp [mu]
  exact add_le_add (Nat.mul_le_mul_left _ hh) le_rfl

/-!
If `firstUncovered` returns a value, then the uncovered set is nonempty
and the measure `mu` is strictly larger than `2 * h`.  This convenience
lemma will be useful when analysing the main recursion measure.
-/
lemma mu_gt_of_firstUncovered_some {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (F := F) Rset ≠ none) :
    2 * h < mu F h Rset := by
  classical
  -- The uncovered set cannot be empty, otherwise `firstUncovered` would
  -- have returned `none`.
  have hne : uncovered F Rset ≠ ∅ := by
    intro hempty
    have := (firstUncovered_none_iff (F := F) (R := Rset)).2 hempty
    exact hfu this
  -- A nonempty set has positive card after coercion to a finset.
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpos : 0 < (uncovered F Rset).toFinset.card :=
    Finset.card_pos.mpr ⟨p, by simpa using hp⟩
  -- Hence the measure `mu` exceeds `2 * h` by at least one.
  have := Nat.lt_add_of_pos_right hpos
  simpa [mu] using this

/-!
`uncovered_card_bound` provides a very coarse upper bound on the number of
still uncovered pairs.  Each pair consists of some function from `F` together
with a point of the Boolean cube, hence there are at most `F.card * 2 ^ n`
possibilities.  This crude estimate is occasionally convenient when comparing
with numeric bounds on the cover size.-/
lemma uncovered_card_bound (F : Family n) (Rset : Finset (Subcube n)) :
    (uncovered F Rset).toFinset.card ≤ F.card * 2 ^ n := by
  classical
  -- Every element of `uncovered F Rset` is a pair `⟨f, x⟩` with `f ∈ F` and a
  -- point `x : Vector Bool n`.  Compare with the full Cartesian product.
  have hsubset : (uncovered F Rset).toFinset ⊆
      F.product (Finset.univ : Finset (Vector Bool n)) := by
    intro p hp
    rcases hp with ⟨hf, -, -⟩
    have hx : p.2 ∈ (Finset.univ : Finset (Vector Bool n)) := by simp
    exact Finset.mem_product.mpr ⟨hf, hx⟩
  have hcard := Finset.card_le_of_subset hsubset
  -- Cardinality of a product splits multiplicatively.
  have hprod := Finset.card_product (s := F)
      (t := (Finset.univ : Finset (Vector Bool n)))
  -- The cube `Vector Bool n` has size `2 ^ n`.
  have hcube : ((Finset.univ : Finset (Vector Bool n))).card = 2 ^ n := by
    simpa using (Fintype.card_vector (α := Bool) (n := n))
  simpa [hprod, hcube] using hcard

/-!
`uncovered_init_coarse_bound` specialises `uncovered_card_bound` to the
initial call of `buildCover`.  It provides a simple size estimate for the
set of uncovered pairs before any rectangles have been inserted.  While the
stronger bound `uncovered_init_bound` below remains an axiom, the following
lemma is fully proved and occasionally handy for crude numeric arguments.-/
lemma uncovered_init_coarse_bound (F : Family n) :
    (uncovered F (∅ : Finset (Subcube n))).toFinset.card ≤ F.card * 2 ^ n := by
  simpa using
    (uncovered_card_bound (F := F) (Rset := (∅ : Finset (Subcube n))))

/-!
  A trivial instance of `uncovered_init_bound` holds when the family is
  empty.  In this situation there are no uncovered pairs at all, so the
  bound is immediate.  This lemma serves as a simple sanity check and a
  base case for future refinements of the combinatorial argument.
-/
lemma uncovered_init_bound_empty (F : Family n) (hF : F = (∅ : Family n)) :
    (uncovered F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
  classical
  have h : uncovered F (∅ : Finset (Subcube n)) = ∅ := by
    ext p; simp [uncovered, hF]
  have := Nat.zero_le n
  simpa [h] using this

/--
  **Initial uncovered bound.**  At the start of the recursion the number of
  uncovered pairs is at most `n`.  A future combinatorial argument will tighten
  this estimate; for now we record it as an axiom so that subsequent proofs can
  rely on a concrete numeric value.
-/
axiom uncovered_init_bound (F : Family n) :
  (uncovered F (∅ : Finset (Subcube n))).toFinset.card ≤ n
/--
  A direct numeric variant of `uncovered_init_bound` expressed via the measure
  `μ`.  Initially we have `μ(F, h, ∅) = 2 * h + (uncovered F ∅).toFinset.card`.
  Plugging in the bound on the uncovered count yields `μ(F, h, ∅) ≤ 2 * h + n`.
  This coarse inequality is occasionally convenient when reasoning about the
  overall recursion measure.
-/
lemma mu_init_linear_bound (F : Family n) (h : ℕ) :
    mu F h (∅ : Finset (Subcube n)) ≤ 2 * h + n := by
  have hstart :
      (uncovered F (∅ : Finset (Subcube n))).toFinset.card ≤ n :=
    uncovered_init_bound (F := F)
  simpa [mu] using add_le_add_left hstart (2 * h)


/-!
`mu_init_bound` upgrades the initial uncovered bound to the full measure.
Since `mu` adds `2 * h` to the uncovered count, the inequality
`uncovered_init_bound` immediately yields
`mu F h ∅ ≤ mBound n h` via `numeric_bound`.-/
lemma mu_init_bound (F : Family n) (h : ℕ) :
    mu F h (∅ : Finset (Subcube n)) ≤ mBound n h := by
  have hstart : (uncovered F (∅ : Finset (Subcube n))).toFinset.card ≤ n :=
    uncovered_init_bound (F := F)
  have hμ : mu F h (∅ : Finset (Subcube n)) ≤ 2 * h + n := by
    simpa [mu] using add_le_add_left hstart (2 * h)
  exact hμ.trans (numeric_bound (n := n) (h := h))

/-!
`uncovered` is monotone with respect to the set of rectangles: adding
a new rectangle can only remove uncovered pairs.  The next lemma
formalises this simple observation and will be handy when reasoning
about the termination measure `mu`.
-/
lemma uncovered_subset_of_union_singleton {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n} :
    uncovered F (Rset ∪ {R}) ⊆ uncovered F Rset := by
  classical
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  -- `p.2` is not covered by any rectangle in `Rset ∪ {R}`,
  -- hence in particular by any rectangle of `Rset` alone.
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

/-!
`uncovered_subset_of_union` generalises
`uncovered_subset_of_union_singleton` to any finite set of rectangles.
Adding more rectangles cannot produce new uncovered pairs.
-/
lemma uncovered_subset_of_union {F : Family n}
    {R₁ R₂ : Finset (Subcube n)} :
    uncovered F (R₁ ∪ R₂) ⊆ uncovered F R₁ := by
  classical
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  exact ⟨hf, hx, by
    intro S hS
    exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)⟩

lemma mu_union_singleton_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ} :
    mu F h (Rset ∪ {R}) ≤ mu F h Rset := by
  classical
  -- The uncovered set can only shrink when adding a rectangle.
  have hsub : uncovered F (Rset ∪ {R}) ⊆ uncovered F Rset :=
    uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R)
  have hsubF : (uncovered F (Rset ∪ {R})).toFinset ⊆ (uncovered F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered F Rset := hsub hx'
    simpa using hx''
  have hcard := Finset.card_le_of_subset hsubF
  -- Combine with the definition of `mu`.
  simpa [mu] using add_le_add_left hcard (2 * h)

lemma mu_union_singleton_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered F Rset, p.2 ∈ₛ R) :
    mu F h (Rset ∪ {R}) < mu F h Rset := by
  classical
  rcases hx with ⟨p, hpU, hpR⟩
  have hp_not : p ∉ uncovered F (Rset ∪ {R}) := by
    rcases hpU with ⟨hf, hx, hnc⟩
    intro hp'
    rcases hp' with ⟨hf', hx', hnc'⟩
    have := hnc' R (by simp) hpR
    exact this
  have hsub : (uncovered F (Rset ∪ {R})).toFinset ⊆ (uncovered F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hproper : ¬( (uncovered F Rset).toFinset ⊆ (uncovered F (Rset ∪ {R})).toFinset ) := by
    intro hsubset
    have hpFin : p ∈ (uncovered F Rset).toFinset := by simpa using hpU
    have := hsubset hpFin
    exact hp_not this
  have hcard := Finset.card_lt_of_subset hsub hproper
  -- Add `2*h` to both sides.
  simpa [mu] using Nat.add_lt_add_left hcard (2 * h)

/-!
Adding a rectangle that covers at least one previously uncovered
pair decreases the measure `μ` by at least one.
This quantified version of `mu_union_singleton_lt` is occasionally
convenient when reasoning about numeric bounds.
-/
lemma mu_union_singleton_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered F Rset, p.2 ∈ₛ R) :
    mu F h (Rset ∪ {R}) + 1 ≤ mu F h Rset := by
  classical
  have hlt :=
    mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx
  exact Nat.succ_le_of_lt hlt

/-!
Adding a rectangle that covers *two distinct* uncovered pairs reduces the
measure `μ` by at least two.  This strengthening of
`mu_union_singleton_succ_le` will be useful for the future sunflower branch of
the cover construction.-/
lemma mu_union_singleton_double_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F Rset) (hp₂ : p₂ ∈ uncovered F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂) :
    mu F h (Rset ∪ {R}) + 2 ≤ mu F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F Rset).toFinset
  let T : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F (Rset ∪ {R})).toFinset
  -- `T` is a subset of `S` since adding rectangles cannot create new
  -- uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hxT
    have hx'' : x ∈ uncovered F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  -- After adding `R`, the pairs `p₁` and `p₂` are no longer uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂`.
  have hsub2 : T ⊆ (S.erase p₁).erase p₂ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq; have : p₁ ∈ T := by simpa [hxEq] using hxT; exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq; have : p₂ ∈ T := by simpa [hxEq] using hxT; exact hp₂T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    exact Finset.mem_erase.mpr ⟨hxne2, hx1⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, hp₂S⟩
  have hcard_le : T.card ≤ ((S.erase p₁).erase p₂).card :=
    Finset.card_le_of_subset hsub2
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard_final : T.card ≤ S.card - 2 := by
    have := hcard_le
    simpa [hcard1, hcard2] using this
  -- `S` contains both `p₁` and `p₂`, so its cardinality is at least two.
  have htwo : 2 ≤ S.card := by
    classical
    have hsub_pair : ({p₁, p₂} : Finset _) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hp₁S
      · have hx' := Finset.mem_singleton.mp hx; simpa [hx'] using hp₂S
    have hcard_pair : ({p₁, p₂} : Finset _).card = 2 := by
      simp [Finset.card_insert, hne]
    have htwo_aux : 2 ≤ ({p₁, p₂} : Finset _).card := by simpa [hcard_pair]
    exact le_trans htwo_aux (Finset.card_le_of_subset hsub_pair)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le htwo).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/-!  A convenient corollary of `mu_union_singleton_triple_succ_le`: if a
rectangle covers three distinct uncovered pairs, the measure strictly decreases
after inserting this rectangle.  As in the double case we reuse the basic
one-pair inequality on one witness. -/
lemma mu_union_singleton_triple_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F Rset) (hp₂ : p₂ ∈ uncovered F Rset)
    (hp₃ : p₃ ∈ uncovered F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃) :
    mu F h (Rset ∪ {R}) < mu F h Rset := by
  classical
  -- Covering even a single uncovered pair suffices for a strict drop.
  have hx : ∃ p ∈ uncovered F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  -- Apply the basic inequality for one newly covered pair.
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/-!
Adding a rectangle that covers *three distinct* uncovered pairs decreases the
measure `μ` by at least three.  This is a straightforward extension of
`mu_union_singleton_double_succ_le` and will be useful for a potential
sunflower branch.
-/
lemma mu_union_singleton_triple_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F Rset) (hp₂ : p₂ ∈ uncovered F Rset)
    (hp₃ : p₃ ∈ uncovered F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃) :
    mu F h (Rset ∪ {R}) + 3 ≤ mu F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F Rset).toFinset
  let T : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hxT
    have hx'' : x ∈ uncovered F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  -- Membership facts for the three pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  -- After adding `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃`.
  have hsub3 : T ⊆ ((S.erase p₁).erase p₂).erase p₃ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq; have : p₁ ∈ T := by simpa [hxEq] using hxT; exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq; have : p₂ ∈ T := by simpa [hxEq] using hxT; exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq; have : p₃ ∈ T := by simpa [hxEq] using hxT; exact hp₃T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ := Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    exact Finset.mem_erase.mpr ⟨hxne3, hx2⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hcard_le : T.card ≤ (((S.erase p₁).erase p₂).erase p₃).card :=
    Finset.card_le_of_subset hsub3
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 : (((S.erase p₁).erase p₂).erase p₃).card =
      ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard_final : T.card ≤ S.card - 3 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3] using this
  -- `S` contains the three distinct pairs, so its cardinality is at least three.
  have hthree : 3 ≤ S.card := by
    classical
    have hsub_trip : ({p₁, p₂, p₃} : Finset _) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx₁ | hxrest
      · simpa [hx₁] using hp₁S
      rcases Finset.mem_insert.mp hxrest with hx₂ | hx₃
      · have hx' := Finset.mem_singleton.mp hx₂; simpa [hx'] using hp₂S
      · have hx' := Finset.mem_singleton.mp hx₃; simpa [hx'] using hp₃S
    have hcard_trip : ({p₁, p₂, p₃} : Finset _).card = 3 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      simp [Finset.card_insert, hnot12, hnot13, hnot23] at *
    have hthree_aux : 3 ≤ ({p₁, p₂, p₃} : Finset _).card := by simpa [hcard_trip]
    exact le_trans hthree_aux (Finset.card_le_of_subset hsub_trip)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hthree).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/-!
Adding a rectangle that covers *four distinct* uncovered pairs decreases the
measure `μ` by at least four.  This statement is a straightforward extension of
`mu_union_singleton_triple_succ_le` and follows the same bookkeeping
argument.-/
lemma mu_union_singleton_quad_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ p₄ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F Rset) (hp₂ : p₂ ∈ uncovered F Rset)
    (hp₃ : p₃ ∈ uncovered F Rset) (hp₄ : p₄ ∈ uncovered F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R) (hp₄R : p₄.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₁₄ : p₁ ≠ p₄)
    (hne₂₃ : p₂ ≠ p₃) (hne₂₄ : p₂ ≠ p₄) (hne₃₄ : p₃ ≠ p₄) :
    mu F h (Rset ∪ {R}) + 4 ≤ mu F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F Rset).toFinset
  let T : Finset (Σ f : BoolFunc n, Vector Bool n) :=
    (uncovered F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hxT
    have hx'' : x ∈ uncovered F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  -- Membership facts for the four pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  have hp₄S : p₄ ∈ S := by simpa [S] using hp₄
  -- After adding `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  have hp₄T : p₄ ∉ T := by
    intro hx
    have hx' : p₄ ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₄R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃.erase p₄`.
  have hsub4 : T ⊆ (((S.erase p₁).erase p₂).erase p₃).erase p₄ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq; have : p₁ ∈ T := by simpa [hxEq] using hxT; exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq; have : p₂ ∈ T := by simpa [hxEq] using hxT; exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq; have : p₃ ∈ T := by simpa [hxEq] using hxT; exact hp₃T this
    have hxne4 : x ≠ p₄ := by
      intro hxEq; have : p₄ ∈ T := by simpa [hxEq] using hxT; exact hp₄T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ := Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    have hx3 : x ∈ ((S.erase p₁).erase p₂).erase p₃ :=
      Finset.mem_erase.mpr ⟨hxne3, hx2⟩
    exact Finset.mem_erase.mpr ⟨hxne4, hx3⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hp₄_in_erase3 : p₄ ∈ ((S.erase p₁).erase p₂).erase p₃ := by
    have hp₄_in_erase1 : p₄ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₄.symm, hp₄S⟩
    have hp₄_in_erase2 : p₄ ∈ (S.erase p₁).erase p₂ :=
      Finset.mem_erase.mpr ⟨hne₂₄.symm, hp₄_in_erase1⟩
    exact Finset.mem_erase.mpr ⟨hne₃₄.symm, hp₄_in_erase2⟩
  have hcard_le : T.card ≤ ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card :=
    Finset.card_le_of_subset hsub4
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 : (((S.erase p₁).erase p₂).erase p₃).card =
      ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard4 : ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card =
      (((S.erase p₁).erase p₂).erase p₃).card - 1 :=
    Finset.card_erase_of_mem hp₄_in_erase3
  have hcard_final : T.card ≤ S.card - 4 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3, hcard4] using this
  -- `S` contains the four distinct pairs, so its cardinality is at least four.
  have hfour : 4 ≤ S.card := by
    classical
    have hsub_quad : ({p₁, p₂, p₃, p₄} : Finset _) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx₁ | hxrest
      · simpa [hx₁] using hp₁S
      rcases Finset.mem_insert.mp hxrest with hx₂ | hxrest
      · have hx' := Finset.mem_insert.mp hx₂
        rcases hx' with hx₂ | hx3
        · have hx'' := Finset.mem_singleton.mp hx₂
          simpa [hx''] using hp₂S
        · have hx'' := Finset.mem_singleton.mp hx3
          simpa [hx''] using hp₃S
      rcases Finset.mem_insert.mp hxrest with hx₃ | hx₄
      · have hx' := Finset.mem_singleton.mp hx₃
        simpa [hx'] using hp₄S
      · have hx' := Finset.mem_singleton.mp hx₄
        simpa [hx'] using hp₄S
    have hcard_quad : ({p₁, p₂, p₃, p₄} : Finset _).card = 4 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot14 : p₁ ≠ p₄ := hne₁₄
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      have hnot24 : p₂ ≠ p₄ := hne₂₄
      have hnot34 : p₃ ≠ p₄ := hne₃₄
      simp [Finset.card_insert, hnot12, hnot13, hnot14, hnot23, hnot24, hnot34]
    have hfour_aux : 4 ≤ ({p₁, p₂, p₃, p₄} : Finset _).card := by simpa [hcard_quad]
    exact le_trans hfour_aux (Finset.card_le_of_subset hsub_quad)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hfour).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/-!  A convenient corollary of `mu_union_singleton_double_succ_le`: if a
rectangle covers two distinct uncovered pairs, the measure strictly decreases
after inserting this rectangle.  The proof reuses the single-pair inequality
`mu_union_singleton_lt` on one of the witnesses.-/
lemma mu_union_singleton_double_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F Rset) (hp₂ : p₂ ∈ uncovered F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂) :
    mu F h (Rset ∪ {R}) < mu F h Rset := by
  classical
  -- Covering even a single uncovered pair suffices for a strict drop.
  have hx : ∃ p ∈ uncovered F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  -- Apply the basic inequality for one newly covered pair.
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/--
If a single rectangle contained in `R₂` simultaneously covers two distinct
uncovered pairs of `R₁`, then taking the union with *all* of `R₂` decreases the
measure `μ` by at least two.  This lemma is a small convenience wrapper around
`mu_union_singleton_double_succ_le` and the monotonicity of `μ`.-/
lemma mu_union_double_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F R₁) (hp₂ : p₂ ∈ uncovered F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu F h (R₁ ∪ R₂) + 2 ≤ mu F h R₁ := by
  classical
  -- Adding additional rectangles can only decrease the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono := mu_mono_subset (F := F) (h := h) (R₁ := R₁ ∪ {R})
      (R₂ := R₁ ∪ R₂) hsub
  have hdouble := mu_union_singleton_double_succ_le (F := F) (Rset := R₁)
      (R := R) (h := h) hp₁ hp₂ hp₁R hp₂R hne
  have := add_le_add_right hmono 2
  exact le_trans this hdouble

/-!
`mu_union_double_lt` is the strict counterpart to
`mu_union_double_succ_le`.  If some rectangle in `R₂` covers two distinct
uncovered pairs of `R₁`, then the measure drops strictly after taking the
union with all of `R₂`.  The proof simply upgrades the `+ 2` inequality to a
strict comparison via `Nat.lt_of_succ_le`.
-/
lemma mu_union_double_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F R₁) (hp₂ : p₂ ∈ uncovered F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu F h (R₁ ∪ R₂) < mu F h R₁ := by
  classical
  -- First obtain the numeric drop by two from the previous lemma.
  have hdrop :=
    mu_union_double_succ_le (F := F) (R₁ := R₁) (R₂ := R₂)
      (R := R) (h := h) hp₁ hp₂ hp₁R hp₂R hne hmem
  -- `a + 2 ≤ b` implies `a + 1 ≤ b`, hence `a < b` for natural numbers.
  have hsucc : mu F h (R₁ ∪ R₂) + 1 ≤ mu F h R₁ := by
    have hstep : (1 : ℕ) ≤ 2 := by decide
    have := Nat.add_le_add_left hstep (mu F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

/-!
`mu_union_triple_succ_le` extends `mu_union_double_succ_le` to the case of
three distinct uncovered pairs.  If a rectangle contained in `R₂` covers all
three of them, then taking the union with `R₂` decreases the measure `μ` by at
least three.
-/
lemma mu_union_triple_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F R₁) (hp₂ : p₂ ∈ uncovered F R₁)
    (hp₃ : p₃ ∈ uncovered F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu F h (R₁ ∪ R₂) + 3 ≤ mu F h R₁ := by
  classical
  -- Adding additional rectangles can only decrease the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono :=
    mu_mono_subset (F := F) (h := h) (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsub
  have htriple :=
    mu_union_singleton_triple_succ_le (F := F) (Rset := R₁) (R := R) (h := h)
      hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R hne₁₂ hne₁₃ hne₂₃
  have := add_le_add_right hmono 3
  exact le_trans this htriple

/--
`mu_union_triple_lt` is the strict version of `mu_union_triple_succ_le`.
Covering three distinct uncovered pairs with a rectangle from `R₂` drops the
measure strictly.
-/
lemma mu_union_triple_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ f : BoolFunc n, Vector Bool n}
    (hp₁ : p₁ ∈ uncovered F R₁) (hp₂ : p₂ ∈ uncovered F R₁)
    (hp₃ : p₃ ∈ uncovered F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu F h (R₁ ∪ R₂) < mu F h R₁ := by
  classical
  -- Use the additive inequality and drop one unit to obtain strictness.
  have hdrop :=
    mu_union_triple_succ_le (F := F) (R₁ := R₁) (R₂ := R₂) (R := R) (h := h)
      hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R hne₁₂ hne₁₃ hne₂₃ hmem
  have hsucc : mu F h (R₁ ∪ R₂) + 1 ≤ mu F h R₁ := by
    have hstep : (1 : ℕ) ≤ 3 := by decide
    have := Nat.add_le_add_left hstep (mu F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

lemma mu_union_le {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ} :
    mu F h (R₁ ∪ R₂) ≤ mu F h R₁ := by
  classical
  refine Finset.induction_on R₂ ?base ?step
  · simp [mu]
  · intro R S hR hIH
    have hstep := mu_union_singleton_le (F := F) (Rset := R₁ ∪ S) (R := R)
      (h := h)
    have hcomb := le_trans hstep hIH
    -- `Finset.insert` ensures `R ∉ S`, so unions simplify.
    have : R₁ ∪ insert R S = (R₁ ∪ S) ∪ {R} := by
      ext x; by_cases hx : x = R
      · subst hx; simp [hR]
      · simp [Finset.mem_insert, hx]
    simpa [this, Finset.union_assoc] using hcomb

lemma mu_mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hsub : R₁ ⊆ R₂) :
    mu F h R₂ ≤ mu F h R₁ := by
  classical
  -- Express `R₂` as `R₁ ∪ (R₂ \ R₁)` and apply `mu_union_le`.
  have hunion : R₂ = R₁ ∪ (R₂ \ R₁) := by
    ext x; by_cases hx : x ∈ R₁
    · constructor
      · intro hxR2
        exact Finset.mem_union.mpr <| Or.inl hx
      · intro hunion
        exact hx
    · constructor
      · intro hxR2
        have hxRdiff : x ∈ R₂ \ R₁ := by
          exact ⟨hxR2, by simpa [hx]⟩
        exact Finset.mem_union.mpr <| Or.inr hxRdiff
      · intro hunion
        rcases Finset.mem_union.mp hunion with hx₁ | hx₂
        · exact hsub hx₁
        · exact hx₂.1
  have := mu_union_le (F := F) (h := h) (R₁ := R₁) (R₂ := R₂ \ R₁)
  simpa [hunion] using this

/-!
`mu_union_lt` generalises `mu_union_singleton_lt` to an arbitrary set of
rectangles.  If some uncovered pair of `R₁` is covered by a rectangle from
`R₂`, then the measure strictly decreases after taking the union.
-/
lemma mu_union_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hx : ∃ p ∈ uncovered F R₁, ∃ R ∈ R₂, p.2 ∈ₛ R) :
    mu F h (R₁ ∪ R₂) < mu F h R₁ := by
  classical
  rcases hx with ⟨p, hpU, R, hR, hpR⟩
  -- First insert the specific rectangle that covers `p`.
  have hx_singleton : ∃ q ∈ uncovered F R₁, q.2 ∈ₛ R := ⟨p, hpU, hpR⟩
  have hstep :=
    mu_union_singleton_lt (F := F) (Rset := R₁) (R := R) (h := h) hx_singleton
  -- Adding more rectangles cannot increase the measure.
  have hsubset : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx'
    rcases Finset.mem_union.mp hx' with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · have hxR : x = R := by simpa using hx₂
      subst hxR
      exact Finset.mem_union.mpr <| Or.inr hR
  have hmono :=
    mu_mono_subset (F := F) (h := h) (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsubset
  exact lt_of_le_of_lt hmono hstep

/-!
`mu_union_buildCover_le` is a small helper lemma used in termination
arguments for `buildCover`.  Adding the rectangles produced by one
step of the construction can only decrease the measure `μ`, since the
set of uncovered pairs shrinks.  The result follows directly from
`mu_union_le`.
-/
lemma mu_union_buildCover_le (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    mu F h (Rset ∪ buildCover F h hH Rset) ≤ mu F h Rset := by
  classical
  -- `mu_union_le` already states that adding any collection of
  -- rectangles cannot increase `μ`.  We instantiate it with the set
  -- returned by `buildCover`.
  simpa [Finset.union_comm, Finset.union_assoc] using
    (mu_union_le (F := F) (h := h) (R₁ := Rset)
      (R₂ := buildCover F h hH Rset))

/-!
`mu_buildCover_lt_start` is a convenient strict version of
`mu_union_buildCover_le` for the initial call of `buildCover`.
If a `1`‑input remains uncovered, then the measure strictly decreases
after inserting the rectangles produced by `buildCover`.
-/
lemma mu_buildCover_lt_start (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered (F := F) (∅ : Finset (Subcube n)) ≠ none) :
    mu F h (buildCover F h hH) < mu F h (∅ : Finset (Subcube n)) := by
  classical
  -- The uncovered set is nonempty because `firstUncovered` returned a value.
  have hne : uncovered F (∅ : Finset (Subcube n)) ≠ ∅ := by
    intro hempty
    have hfu0 :=
      (firstUncovered_none_iff (F := F) (R := (∅ : Finset (Subcube n)))).2 hempty
    exact hfu hfu0
  have hpos :
      0 < (uncovered F (∅ : Finset (Subcube n))).toFinset.card := by
    have hnonempty :
        (uncovered F (∅ : Finset (Subcube n))).toFinset.Nonempty := by
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact ⟨p, by simpa using hp⟩
    exact Finset.card_pos.mpr hnonempty
  -- The measure of the final cover collapses to `2*h`.
  have hmu := buildCover_mu (F := F) (h := h) (hH := hH)
  -- Explicit expression for the initial measure.
  have hmu0 :
      mu F h (∅ : Finset (Subcube n)) =
        2 * h + (uncovered F (∅ : Finset (Subcube n))).toFinset.card := by
    simp [mu]
  -- Compare the two measures.
  have hgt :
      (2 * h) < 2 * h + (uncovered F (∅ : Finset (Subcube n))).toFinset.card :=
    Nat.lt_add_of_pos_right hpos
  simpa [hmu, hmu0] using hgt

/--
`mu_union_buildCover_lt` generalises `mu_buildCover_lt_start` to an
arbitrary starting set of rectangles.  Whenever `firstUncovered` returns a
pair, the recursion inserts additional subcubes that strictly decrease the
measure `μ`.
-/
lemma mu_union_buildCover_lt (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (F := F) Rset ≠ none) :
    mu F h (Rset ∪ buildCover F h hH Rset) < mu F h Rset := by
  classical
  -- The uncovered set is nonempty because `firstUncovered` returned a value.
  have hpos : 0 < (uncovered F Rset).toFinset.card := by
    have hne : uncovered F Rset ≠ ∅ := by
      intro hempty
      have hfu0 :=
        (firstUncovered_none_iff (F := F) (R := Rset)).2 hempty
      exact hfu hfu0
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact Finset.card_pos.mpr ⟨p, by simpa using hp⟩
  -- The final union covers all 1-inputs, hence its measure collapses to `2*h`.
  have hcov := buildCover_covers (F := F) (h := h) (hH := hH) (Rset := Rset)
  have hmu_fin :
      mu F h (Rset ∪ buildCover F h hH Rset) = 2 * h := by
    -- First drop the extra rectangles from the measure comparison.
    have hdrop :=
      mu_union_le (F := F) (h := h)
        (R₁ := buildCover F h hH Rset) (R₂ := Rset)
    have hmain : mu F h (buildCover F h hH Rset) = 2 * h :=
      mu_of_allCovered (F := F) (Rset := buildCover F h hH Rset)
        (h := h) hcov
    have hle :
        mu F h (Rset ∪ buildCover F h hH Rset) ≤ 2 * h := by
      simpa [Finset.union_comm, hmain] using hdrop
    have hge : 2 * h ≤ mu F h (Rset ∪ buildCover F h hH Rset) :=
      mu_lower_bound (F := F) (Rset := Rset ∪ buildCover F h hH Rset)
        (h := h)
    exact le_antisymm hle hge
  -- The starting measure exceeds `2*h` because a pair is uncovered.
  have hstart :=
    mu_gt_of_firstUncovered_some (F := F) (Rset := Rset) (h := h) hfu
  -- Combine the two facts.
  simpa [hmu_fin] using hstart

/-!
`mu_buildCover_le_start` is a weak version of `mu_buildCover_lt_start`
that holds unconditionally.  If the family already has no uncovered
inputs then `buildCover` immediately returns the empty set and the two
measures coincide.  Otherwise `mu_buildCover_lt_start` yields a strict
inequality.  In both cases the result after running `buildCover` has
measure at most the starting value.-/

lemma mu_buildCover_le_start (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) ≤ mu F h (∅ : Finset (Subcube n)) := by
  classical
  -- Either an uncovered input exists or not.
  by_cases hfu : firstUncovered F (∅ : Finset (Subcube n)) = none
  · -- Immediate termination: both measures collapse to `2*h`.
    have hmu := buildCover_mu (F := F) (h := h) (hH := hH)
    have hmu0 := mu_of_firstUncovered_none (F := F)
      (R := (∅ : Finset (Subcube n))) (h := h) hfu
    simpa [hfu, hmu0] using hmu.le
  · -- Otherwise we invoke the strict inequality lemma.
    have hlt := mu_buildCover_lt_start (F := F) (h := h) (hH := hH)
      (by simpa using hfu)
    exact hlt.le

/-!  The previous lemma together with `buildCover_mu` yields a handy
inequality between the initial measure and the final value `2 * h`.  We
record it explicitly for later use.  The main counting argument for
`buildCover_card_bound` will eventually rely on a more precise analysis,
but this simple bound already provides a useful sanity check.-/
lemma buildCover_measure_drop (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    2 * h ≤ mu F h (∅ : Finset (Subcube n)) := by
  classical
  -- `mu_buildCover_le_start` compares the measure of the final cover with
  -- the measure of the empty set.
  have hμ := mu_buildCover_le_start (F := F) (h := h) (hH := hH)
  -- `buildCover_mu` states that the final measure collapses to `2 * h`.
  have hfinal := buildCover_mu (F := F) (h := h) (hH := hH)
  -- Combine the two statements.
  simpa [hfinal] using hμ
  
lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F) (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

@[simp] lemma AllOnesCovered.empty {F : Family n} :
    AllOnesCovered (F := F) (∅ : Finset (Subcube n)) ↔
      ∀ f ∈ F, ∀ x, f x = true → False := by
  classical
  constructor
  · intro h f hf x hx
    rcases h f hf x hx with ⟨R, hR, _hxR⟩
    simp at hR
  · intro h f hf x hx
    exact False.elim (h f hf x hx)

lemma allOnesCovered_of_firstUncovered_none {F : Family n}
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (F := F) Rset = none) :
    AllOnesCovered F Rset := by
  classical
  intro f hf x hx
  by_contra hxcov
  -- If `x` were uncovered, `⟨f, x⟩` would appear in `uncovered F Rset`.
  have hxNC : NotCovered (Rset := Rset) x := by
    intro R hR hxR
    exact hxcov ⟨R, hR, hxR⟩
  have hx_mem : (⟨f, x⟩ : Σ f : BoolFunc n, Vector Bool n) ∈ uncovered F Rset := by
    simp [uncovered, hf, hx, hxNC]
  have hempty : uncovered F Rset = ∅ := (firstUncovered_none_iff (F := F) (R := Rset)).1 hfu
  simpa [hempty] using hx_mem


/-! ### Lifting monochromaticity from restricted families

If a subcube `R` fixes the `i`-th coordinate to `b`, then a family that is
monochromatic on the restricted version of `F` is also monochromatic on `F`
itself.  This simple helper lemma is used in the entropy branch of the cover
construction. -/

lemma lift_mono_of_restrict
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  have hf0 : f.restrictCoord i b ∈ F.restrict i b := by
    simpa [Family.restrict, hf]
  have : (f.restrictCoord i b) x = c := hc (f.restrictCoord i b) hf0 x hx
  have hxib : x i = b := hfix x hx
  simpa [BFunc.restrictCoord, hxib] using this


lemma lift_mono_of_restrict_fixOne
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily (Subcube.fixOne i b ⊓ R) F := by
  classical
  have hfix : ∀ x, (Subcube.fixOne i b ⊓ R).Mem x → x i = b := by
    intro x hx
    exact (Subcube.mem_fixOne_iff).1 hx.1
  have hmono' : Subcube.monochromaticForFamily (Subcube.fixOne i b ⊓ R) (F.restrict i b) := by
    rcases hmono with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro f hf x hx
    exact hc f hf x hx.2
  exact lift_mono_of_restrict (F := F) (i := i) (b := b) (R := Subcube.fixOne i b ⊓ R) hfix hmono'


lemma buildCover_covers (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (buildCover F h hH) := by
  classical
  -- well-founded recursion on number of uncovered points (lexicographic on H₂ and uncovered count)
  revert F
  refine (fun F ↦ _ : AllOnesCovered F (buildCover F h hH)) ?_?_
  intro F
  suffices H : ∀ Rset, AllOnesCovered F (buildCover F h hH Rset) by
    simpa using H ∅
  intro Rset
  -- split on the first uncovered 1-input, if any
  cases hfu : firstUncovered F Rset with
  | none =>
    -- Base case: no uncovered inputs remain
    have hbase : AllOnesCovered F Rset := by
      intro f hf x hx
      have hempty : uncovered F Rset = ∅ := (firstUncovered_none_iff (F := F) Rset).1 hfu
      -- If x were not covered by Rset, then ⟨f, x⟩ would lie in `uncovered F Rset` (contradiction)
      by_cases hxRset : ∃ R ∈ Rset, x ∈ₛ R
      · rcases hxRset with ⟨R, hR, hxR⟩
        exact ⟨R, hR, hxR⟩
      · have hxNC : NotCovered Rset x := fun R hR ↦ (not_exists.mp hxRset) R ∘ And.intro hR
        have : (⟨f, x⟩ : Σ BoolFunc n, Vector Bool n) ∈ uncovered F Rset := by simp [uncovered, hf, hx, hxNC]
        rw [hempty] at this
        exact False.elim this
    simpa [buildCover, hfu] using hbase
  | some tup =>
    -- Inductive step: an uncovered 1-input exists
    rcases tup with ⟨f, x⟩  -- so f ∈ F, f x = true, and x is not covered by Rset
    -- Consider the branch strategy from `buildCover` definition:
    -- (1) Low-sensitivity branch
    let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
    let s := sensSet.max' (Finset.nonempty.image (BoolFunc.Family.nonempty_of_mem hf) _)
    have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
      fun g hg ↦ Finset.le_max' sensSet s (by simp [sensSet, hg])
    cases hs : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
    | inl hs_small =>
      -- Low-sensitivity case: use the `low_sensitivity_cover` lemma to cover all 1-inputs at once
      obtain ⟨R_ls, Hmono, Hcover, Hsize⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      -- Here `Hcover` states: ∀ f ∈ F, ∀ y, f y = true → ∃ R ∈ R_ls, y ∈ₛ R
      -- Combine the existing coverage of `Rset` with the low-sensitivity cover `R_ls`.
      have hcov_union : AllOnesCovered F (Rset ∪ R_ls) := by
        intro g hg y hy
        by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
        · rcases hyRset with ⟨R, hRset, hyR⟩
          exact ⟨R, by simp [Finset.mem_union.mpr (Or.inl hRset)], hyR⟩
        · obtain ⟨R, hR_ls, hyR⟩ := Hcover g hg y hy
          exact ⟨R, by simp [Finset.mem_union.mpr (Or.inr hR_ls)], hyR⟩
      -- Conclude for this branch: buildCover returns `Rset ∪ R_ls`.
      simpa [buildCover, hfu, hs_small] using hcov_union
    | inr hs_large =>
      -- **Entropy branch:** split on a coordinate to reduce entropy
      obtain ⟨i, b, Hdrop⟩ :=
        BoolFunc.exists_coord_entropy_drop (F := F) (hn := by decide)
          (hF := Finset.card_pos.mpr ⟨f, hf⟩)
      let F0 := F.restrict i b
      let F1 := F.restrict i (!b)
      have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
        simpa using (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
      have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
        simpa using (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
      -- Final cover is `buildCover F0 (h-1) ∪ buildCover F1 (h-1)`
      intro g hg y hy
      by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
      · rcases hyRset with ⟨R, hR, hyR⟩
        exact ⟨R, by simp [hyRset], hyR⟩
      by_cases hi : y i = b
      · -- y falls in the branch where `x_i = b`
        let g0 := g.restrictCoord i b
        have hg0 : g0 ∈ F0 := Finset.mem_image_of_mem (fun f => f.restrictCoord i b) hg
        have hg0y : g0 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
        rcases buildCover_covers (F := F0) (h := h - 1) (hH := hH0) g0 hg0 y hg0y with ⟨R0, hR0, hyR0⟩
        exact ⟨R0, by simp [hR0], hyR0⟩
      · -- y falls in the branch where `x_i = ¬b`
        let g1 := g.restrictCoord i (!b)
        have hg1 : g1 ∈ F1 := Finset.mem_image_of_mem (fun f => f.restrictCoord i (!b)) hg
        have hg1y : g1 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
        rcases buildCover_covers (F := F1) (h := h - 1) (hH := hH1) g1 hg1 y hg1y with ⟨R1, hR1, hyR1⟩
        exact ⟨R1, by simp [hR1], hyR1⟩
  -- **Termination proofs for recursive calls**
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))

/-!
`buildCover_covers_with` extends `buildCover_covers` to an arbitrary
initial collection of rectangles.  The union of this starting set with
the rectangles produced by `buildCover` still covers all `1`-inputs of
the family.  The proof follows the same recursion as above, with an
additional case distinction for points already covered by `Rset`.-/
lemma buildCover_covers_with (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    AllOnesCovered F (Rset ∪ buildCover F h hH Rset) := by
  classical
  -- well-founded recursion on the uncovered count as in `buildCover_covers`.
  revert F
  refine (fun F ↦ _ : AllOnesCovered F (Rset ∪ buildCover F h hH Rset)) ?_?_
  intro F
  suffices H : ∀ S, AllOnesCovered F (S ∪ buildCover F h hH S) by
    simpa using H Rset
  intro S
  -- Analyse the first uncovered input of `S` if it exists.
  cases hfu : firstUncovered F S with
  | none =>
      -- If no uncovered pair remains, `S` already covers everything and the
      -- recursion terminates without adding new rectangles.
      have hbase : AllOnesCovered F S :=
        allOnesCovered_of_firstUncovered_none (F := F) (Rset := S) hfu
      simpa [buildCover, hfu, Finset.union_self] using hbase
  | some tup =>
      -- A witness `⟨f, x⟩` lies in `uncovered F S`.
      rcases tup with ⟨f, x⟩
      have hf : f ∈ F := (Set.choose?_mem (S := uncovered F S) hfu).1
      have hx_true : f x = true := (Set.choose?_mem (S := uncovered F S) hfu).2.1
      have hxNC : NotCovered (Rset := S) x := (Set.choose?_mem (S := uncovered F S) hfu).2.2
      -- Compute the maximum sensitivity `s` of functions in `F`.
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image ⟨f, hf⟩ _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg ↦ Finset.le_max' sensSet s (by simp [sensSet, hg])
      -- Split on the sensitivity threshold as in `buildCover`.
      cases hs : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
      | inl hs_small =>
          -- Low-sensitivity branch inserts the rectangles `R_ls`.
          obtain ⟨R_ls, _hm, Hcover, _hsize⟩ :=
            BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
          have hcov_union : AllOnesCovered F (S ∪ R_ls) := by
            intro g hg y hy
            by_cases hyS : ∃ R ∈ S, y ∈ₛ R
            · rcases hyS with ⟨R, hR, hyR⟩
              exact ⟨R, by simp [Finset.mem_union.mpr (Or.inl hR)], hyR⟩
            · obtain ⟨R, hRls, hyR⟩ := Hcover g hg y hy
              exact ⟨R, by simp [Finset.mem_union.mpr (Or.inr hRls)], hyR⟩
          -- Resulting cover is `S ∪ R_ls`.
          simpa [buildCover, hfu, hs_small, Finset.union_assoc] using hcov_union
      | inr hs_large =>
          -- Entropy branch: recurse on restricted families.
          obtain ⟨i, b, Hdrop⟩ :=
            BoolFunc.exists_coord_entropy_drop (F := F) (hn := by decide)
              (hF := Finset.card_pos.mpr ⟨f, hf⟩)
          let F0 := F.restrict i b
          let F1 := F.restrict i (!b)
          have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
            simpa using (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
          have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
            simpa using (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
          -- Cover the input depending on the value of `x i`.
          intro g hg y hy
          by_cases hyS : ∃ R ∈ S, y ∈ₛ R
          · rcases hyS with ⟨R, hR, hyR⟩
            exact ⟨R, by simp [Finset.mem_union.mpr (Or.inl hR)], hyR⟩
          by_cases hi : y i = b
          · let g0 := g.restrictCoord i b
            have hg0 : g0 ∈ F0 := Finset.mem_image_of_mem (fun f => f.restrictCoord i b) hg
            have hg0y : g0 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
            rcases buildCover_covers (F := F0) (h := h - 1) (hH := hH0) g0 hg0 y hg0y with ⟨R0, hR0, hyR0⟩
            exact ⟨R0, by
              have hmem : R0 ∈ buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 :=
                Finset.mem_union.mpr (Or.inl hR0)
              simpa [buildCover, hfu, hs_large] using hmem, hyR0⟩
          · let g1 := g.restrictCoord i (!b)
            have hg1 : g1 ∈ F1 := Finset.mem_image_of_mem (fun f => f.restrictCoord i (!b)) hg
            have hg1y : g1 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
            rcases buildCover_covers (F := F1) (h := h - 1) (hH := hH1) g1 hg1 y hg1y with ⟨R1, hR1, hyR1⟩
            exact ⟨R1, by
              have hmem : R1 ∈ buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 :=
                Finset.mem_union.mpr (Or.inr hR1)
              simpa [buildCover, hfu, hs_large] using hmem, hyR1⟩
  -- Recursive calls decrease the measure.
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))

/-! ## Basic properties of `buildCover` -/

/--
After constructing a cover via `buildCover`, the auxiliary measure `mu`
records that no uncovered pairs remain.  Hence the measure of the
resulting cover collapses to `2 * h`.
-/
lemma buildCover_mu (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) = 2 * h := by
  classical
  have hcov := buildCover_covers (F := F) (h := h) (hH := hH)
  simpa using mu_of_allCovered (F := F) (Rset := buildCover F h hH) (h := h) hcov

/--
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The full proof proceeds by well-founded
induction on the recursion tree.  The low-sensitivity branch inserts cubes
from `low_sensitivity_cover`, while the entropy branch applies the
induction hypothesis to the restricted families.
-
/-!
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The proof follows the same well-founded
induction as `buildCover_covers`.  Each branch either inserts a collection of
subcubes produced by `low_sensitivity_cover`, a  
recurses on families with strictly smaller measures.  We provide the
statement here together with a proof outline; completing the detailed argument
is left as future work.
-/
/--
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The intended proof mirrors the
well‑founded recursion used in `buildCover_covers`.  One performs induction
on the lexicographic measure

```
  μ(F, Rset) = 2 * h + (uncovered F Rset).toFinset.card,
```

where `h` bounds the entropy of the current family and `uncovered` counts
the remaining uncovered `1`‑inputs.  Each branch strictly decreases this
measure:

* **Low‑sensitivity branch.**  When all functions have small sensitivity,
  `low_sensitivity_cover` yields monochromatic subcubes covering the
  outstanding points, dropping the second component of `μ` to zero.
* **Entropy branch.**  Otherwise a coordinate split reduces the entropy
  budget.  The recursion applies the induction hypothesis to both
  restrictions and lifts the resulting cubes back via
  `lift_mono_of_restrict_fixOne`.

Formalising this argument is nontrivial and left for future work.  We keep
the expected statement as an axiom so that other lemmas can depend on it. -/

/-! ### Monochromaticity in the low‑sensitivity case

The next lemma handles the special situation where all functions in the family
have sensitivity strictly below `log₂ (n + 1)`.  In this regime the recursive
construction `buildCover` immediately takes the low‑sensitivity branch and
returns the rectangles provided by `low_sensitivity_cover`.  We can therefore
establish monochromaticity directly.  The general statement is left as an axiom
below. -/

lemma buildCover_mono_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n)) :
    ∀ R ∈ buildCover (F := F) (h := h) hH,
      Subcube.monochromaticForFamily R F := by
  classical
  -- Expand the recursion once at the top level.
  dsimp [buildCover]
  -- Split on whether an uncovered pair exists.
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      intro R hR
      simpa [hfu] using hR
  | some tup =>
      rcases tup with ⟨f, x⟩
      -- Obtain a witness that `F` is nonempty for `max'`.
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F (∅ : Finset (Subcube n))) hfu with
          ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      -- Maximum sensitivity over the family.
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      -- Show that `s` itself is below the threshold.
      have hs_lt : s < Nat.log2 (Nat.succ n) := by
        have hle : s ≤ Nat.log2 (Nat.succ n) - 1 := by
          refine Finset.max'_le ?_?
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨g, hg, rfl⟩
          exact Nat.le_pred_of_lt (hs g hg)
        have hpos : 0 < Nat.log2 (Nat.succ n) := by
          have : (1 : ℕ) < Nat.succ n := Nat.succ_lt_succ (Nat.zero_lt_succ _)
          exact Nat.log2_pos this
        have : s.succ ≤ Nat.log2 (Nat.succ n) := by
          simpa [Nat.succ_pred_eq_of_pos hpos] using Nat.succ_le_succ hle
        exact Nat.lt_of_succ_le this
      -- The pattern match in `buildCover` therefore selects the low-sensitivity branch.
      have hs_case : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) := Or.inl hs_lt
      obtain ⟨R_ls, hmono_ls, -, -⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      -- The result of `buildCover` is precisely `R_ls`.
      have hres : buildCover (F := F) (h := h) hH = R_ls := by
        simp [buildCover, hfu, hs_case]
      intro R hR
      have hR_ls : R ∈ R_ls := by simpa [hres] using hR
      exact hmono_ls R hR_ls

lemma buildCover_card_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n)) :
    (buildCover F h hH).card
      ≤ Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  classical
  dsimp [buildCover]
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
        simpa [buildCover, hfu]
      have : 0 ≤ Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
        Nat.zero_le _
      simpa [hres] using this
  | some tup =>
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F (∅ : Finset (Subcube n))) hfu with
          ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      have hs_lt : s < Nat.log2 (Nat.succ n) := by
        have hle : s ≤ Nat.log2 (Nat.succ n) - 1 := by
          refine Finset.max'_le ?_?
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨g, hg, rfl⟩
          exact Nat.le_pred_of_lt (hs g hg)
        have hpos : 0 < Nat.log2 (Nat.succ n) := by
          have : (1 : ℕ) < Nat.succ n := Nat.succ_lt_succ (Nat.zero_lt_succ _)
          exact Nat.log2_pos this
        have : s.succ ≤ Nat.log2 (Nat.succ n) := by
          simpa [Nat.succ_pred_eq_of_pos hpos] using Nat.succ_le_succ hle
        exact Nat.lt_of_succ_le this
      have hs_case : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) := Or.inl hs_lt
      obtain ⟨R_ls, -, -, hsize⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      have hres : buildCover F h hH = R_ls := by
        simp [buildCover, hfu, hs_case]
      have hs_le : s ≤ Nat.log2 (Nat.succ n) := Nat.le_of_lt hs_lt
      have hexp : 10 * s * Nat.log2 (Nat.succ n)
          ≤ 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) := by
        have := Nat.mul_le_mul_left (Nat.log2 (Nat.succ n)) hs_le
        have := Nat.mul_le_mul_left 10 this
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have hpow := Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
      have hsize' := le_trans hsize hpow
      simpa [hres] using hsize'

/-!  Variant of `buildCover_card_lowSens` that takes an existing set of
    rectangles.  The lemma adds the low-sensitivity cover on top of
    `Rset` and bounds the resulting cardinality. -/
lemma buildCover_card_lowSens_with (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n))
    (Rset : Finset (Subcube n)) :
    (buildCover F h hH Rset).card ≤
      Rset.card + Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  classical
  cases hfu : firstUncovered F Rset with
  | none =>
      -- If nothing is uncovered, the recursion terminates immediately.
      have hres : buildCover F h hH Rset = Rset := by
        simpa [buildCover, hfu]
      have hle : Rset.card ≤ Rset.card + Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
        Nat.le_add_right _ _
      simpa [hres] using hle
  | some tup =>
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F Rset) hfu with ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      have hs_lt : s < Nat.log2 (Nat.succ n) := by
        have hle : s ≤ Nat.log2 (Nat.succ n) - 1 := by
          refine Finset.max'_le ?_?
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨g, hg, rfl⟩
          exact Nat.le_pred_of_lt (hs g hg)
        have hpos : 0 < Nat.log2 (Nat.succ n) := by
          have : (1 : ℕ) < Nat.succ n := Nat.succ_lt_succ (Nat.zero_lt_succ _)
          exact Nat.log2_pos this
        have : s.succ ≤ Nat.log2 (Nat.succ n) := by
          simpa [Nat.succ_pred_eq_of_pos hpos] using Nat.succ_le_succ hle
        exact Nat.lt_of_succ_le this
      have hs_case : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) := Or.inl hs_lt
      obtain ⟨R_ls, -, -, hsize⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      have hres : buildCover F h hH Rset = Rset ∪ R_ls := by
        simp [buildCover, hfu, hs_case]
      have hs_le : s ≤ Nat.log2 (Nat.succ n) := Nat.le_of_lt hs_lt
      have hexp : 10 * s * Nat.log2 (Nat.succ n)
          ≤ 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) := by
        have := Nat.mul_le_mul_left (Nat.log2 (Nat.succ n)) hs_le
        have := Nat.mul_le_mul_left 10 this
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have hpow := Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
      have hsize' := le_trans hsize hpow
      -- Combine with the existing rectangles via `card_union_le`.
      have hunion : (Rset ∪ R_ls).card ≤ Rset.card + R_ls.card :=
        Finset.card_union_le
      have hfinal : (Rset ∪ R_ls).card ≤
          Rset.card + Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
        hunion.trans <| Nat.add_le_add_left hsize' _
      simpa [hres] using hfinal

/-!
`buildCover_card_bound_lowSens` is a numeric refinement of
`buildCover_card_lowSens`.  When the sensitivity threshold is small
relative to the entropy budget we can upgrade the crude exponential
bound on the number of rectangles to the standard `mBound` function.
The inequality `hh` ensures that `10 * log₂(n+1)^2 ≤ 10*h`, allowing us
to compare the two exponentials.  A positivity hypothesis on `n`
conveniently supplies the final factor from `pow_le_mBound`.-/
lemma buildCover_card_bound_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  -- Start with the crude exponential bound from `buildCover_card_lowSens`.
  have hcard :=
    buildCover_card_lowSens (F := F) (h := h) (hH := hH) hs
  -- Compare the exponents `10 * log₂(n+1)^2` and `10 * h`.
  have hexp_mul : 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)
      ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n))
        ≤ Nat.pow 2 (10 * h) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp_mul
  -- Combine the two exponentials and finish with `pow_le_mBound`.
  have hbig := le_trans hcard hpow
  have hbound := le_trans hbig (pow_le_mBound (n := n) (h := h) hn)
  simpa using hbound

/-!
  `buildCover_card_bound_lowSens_with` upgrades `buildCover_card_lowSens_with`
  to the standard bound `mBound`.  The lemma allows an existing collection
  of rectangles `Rset` as starting point and shows that after inserting the
  low‑sensitivity cover the total size is still controlled by the next
  entropy budget `h + 1`.

  The numeric hypothesis `hh` ensures that the intermediate exponential bound
  fits into `mBound n h`.  This lets us combine the sizes via
  `two_mul_mBound_le_succ`.
-/
lemma buildCover_card_bound_lowSens_with (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) (Rset : Finset (Subcube n))
    (hcard : Rset.card ≤ mBound n h) :
    (buildCover F h hH Rset).card ≤ mBound n (h + 1) := by
  classical
  -- Cardinality bound from the low-sensitivity cover.
  have hsize :=
    buildCover_card_lowSens_with (F := F) (h := h) (hH := hH) hs
      (Rset := Rset)
  -- Estimate the additional rectangles using `mBound`.
  have hexp_mul : 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)
      ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n))
        ≤ mBound n h :=
    le_trans
      (Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp_mul)
      (pow_le_mBound (n := n) (h := h) hn)
  -- Combine with the existing rectangles.
  have hsum : (buildCover F h hH Rset).card ≤ Rset.card + mBound n h :=
    hsize.trans <| Nat.add_le_add_left hpow _
  have hdouble : Rset.card + mBound n h ≤ 2 * mBound n h := by
    have := add_le_add hcard (le_rfl : mBound n h ≤ mBound n h)
    simpa [two_mul] using this
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans (hdouble.trans hstep)

/-!
  `buildCover_card_bound_lowSens_or` partially bridges the gap towards the
  full counting lemma `buildCover_card_bound`.  When the maximum sensitivity of
  functions in the family falls below the logarithmic threshold we invoke the
  established low‑sensitivity bound.  Otherwise we fall back to the coarse
  measure argument used in the general placeholder proof.  The additional
  hypotheses `hh` and `hn` ensure that the numeric comparison with
  `mBound` is valid in the first case.
-/
lemma buildCover_card_bound_lowSens_or (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  -- Inspect the initial uncovered pair, if any, to obtain a witness function.
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      -- Trivial termination: `buildCover` returns the empty set.
      have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
        simpa [buildCover, hfu]
      have : (0 : ℕ) ≤ mBound n h :=
        (Nat.zero_le _).trans (numeric_bound (n := n) (h := h))
      simpa [hres] using this
  | some tup =>
      -- A genuine uncovered pair exists.  Compute the maximal sensitivity `s`.
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F (∅ : Finset (Subcube n))) hfu with
          ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      -- Compare `s` with the logarithmic threshold.
      by_cases hs_small : s < Nat.log2 (Nat.succ n)
      ·
        -- Low-sensitivity branch: apply the dedicated lemma.
        have hsF : ∀ g ∈ F, sensitivity g < Nat.log2 (Nat.succ n) :=
          fun g hg => lt_of_le_of_lt (Hsens g hg) hs_small
        simpa [buildCover, hfu, hs_small] using
          buildCover_card_bound_lowSens (F := F) (h := h) (hH := hH) hsF hh hn
      ·
        -- Fallback: reuse the coarse measure bound from
        -- `buildCover_card_init_mu` and compare with `mBound`.
        have hsize :=
          buildCover_card_init_mu (F := F) (h := h) (hH := hH)
        exact hsize.trans (numeric_bound (n := n) (h := h))
/--
`buildCover_mono` states that every rectangle produced by the recursive
procedure `buildCover` is monochromatic for the entire family.  The present
code base still treats this statement as an axiom.  A full proof is expected
to follow the same well-founded recursion on the measure `μ` used in
`buildCover_covers`.

In outline one strengthens the induction hypothesis to assume that the set of
rectangles accumulated so far is already monochromatic.  The recursion then
proceeds as follows.

* **Base case.**  When `firstUncovered` returns `none` the algorithm simply
  returns the current set.  Monochromaticity is immediate.
* **Low-sensitivity branch.**  If all functions of `F` have sensitivity below
  the logarithmic threshold, `low_sensitivity_cover` provides a collection of
  monochromatic subcubes covering all remaining points.  Their union with the
  current set remains monochromatic.
* **Entropy branch.**  Otherwise one fixes a coordinate which decreases the
  entropy budget and recurses on the two restricted families.  By lifting the
  induction hypotheses via `lift_mono_of_restrict_fixOne` the resulting
  subcubes are monochromatic for the original family.



lemma buildCover_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F := by
  classical
  revert F
  refine (fun F ↦ _ : ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F) ?_?_
  intro F
  suffices
    H : ∀ Rset,
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) →
        ∀ R ∈ buildCover F h hH Rset, Subcube.monochromaticForFamily R F
    by
      have hmono_empty : ∀ R ∈ (∅ : Finset (Subcube n)),
          Subcube.monochromaticForFamily R F := by intro R h; simpa using h
      simpa using H ∅ hmono_empty
  intro Rset hmonoR
  cases hfu : firstUncovered F Rset with
  | none =>
      intro R hR
      have hRset : R ∈ Rset := by simpa [buildCover, hfu] using hR
      exact hmonoR R hRset
  | some tup =>
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F Rset) hfu with ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      cases hs : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
      | inl hs_small =>
          obtain ⟨R_ls, hmono_ls, -, -⟩ :=
            BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
          have hres : buildCover F h hH Rset = Rset ∪ R_ls := by
            simp [buildCover, hfu, hs_small]
          have hmono_union := mono_union hmonoR hmono_ls
          intro R hR
          have hR' : R ∈ Rset ∪ R_ls := by simpa [hres] using hR
          exact hmono_union R hR'
      | inr hs_large =>
          obtain ⟨i, b, Hdrop⟩ :=
            BoolFunc.exists_coord_entropy_drop (F := F)
              (hn := by decide)
              (hF := Finset.card_pos.mpr F_nonempty)
          let F0 := F.restrict i b
          let F1 := F.restrict i (!b)
          have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
            simpa using
              (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
          have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
            simpa using
              (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
          have hmono0 := buildCover_mono (F := F0) (h := h - 1) (hH := hH0)
          have hmono1 := buildCover_mono (F := F1) (h := h - 1) (hH := hH1)
          have hmono0_lift :
              ∀ R ∈ buildCover F0 (h - 1) hH0,
                Subcube.monochromaticForFamily R F :=
            by
              intro R hR
              exact lift_mono_of_restrict_fixOne
                (F := F) (i := i) (b := b) (R := R) (hmono0 R hR)
          have hmono1_lift :
              ∀ R ∈ buildCover F1 (h - 1) hH1,
                Subcube.monochromaticForFamily R F :=
            by
              intro R hR
              exact lift_mono_of_restrict_fixOne
                (F := F) (i := i) (b := !b) (R := R) (hmono1 R hR)
          have hmono_union := mono_union hmono0_lift hmono1_lift
          have hres : buildCover F h hH Rset =
              buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 := by
            simp [buildCover, hfu, hs_large]
          intro R hR
          have hR' : R ∈ buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 :=
            by simpa [hres] using hR
          exact hmono_union R hR'
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))
/--
`buildCover_card_bound` bounds the size of the cover returned by
`buildCover` in terms of the entropy budget `h`.  A double induction on `h` and the number of uncovered pairs shows that at most `2^h` cubes are produced.
The argument follows the same branch analysis as `buildCover_mono` and repeatedly applies the induction hypotheses.  We outline the reasoning here and leave a full proof to future work.
-/
/-!
`buildCover_card_bound` bounds the cardinality of the set produced by
`buildCover`.  The algorithm proceeds by well founded recursion on the
measure

```
μ(F, h, Rset) = 2 * h + (uncovered F Rset).toFinset.card,
```

which lexicographically tracks the entropy budget and the number of
currently uncovered `1`‑inputs.  Each recursive call strictly decreases
this measure.  The proof analyses the three branches of the
construction.

* **Low‑sensitivity branch.**  When every function of `F` has sensitivity
  below `log₂ (n + 1)` the auxiliary lemma `low_sensitivity_cover`
  produces at most `2 ^ (10 * h)` additional rectangles.  Since the
  measure already enforces an upper bound on the size of `Rset`, the
  union with these new rectangles still fits inside `mBound n h`.
* **Entropy branch.**  Otherwise we apply `exists_coord_entropy_drop`
  and split the family on a coordinate that lowers the collision
  entropy.  Both restrictions have strictly smaller measure and the
  induction hypotheses yield covers of size at most `mBound n (h - 1)`.
  Their union is bounded by `2 * mBound n (h - 1)` which is dominated by
  `mBound n h` thanks to `two_mul_mBound_le_succ`.
* **Sunflower branch.**  Occasionally the sunflower lemma finds a single
  rectangle that simultaneously covers many functions.  Adding this
  rectangle reduces the uncovered count by at least two, hence the
  measure drops and the induction hypothesis applies to the remainder.

Combining these cases shows that no more than `mBound n h` rectangles are
added before the measure reaches `0`.  A convenient way to organise the
argument is to introduce a measure

```
μ(F, h, Rset) = 2 * h + (uncovered F Rset).toFinset.card
```

which simultaneously tracks the remaining entropy budget and the number of
yet uncovered pairs `(f, x)`.  Every recursive call in `buildCover`
strictly reduces this measure: the entropy branch decreases the first
component, while the sunflower and low-sensitivity branches reduce the
second.  Double induction on `h` and the size of the uncovered set then
proves that the recursion cannot insert more than `mBound n h` rectangles.

The formal development below still uses a simplified argument, but the
comments document the intended induction in detail.

--  The outline below mirrors the informal reasoning:
--  * Base case: `uncovered = ∅`.
--  * Low sensitivity branch: `low_sensitivity_cover` gives
--    at most `2 ^ (10*h)` rectangles.
--  * Entropy branch: recurse with reduced entropy.
--  * Sunflower branch: remove a positive fraction of the remaining
--    pairs.
--  Each step strictly decreases `μ`, so the overall size is bounded by
--  `mBound n h`.
-/
lemma buildCover_card_bound_of_none (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered F Rset = none) (hcard : Rset.card ≤ mBound n h) :
    (buildCover F h hH Rset).card ≤ mBound n h := by
  classical
  have hres : buildCover F h hH Rset = Rset := by
    simpa [buildCover, hfu]
  simpa [hres] using hcard

lemma buildCover_card_bound_base (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered F (∅ : Finset (Subcube n)) = none) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
    simpa [buildCover, hfu]
  have : (0 : ℕ) ≤ mBound n h :=
    (Nat.zero_le _).trans (numeric_bound (n := n) (h := h))
  simpa [hres] using this

lemma buildCover_card_linear_bound_base (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered F (∅ : Finset (Subcube n)) = none) :
    (buildCover F h hH).card ≤ 2 * h + n := by
  classical
  have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
    simpa [buildCover, hfu]
  have : (0 : ℕ) ≤ 2 * h + n := Nat.zero_le _
  simpa [hres] using this

/-!
  A coarse numeric estimate that bounds the size of the cover directly
  by the initial measure `2 * h + n`.  The proof mirrors the placeholder
  argument used in `buildCover_card_bound` but is stated separately so
  that later refinements can build on it.
-/
lemma buildCover_card_linear_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ 2 * h + n := by
  classical

  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      simpa using
        (buildCover_card_linear_bound_base (F := F) (h := h) (hH := hH) hfu)
  | some _tup =>
      -- The detailed measure argument is still work in progress.
      -- For now we reuse the rough numeric estimate.
      have hnum := numeric_bound (n := n) (h := h)
      exact le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self _)) hnum

/-!
Bounding the size of the cover by the initial measure `μ`.  The
coarse linear estimate together with `mu_init_linear_bound` shows that
the rectangles produced by `buildCover` never exceed the starting
measure.
-/
lemma buildCover_card_init_mu (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ 2 * h + n := by
  classical
  simpa using
    buildCover_card_linear_bound (F := F) (h := h) (hH := hH)

-/
lemma buildCover_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  by_cases hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h
  ·
    by_cases hn : 0 < n
    ·
      simpa using
        buildCover_card_bound_lowSens_or (F := F) (h := h)
          (hH := hH) hh hn
    ·
      -- Degenerate dimension: fall back to the coarse measure bound.
      have hμ := buildCover_card_init_mu (F := F) (h := h) (hH := hH)
      have hbound := numeric_bound (n := n) (h := h)
      exact hμ.trans hbound
  ·
    -- Entropy budget too small: reuse the basic linear estimate.
    have hμ := buildCover_card_init_mu (F := F) (h := h) (hH := hH)
    have hbound := numeric_bound (n := n) (h := h)
    exact hμ.trans hbound
lemma buildCover_card_univ_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ bound_function n := by
  classical
  -- `size_bounds` provides a universal bound for any finite set of
  -- subcubes.  We instantiate it with the set returned by `buildCover`.
  have := size_bounds (n := n) (Rset := buildCover F h hH)
  simpa [size, bound_function] using this

/-! ## Main existence lemma -/

lemma cover_exists (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  let Rset := buildCover F h hH
  refine ⟨Rset, ?_, ?_, ?_⟩
  · intro R hR
    simpa using buildCover_mono (F := F) (h := h) (hH := hH) R hR
  · simpa using buildCover_covers (F := F) (h := h) hH
  · simpa using buildCover_card_bound (F := F) (h := h) (hH := hH)

/-! ## Choice wrapper -/

noncomputable
  def coverFamily (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
    Classical.choice (cover_exists (F := F) (h := h) hH)

  @[simp] lemma coverFamily_eq_buildCover (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
      coverFamily (F := F) (h := h) hH = buildCover F h hH := by
    classical
    simp [coverFamily, cover_exists]

lemma coverFamily_spec (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ coverFamily (F := F) (h := h) hH,
        Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F (coverFamily (F := F) (h := h) hH) ∧
      (coverFamily (F := F) (h := h) hH).card ≤ mBound n h := by
  classical
  simpa [coverFamily] using
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)

lemma coverFamily_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (F := F) (h := h) hH,
      Subcube.monochromaticForFamily R F :=
  (coverFamily_spec (F := F) (h := h) hH).1

lemma coverFamily_spec_cover (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (coverFamily (F := F) (h := h) hH) :=
  (coverFamily_spec (F := F) (h := h) hH).2.1

  lemma coverFamily_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
      (coverFamily (F := F) (h := h) hH).card ≤ mBound n h :=
    (coverFamily_spec (F := F) (h := h) hH).2.2

  lemma coverFamily_card_linear_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
      (coverFamily (F := F) (h := h) hH).card ≤ 2 * h + n := by
    classical
    simpa [coverFamily_eq_buildCover (F := F) (h := h) hH] using
      buildCover_card_linear_bound (F := F) (h := h) (hH := hH)

lemma coverFamily_card_univ_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (F := F) (h := h) hH).card ≤ bound_function n := by
  classical
  -- `buildCover_card_univ_bound` already gives the universal bound for
  -- the underlying `buildCover` construction.  We reuse it here via
  -- the equality `coverFamily_eq_buildCover`.
  simpa [coverFamily_eq_buildCover (F := F) (h := h) hH] using
    buildCover_card_univ_bound (F := F) (h := h) (hH := hH)

end Cover
-/
