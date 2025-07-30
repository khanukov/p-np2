import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.low_sensitivity_cover
import Pnp2.Boolcube
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

-- Local notation for membership in a subcube of the Boolean cube.
notation x " ∈ₛ " R => Boolcube.Subcube.Mem R x

namespace Cover2

/-!  This module will eventually replicate `cover.lean`.  For now we only
reintroduce the basic numeric definitions and state their properties as
axioms so that other files can depend on them without importing the heavy
original construction.  -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) (hn : 0 < n) :
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

lemma numeric_bound_pos (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h :=
  numeric_bound (n := n) (h := h) hn
lemma pow_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ^ (10 * h) ≤ mBound n h := by
  have hpos : 0 < n * (h + 2) := by
    have hpos' : 0 < h + 2 := Nat.succ_pos _
    exact Nat.mul_pos hn hpos'
  have hfactor : 1 ≤ n * (h + 2) := Nat.succ_le_of_lt hpos
  have := Nat.mul_le_mul_left (2 ^ (10 * h)) hfactor
  simpa [mBound, one_mul] using this
lemma pow_le_mBound_simple (n h : ℕ) (hn : 0 < n) :
    2 ^ h ≤ mBound n h := by
  -- The exponent `10 * h` dominates `h`, so `2 ^ h ≤ 2 ^ (10 * h)`.
  have hexp : h ≤ 10 * h := by
    have hbase : (1 : ℕ) ≤ 10 := by decide
    have := Nat.mul_le_mul_left h hbase
    simpa [Nat.mul_comm] using this
  have hpow : 2 ^ h ≤ 2 ^ (10 * h) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hexp
  -- Combine with the main bound on the power factor.
  exact hpow.trans (pow_le_mBound (n := n) (h := h) hn)

lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  -- Each factor in the definition is positive.
  have hpos₁ : 0 < h + 2 := Nat.succ_pos _
  have hpos₂ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul : 0 < n * (h + 2) := Nat.mul_pos hn hpos₁
  have := Nat.mul_pos hmul hpos₂
  simpa [mBound] using this

lemma two_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hh2 : 2 ≤ h + 2 := by
    have := Nat.zero_le h
    exact Nat.succ_le_succ (Nat.succ_le_succ this)
  have hfactor : 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul hn1 hh2
    simpa [one_mul] using this
  have hpow : 1 ≤ 2 ^ (10 * h) :=
    Nat.succ_le_of_lt (pow_pos (by decide) _)
  have := Nat.mul_le_mul hfactor hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

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
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have := Nat.mul_le_mul hfac hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

@[simp] lemma mBound_zero (h : ℕ) : mBound 0 h = 0 := by simp [mBound]

lemma mBound_eq_zero_iff {n h : ℕ} : mBound n h = 0 ↔ n = 0 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have hpos : 0 < mBound (Nat.succ n) h :=
        mBound_pos (n := Nat.succ n) (h := h) (Nat.succ_pos _)
      have hneq : mBound (Nat.succ n) h ≠ 0 := ne_of_gt hpos
      constructor
      · intro hzero; exact False.elim (hneq hzero)
      · intro hfalse; cases hfalse
lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  dsimp [mBound]
  have hfac : n * (h₁ + 2) ≤ n * (h₂ + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 2)
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) this
  exact Nat.mul_le_mul hfac hpow

lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  dsimp [mBound]
  have hfac : n₁ * (h + 2) ≤ n₂ * (h + 2) :=
    Nat.mul_le_mul_right (h + 2) hn
  exact Nat.mul_le_mul hfac (le_rfl)

lemma mBound_le_succ (n h : ℕ) : mBound n h ≤ mBound n (h + 1) :=
  mBound_mono (n := n) (Nat.le_succ h)
lemma two_mul_mBound_le_succ (n h : ℕ) :
    2 * mBound n h ≤ mBound n (h + 1) := by
  -- We compare the factors of `mBound` for budgets `h` and `h + 1`.
  -- The linear factor grows monotonically with `h`.
  have hfac : h + 2 ≤ h + 3 := Nat.le_succ (h + 2)
  -- The exponential term grows by a factor of at least `2 ^ 9`.
  have hexp : 10 * h + 1 ≤ 10 * h + 10 := by
    -- `1 ≤ 10` lets us shift by `10 * h` on both sides.
    have h1 : (1 : ℕ) ≤ 10 := by decide
    exact add_le_add_left h1 (10 * h)
  -- Use monotonicity of exponentiation with a positive base.
  have hpow : 2 ^ (10 * h + 1) ≤ 2 ^ (10 * h + 10) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  -- Combine growth of both factors.
  have hmul := Nat.mul_le_mul hfac hpow
  -- Multiply by the common dimension factor.
  have hmain := Nat.mul_le_mul_left n hmul
  -- Rewrite both sides into the desired `mBound` form.
  have lhs_eq : n * ((h + 2) * 2 ^ (10 * h + 1)) = 2 * mBound n h := by
    simp [mBound, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have rhs_eq : n * ((h + 3) * 2 ^ (10 * h + 10)) = mBound n (h + 1) := by
    have : 10 * (h + 1) = 10 * h + 10 := by ring
    simp [mBound, pow_add, this, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simpa [lhs_eq, rhs_eq] using hmain
lemma card_union_mBound_succ {n h : ℕ} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : R₁.card ≤ mBound n h) (h₂ : R₂.card ≤ mBound n h) :
    (R₁ ∪ R₂).card ≤ mBound n (h + 1) := by
  classical
  have hsum : (R₁ ∪ R₂).card ≤ R₁.card + R₂.card := by
    simpa using (Finset.card_union_le (s := R₁) (t := R₂))
  have hdouble : R₁.card + R₂.card ≤ 2 * mBound n h := by
    have := add_le_add h₁ h₂
    simpa [two_mul] using this
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans <| hdouble.trans hstep

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

lemma card_union_singleton_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R}).card ≤ mBound n (h + 1) := by
  classical
  have hsum : (Rset ∪ {R}).card ≤ Rset.card + 1 := by
    simpa using (Finset.card_union_le (s := Rset) (t := ({R} : Finset (Subcube n))) )
  have hbound : Rset.card + 1 ≤ mBound n h + 1 :=
    Nat.add_le_add_right hcard 1
  have hstep := one_add_mBound_le_succ (n := n) (h := h) hn
  exact hsum.trans <| hbound.trans hstep

lemma card_insert_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (insert R Rset).card ≤ mBound n (h + 1) := by
  classical
  have hunion : insert R Rset = Rset ∪ {R} := by
    ext x; by_cases hx : x = R <;> by_cases hxset : x ∈ Rset <;>
      simp [hx, hxset, Finset.mem_insert, Finset.mem_union]
  simpa [hunion] using
    (card_union_singleton_mBound_succ (n := n) (h := h)
      (Rset := Rset) (R := R) hcard hn)

lemma card_union_pair_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R₁, R₂}).card ≤ mBound n (h + 1) := by
  classical
  let Rpair : Finset (Subcube n) := {R₁, R₂}
  have hpair_le_two : Rpair.card ≤ 2 := by
    by_cases h : R₁ = R₂
    · subst h; simp [Rpair]
    · simp [Rpair, h]
  have hpair_bound : Rpair.card ≤ mBound n h :=
    le_trans hpair_le_two (two_le_mBound (n := n) (h := h) hn)
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rpair) hcard hpair_bound
  simpa [Rpair, Finset.union_comm, Finset.union_assoc] using this

lemma card_union_triple_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ R₃ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) (hh : 1 ≤ h) :
    (Rset ∪ {R₁, R₂, R₃}).card ≤ mBound n (h + 1) := by
  classical
  let Rtriple : Finset (Subcube n) := {R₁, R₂, R₃}
  have htriple_le_three : Rtriple.card ≤ 3 := by
    have hcard_insert := Finset.card_insert_le (s := {R₁, R₂}) (a := R₃)
    have hpair_le_two : ({R₁, R₂} : Finset (Subcube n)).card ≤ 2 := by
      by_cases h : R₁ = R₂
      · subst h; simp
      · simp [h]
    have h := le_trans hcard_insert (Nat.add_le_add_right hpair_le_two 1)
    have hrepr : insert R₃ ({R₁, R₂} : Finset (Subcube n)) = {R₁, R₂, R₃} := by
      ext x; by_cases hx : x = R₃ <;> by_cases hx1 : x = R₁ <;> by_cases hx2 : x = R₂ <;>
        simp [hx, hx1, hx2, Finset.mem_insert, Finset.mem_singleton, or_comm]
    simpa [Rtriple, hrepr] using h
  have htriple_bound : Rtriple.card ≤ mBound n h :=
    le_trans htriple_le_three (three_le_mBound (n := n) (h := h) hn hh)
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rtriple) hcard htriple_bound
  simpa [Rtriple, Finset.union_comm, Finset.union_assoc] using this

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

/-! ## Auxiliary predicates -/

variable {n h : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Point n) : Prop :=
  ∀ R ∈ Rset, ¬ x ∈ₛ R

@[simp] lemma notCovered_empty (x : Point n) :
    NotCovered (n := n) (Rset := (∅ : Finset (Subcube n))) x := by
  intro R hR
  -- `hR` is impossible since the set is empty
  cases hR

lemma NotCovered.monotone {R₁ R₂ : Finset (Subcube n)} (hsub : R₁ ⊆ R₂)
    {x : Point n} (hx : NotCovered (n := n) (Rset := R₂) x) :
    NotCovered (n := n) (Rset := R₁) x := by
  intro R hR
  exact hx R (hsub hR)

/-! ### Uncovered points and search utilities -/

/-- The set of all uncovered `1`-inputs (paired with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) :
    Set (Σ f : BFunc n, Point n) :=
  {p | p.1 ∈ F ∧ p.1 p.2 = true ∧ NotCovered (n := n) (Rset := Rset) p.2}

/-- Optionally return the *first* uncovered pair. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) :
    Option (Σ f : BFunc n, Point n) :=
  if h : (uncovered (n := n) F Rset).Nonempty then
    some h.choose
  else
    none

lemma firstUncovered_none_iff {F : Family n} {Rset : Finset (Subcube n)} :
    firstUncovered (n := n) F Rset = none ↔
      uncovered (n := n) F Rset = (∅ : Set (Σ f : BFunc n, Point n)) := by
  classical
  by_cases h : (uncovered (n := n) F Rset).Nonempty
  ·
    have hne : uncovered (n := n) F Rset ≠ (∅ : Set (Σ f : BFunc n, Point n)) :=
      Set.nonempty_iff_ne_empty.mp h
    simp [firstUncovered, h, hne]
  ·
    have hempty : uncovered (n := n) F Rset =
        (∅ : Set (Σ f : BFunc n, Point n)) :=
      Set.not_nonempty_iff_eq_empty.mp h
    simp [firstUncovered, h, hempty]


/-- All `1`-inputs of `F` lie in some rectangle of `Rset`. -/
@[simp]
def AllOnesCovered (F : Family n) (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

lemma AllOnesCovered.full (F : Family n) :
    AllOnesCovered (n := n) F ({Subcube.full} : Finset (Subcube n)) := by
  intro f hf x hx
  refine ⟨Subcube.full, by simp, ?_⟩
  simp

lemma AllOnesCovered.superset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered (n := n) F R₁) (hsub : R₁ ⊆ R₂) :
    AllOnesCovered (n := n) F R₂ := by
  intro f hf x hx
  rcases h₁ f hf x hx with ⟨R, hR, hxR⟩
  exact ⟨R, hsub hR, hxR⟩

lemma AllOnesCovered.union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered (n := n) F R₁) (h₂ : AllOnesCovered (n := n) F R₂) :
    AllOnesCovered (n := n) F (R₁ ∪ R₂) := by
  intro f hf x hx
  by_cases hx1 : ∃ R ∈ R₁, x ∈ₛ R
  · rcases hx1 with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union] using Or.inl hR, hxR⟩
  · rcases h₂ f hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union, hx1] using Or.inr hR, hxR⟩

lemma AllOnesCovered.insert {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} (hcov : AllOnesCovered (n := n) F Rset) :
    AllOnesCovered (n := n) F (Insert.insert R Rset) := by
  classical
  have hsub : Rset ⊆ Insert.insert R Rset := by
    intro S hS; exact Finset.mem_insert.mpr (Or.inr hS)
  exact AllOnesCovered.superset (F := F) (R₁ := Rset)
    (R₂ := Insert.insert R Rset) hcov hsub

lemma uncovered_eq_empty_of_allCovered {F : Family n}
    {Rset : Finset (Subcube n)}
    (hcov : AllOnesCovered (n := n) F Rset) :
    uncovered (n := n) F Rset = (∅ : Set (Σ f : BFunc n, Point n)) := by
  classical
  ext p; constructor
  · intro hp
    have hf : p.1 ∈ F := hp.1
    have hx : p.1 p.2 = true := hp.2.1
    have hnc : NotCovered (n := n) (Rset := Rset) p.2 := hp.2.2
    rcases hcov p.1 hf p.2 hx with ⟨R, hR, hxR⟩
    have : ¬ Boolcube.Subcube.Mem R p.2 := hnc R hR
    exact False.elim (this hxR)
  · intro hp
    cases hp

/-!
`uncovered` is monotone with respect to the set of rectangles.  Adding a new
rectangle can only remove uncovered pairs.  The next lemmas capture this
simple observation and will be useful when reasoning about termination
measures.-/

lemma uncovered_subset_of_union_singleton {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n} :
    uncovered (n := n) F (Rset ∪ {R}) ⊆ uncovered (n := n) F Rset := by
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

lemma uncovered_subset_of_union {F : Family n}
    {R₁ R₂ : Finset (Subcube n)} :
    uncovered (n := n) F (R₁ ∪ R₂) ⊆ uncovered (n := n) F R₁ := by
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

/-! ### Simple termination measure

`mu` tracks the remaining entropy budget together with the number of
currently uncovered pairs.  The measure is used in the original
construction to show that each recursive step makes progress.  We only
record a minimal API for now. -/

noncomputable def mu (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) : ℕ :=
  2 * h + (uncovered (n := n) F Rset).toFinset.card

lemma mu_union_singleton_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ} :
    mu (n := n) F h (Rset ∪ {R}) ≤ mu (n := n) F h Rset := by
  classical
  -- Adding a rectangle can only reduce the uncovered set.
  have hsub : uncovered (n := n) F (Rset ∪ {R}) ⊆
      uncovered (n := n) F Rset :=
    uncovered_subset_of_union_singleton
      (F := F) (Rset := Rset) (R := R)
  -- Convert the set inclusion into a finset inclusion on cardinals.
  have hsubF : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
        (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset := hsub hx'
    simpa using hx''
  -- Cardinalities respect inclusion.
  have hcard := Finset.card_le_card hsubF
  -- Add the entropy contribution to both sides.
  have := add_le_add_left hcard (2 * h)
  simpa [mu] using this

/-!
Adding a rectangle that covers at least one previously uncovered pair strictly
decreases the measure `μ`.  This lemma will be useful when reasoning about
progress of the cover construction.
-/
lemma mu_union_singleton_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  rcases hx with ⟨p, hpU, hpR⟩
  have hp_not : p ∉ uncovered (n := n) F (Rset ∪ {R}) := by
    rcases hpU with ⟨hf, hx, hnc⟩
    intro hp'
    rcases hp' with ⟨hf', hx', hnc'⟩
    have := hnc' R (by simp) hpR
    exact this
  have hsub : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
      (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton
        (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hproper : ¬((uncovered (n := n) F Rset).toFinset ⊆
        (uncovered (n := n) F (Rset ∪ {R})).toFinset) := by
    intro hsubset
    have hpFin : p ∈ (uncovered (n := n) F Rset).toFinset := by simpa using hpU
    have := hsubset hpFin
    exact hp_not (by simpa using this)
  have hcard := Finset.card_lt_card ⟨hsub, hproper⟩
  have := Nat.add_lt_add_left hcard (2 * h)
  simpa [mu] using this

/-!  A convenient corollary of `mu_union_singleton_lt`: if at least one new
pair becomes covered, the measure decreases by one.  This quantified version is
occasionally handy for numeric estimates. -/
lemma mu_union_singleton_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) + 1 ≤ mu (n := n) F h Rset := by
  classical
  have hlt :=
    mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx
  exact Nat.succ_le_of_lt hlt

end Cover2

