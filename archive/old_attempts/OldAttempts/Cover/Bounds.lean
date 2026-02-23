import OldAttempts.Boolcube
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Classical
open Finset
open Boolcube (Point Subcube)

/-!
This module isolates the arithmetic bounds used in the cover construction.
Moving these numeric lemmas out of `cover2.lean` keeps the main file focused
on the combinatorial aspects.  The central quantity is `mBound`, an explicit
function controlling the size of intermediate rectangle sets.  The lemmas
below collect basic estimates and monotonicity properties which are heavily
used throughout the cover development.
-/

namespace Cover2

/--
`mBound n h` is a coarse upper bound on the number of rectangles generated
when covering a family of Boolean functions on `n` variables with entropy
budget `h`.  It intentionally grows very quickly; the factor `2^(10*h)` keeps
the arithmetic simple while still dominating all combinatorial overheads.
-/
@[simp] def mBound (n h : ℕ) : ℕ := n * 3 ^ n * (h + 2) * 2 ^ (10 * h)

/-- `mBound` is trivially nonnegative. -/
lemma mBound_nonneg (n h : ℕ) : 0 ≤ mBound n h := by
  exact Nat.zero_le _

/-- A linear upper bound showing that `mBound` dominates `2*h + n` when
`n` is positive.  The proof performs a case split on `h` and massages the
result using basic arithmetic reasoning. -/
lemma numeric_bound_core (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ n * (h + 2) * 2 ^ (10 * h) := by
  classical
  cases h with
  | zero =>
      have hmul := Nat.mul_le_mul_left n (show (1 : ℕ) ≤ 2 from by decide)
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using (show n ≤ n * (0 + 2) * 2 ^ (10 * 0) from
          by simpa using hmul)
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
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this

lemma numeric_bound (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h := by
  classical
  have hcore := numeric_bound_core (n := n) (h := h) hn
  have hmul : (2 * h + n) * 3 ^ n ≤
      (n * (h + 2) * 2 ^ (10 * h)) * 3 ^ n :=
    Nat.mul_le_mul_right _ hcore
  have hpos : 0 < 3 ^ n := pow_pos (by decide) _
  have hle : 2 * h + n ≤ (2 * h + n) * 3 ^ n :=
    Nat.le_mul_of_pos_right _ hpos
  have hbound : (n * (h + 2) * 2 ^ (10 * h)) * 3 ^ n = mBound n h := by
    simp [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  exact hle.trans (by simpa [hbound] using hmul)

/-- A convenience wrapper around `numeric_bound` for positive `n`. -/
lemma numeric_bound_pos (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h :=
  numeric_bound (n := n) (h := h) hn

/-- The exponential factor `2^(10*h)` is at most `mBound`. -/
lemma mBound_eq_mul (n h : ℕ) :
    mBound n h = (n * 3 ^ n * (h + 2)) * 2 ^ (10 * h) := by
  simp [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma pow_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ^ (10 * h) ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hpow3 : 1 ≤ 3 ^ n := by
    have hpos : 0 < 3 ^ n := pow_pos (by decide) _
    exact Nat.succ_le_of_lt hpos
  have hfac : 1 ≤ n * 3 ^ n := Nat.mul_le_mul hn1 hpow3
  have hh2 : 1 ≤ h + 2 := by
    have := Nat.zero_le (Nat.succ h)
    exact Nat.succ_le_succ this
  have htotal : 1 ≤ n * 3 ^ n * (h + 2) := Nat.mul_le_mul hfac hh2
  have := Nat.mul_le_mul_left (2 ^ (10 * h)) htotal
  simpa [mBound_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/--
Bounding `mBound` against the exponentially many candidate rectangles
constructed by `buildCover`.  Every recursive step inserts a subcube of the
form `Subcube.fromPoint x (supportUnion F)`, so there are at most `2^n`
distinct candidates.  The strengthened arithmetic guard shows that as soon as
the dimension is positive the catalogue bound `mBound n h` comfortably
dominates this count.
-/
lemma two_pow_le_mBound {n h : ℕ} (hn : 0 < n) :
    2 ^ n ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hpow23 : 2 ^ n ≤ 3 ^ n :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
  have hpow3 : 3 ≤ 3 ^ n := by
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
    have hbase : 1 ≤ 3 ^ k := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have := Nat.mul_le_mul_left 3 hbase
    simpa [hk, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hle : 3 ^ n ≤ n * 3 ^ n := by
    have := Nat.mul_le_mul_right (3 ^ n) hn1
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hh2 : 1 ≤ h + 2 := by
    have := Nat.zero_le (Nat.succ h)
    exact Nat.succ_le_succ this
  have hprod : n * 3 ^ n ≤ n * 3 ^ n * (h + 2) := by
    have := Nat.mul_le_mul_left (n * 3 ^ n) hh2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hfinal := Nat.mul_le_mul_left (n * 3 ^ n * (h + 2)) hpow
  have hmb := mBound_eq_mul (n := n) (h := h)
  have hthree : 3 ≤ n * 3 ^ n := hpow3.trans hle
  exact (hpow23.trans hle).trans
    ((hprod.trans (by simpa [hmb] using hfinal)))

/-- A simpler power bound obtained by weakening the exponent. -/
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

/-- `mBound` is positive whenever `n` is positive. -/
lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  have hpos₁ : 0 < 3 ^ n := pow_pos (by decide) _
  have hpos₂ : 0 < h + 2 := Nat.succ_pos _
  have hpos₃ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul₁ : 0 < n * 3 ^ n := Nat.mul_pos hn hpos₁
  have hmul₂ : 0 < n * 3 ^ n * (h + 2) := Nat.mul_pos hmul₁ hpos₂
  have := Nat.mul_pos hmul₂ hpos₃
  simpa [mBound_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- The bound always exceeds `2` once the dimension is positive. -/
lemma two_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ≤ mBound n h := by
  have hpow3 : 3 ≤ 3 ^ n := by
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
    have hbase : 1 ≤ 3 ^ k := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have := Nat.mul_le_mul_left 3 hbase
    simpa [hk, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hle : 3 ^ n ≤ n * 3 ^ n := by
    have := Nat.mul_le_mul_right (3 ^ n) hn1
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hthree : 3 ≤ n * 3 ^ n := hpow3.trans hle
  have hh2 : 2 ≤ h + 2 := by
    have := Nat.zero_le h
    exact Nat.succ_le_succ (Nat.succ_le_succ this)
  have hprod : 6 ≤ n * 3 ^ n * (h + 2) := by
    have := Nat.mul_le_mul hthree hh2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hmul := Nat.mul_le_mul_left (n * 3 ^ n * (h + 2)) hpow
  have hbound := mBound_eq_mul (n := n) (h := h)
  exact
    (Nat.le_trans (by decide : (2 : ℕ) ≤ 6) hprod).trans
      (by simpa [hbound] using hmul)

/-- `mBound` also dominates `3` for every positive dimension. -/
lemma three_le_mBound (n h : ℕ) (hn : 0 < n) :
    3 ≤ mBound n h := by
  have hpow3 : 3 ≤ 3 ^ n := by
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
    have hbase : 1 ≤ 3 ^ k := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have := Nat.mul_le_mul_left 3 hbase
    simpa [hk, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hle : 3 ^ n ≤ n * 3 ^ n := by
    have := Nat.mul_le_mul_right (3 ^ n) hn1
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hthree : 3 ≤ n * 3 ^ n := hpow3.trans hle
  have hh2 : 1 ≤ h + 2 := by
    have := Nat.zero_le (Nat.succ h)
    exact Nat.succ_le_succ this
  have hprod' := Nat.mul_le_mul hthree hh2
  have hprod : 3 ≤ n * 3 ^ n * (h + 2) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod'
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hmul := Nat.mul_le_mul_left (n * 3 ^ n * (h + 2)) hpow
  have hmul' : n * 3 ^ n * (h + 2) ≤
      n * 3 ^ n * (h + 2) * 2 ^ (10 * h) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have := Nat.le_trans hprod hmul'
  simpa [mBound_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/-- `mBound` vanishes when there are no variables. -/
@[simp] lemma mBound_zero (h : ℕ) : mBound 0 h = 0 := by
  simp [mBound]

/-- `mBound` collapses to zero iff the dimension vanishes. -/
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

/-- `mBound` grows monotonically in the entropy budget. -/
lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  have hfac : n * 3 ^ n * (h₁ + 2) ≤ n * 3 ^ n * (h₂ + 2) := by
    have := Nat.mul_le_mul_left (n * 3 ^ n) (Nat.add_le_add_right hh 2)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) this
  have := Nat.mul_le_mul hfac hpow
  simpa [mBound_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/-- Monotonicity in the dimension parameter. -/
lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  have hpow : 3 ^ n₁ ≤ 3 ^ n₂ :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (3 : ℕ)) hn
  have hdim := hn
  have hfac₁ : n₁ * 3 ^ n₁ ≤ n₂ * 3 ^ n₁ :=
    Nat.mul_le_mul_right (3 ^ n₁) hdim
  have hfac₂ : n₂ * 3 ^ n₁ ≤ n₂ * 3 ^ n₂ :=
    Nat.mul_le_mul_left n₂ hpow
  have hfac : n₁ * 3 ^ n₁ ≤ n₂ * 3 ^ n₂ := le_trans hfac₁ hfac₂
  have hh2 : (h + 2) ≤ (h + 2) := le_rfl
  have hprod : n₁ * 3 ^ n₁ * (h + 2) ≤ n₂ * 3 ^ n₂ * (h + 2) :=
    Nat.mul_le_mul hfac hh2
  have := Nat.mul_le_mul hprod (le_rfl : 2 ^ (10 * h) ≤ 2 ^ (10 * h))
  simpa [mBound_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

/-- Increasing the budget by one never decreases the bound. -/
lemma mBound_le_succ (n h : ℕ) : mBound n h ≤ mBound n (h + 1) :=
  mBound_mono (n := n) (Nat.le_succ h)

/-- Doubling the bound for budget `h` stays below the bound for `h + 1`. -/
lemma two_mul_mBound_le_succ (n h : ℕ) :
    2 * mBound n h ≤ mBound n (h + 1) := by
  have hcoeff : 2 * (h + 2) ≤ (h + 3) * 2 ^ 10 := by
    have hmono : h + 2 ≤ h + 3 := Nat.le_succ _
    have hpow : 2 ≤ 2 ^ 10 := by decide
    have := Nat.mul_le_mul hmono hpow
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  set base := n * 3 ^ n * 2 ^ (10 * h) with hbase
  have hcommon := Nat.mul_le_mul_left base hcoeff
  have hleft : base * (2 * (h + 2)) = 2 * mBound n h := by
    have hassoc : base * (2 * (h + 2)) = (base * 2) * (h + 2) := by
      simpa [Nat.mul_comm] using (Nat.mul_assoc base 2 (h + 2)).symm
    have hswap : (base * 2) * (h + 2) = (2 * base) * (h + 2) := by
      simp [Nat.mul_comm]
    have hassoc' : (2 * base) * (h + 2) = 2 * (base * (h + 2)) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    calc
      base * (2 * (h + 2)) = (base * 2) * (h + 2) := hassoc
      _ = (2 * base) * (h + 2) := hswap
      _ = 2 * (base * (h + 2)) := hassoc'
      _ = 2 * mBound n h := by
        simp [hbase, mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hright : base * ((h + 3) * 2 ^ 10) = mBound n (h + 1) := by
    have hten : 10 * (h + 1) = 10 * h + 10 := by ring
    calc
      base * ((h + 3) * 2 ^ 10)
          = n * 3 ^ n * 2 ^ (10 * h) * ((h + 3) * 2 ^ 10) := by
              simp [hbase, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = n * 3 ^ n * (h + 3) * (2 ^ (10 * h) * 2 ^ 10) := by
              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = n * 3 ^ n * (h + 3) * 2 ^ (10 * h + 10) := by
              simp [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = n * 3 ^ n * (h + 3) * 2 ^ (10 * (h + 1)) := by
              simp [hten, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = mBound n (h + 1) := by
              simp [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hleft' := hleft.symm
  have hright' := hright
  exact
    calc
      2 * mBound n h = base * (2 * (h + 2)) := hleft'
      _ ≤ base * ((h + 3) * 2 ^ 10) := hcommon
      _ = mBound n (h + 1) := hright'

/--
If two finite sets of rectangles each respect the current budget, then their
union respects the next budget.  This numeric helper underpins the recursive
construction of covers.
-/
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

/-- Adding one extra rectangle keeps us within the next budget. -/
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

/-- Convenient wrapper around `card_union_mBound_succ` for adding a singleton. -/
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

/-- Inserting an element into a set of rectangles grows the bound appropriately. -/
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

/-- A small helper: inserting two rectangles still fits into the next budget. -/
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

/-- And similarly for inserting three rectangles at once. -/
lemma card_union_triple_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ R₃ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R₁, R₂, R₃}).card ≤ mBound n (h + 1) := by
  classical
  let Rtriple : Finset (Subcube n) := {R₁, R₂, R₃}
  have htriple_le_three : Rtriple.card ≤ 3 := by
    have hcard_insert := Finset.card_insert_le (s := ({R₁, R₂} : Finset _))
        (a := R₃)
    have hpair_le_two : ({R₁, R₂} : Finset (Subcube n)).card ≤ 2 := by
      by_cases h : R₁ = R₂
      · subst h; simp
      · simp [h]
    have hbound := le_trans hcard_insert (Nat.add_le_add_right hpair_le_two 1)
    have hperm : ({R₃, R₁, R₂} : Finset (Subcube n)) = {R₁, R₂, R₃} := by
      ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_left_comm,
        or_comm]
    simpa [Rtriple, hperm] using hbound
  have htriple_bound : Rtriple.card ≤ mBound n h :=
    le_trans htriple_le_three (three_le_mBound (n := n) (h := h) hn)
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rtriple) hcard htriple_bound
  simpa [Rtriple, Finset.union_comm, Finset.union_assoc] using this

end Cover2

namespace Cover2

/-- The family of subcubes on `n` variables has cardinality `3^n`.  Each
subcube is described by choosing, for every coordinate, either `none`
(coordinate is free) or `some b` (coordinate fixed to `b`). -/
lemma card_subcube (n : ℕ) :
    Fintype.card (Boolcube.Subcube n) = 3 ^ n := by
  classical
  -- Equip `Subcube n` with the obvious equivalence to functions `Fin n → Option Bool`.
  let e : Boolcube.Subcube n ≃ (Fin n → Option Bool) :=
    { toFun := fun C => C.fix,
      invFun := fun f => ⟨f⟩,
      left_inv := by intro C; cases C; rfl,
      right_inv := by intro f; rfl }
  have hcard := Fintype.card_congr e
  have hpow : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
    classical
    have hcard_fun :=
        Fintype.card_fun (α := Fin n) (β := Option Bool)
    have hnum : (Fintype.card (Option Bool)) ^ Fintype.card (Fin n) = 3 ^ n := by
      simp [Fintype.card_fin, Fintype.card_option]
    exact hcard_fun.trans hnum
  exact hcard.trans hpow

/--
A coarse arithmetic bound showing that the total number of subcubes is
dominated by `mBound` once the entropy budget `h` grows linearly with the
dimension.  The factor `5` is deliberately slack to keep the argument simple.

This lemma is intentionally weak: the assumption `n ≤ 5 * h` is only used to
compare the exponents `2 * n` and `10 * h`.  In the cover construction it is
invoked exclusively under this hypothesis, so we make no attempt to optimise
the constant.
-/
lemma card_subcube_le_mBound {n h : ℕ}
    (hn : 0 < n) :
    Fintype.card (Boolcube.Subcube n) ≤ mBound n h := by
  classical
  have hcard := card_subcube (n := n)
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hle₁ : 3 ^ n ≤ n * 3 ^ n := by
    have := Nat.mul_le_mul_right (3 ^ n) hn1
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hle₂ : n * 3 ^ n ≤ n * 3 ^ n * (h + 2) := by
    have hh2 : 1 ≤ h + 2 := by
      have := Nat.zero_le (Nat.succ h)
      exact Nat.succ_le_succ this
    have := Nat.mul_le_mul_left (n * 3 ^ n) hh2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hmul := Nat.mul_le_mul_left (n * 3 ^ n * (h + 2)) hpow
  have hmul'' : n * 3 ^ n * (h + 2) ≤ n * 3 ^ n * (h + 2) * 2 ^ (10 * h) := by
    have := hmul
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have htotal : 3 ^ n ≤ mBound n h := by
    have hchain := hle₁.trans (hle₂.trans hmul'')
    simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hchain
  simpa [hcard] using htotal

end Cover2

