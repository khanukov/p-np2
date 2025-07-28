import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.low_sensitivity_cover
import Pnp2.Boolcube
import Mathlib.Data.Nat.Basic

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Subcube)

namespace Cover2

/-!  This module will eventually replicate `cover.lean`.  For now we only
reintroduce the basic numeric definitions and state their properties as
axioms so that other files can depend on them without importing the heavy
original construction.  -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

axiom numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h
axiom numeric_bound_pos (n h : ℕ) (hn : 0 < n) : 2 * h + n ≤ mBound n h
axiom pow_le_mBound (n h : ℕ) (hn : 0 < n) : 2 ^ (10 * h) ≤ mBound n h
axiom pow_le_mBound_simple (n h : ℕ) (hn : 0 < n) : 2 ^ h ≤ mBound n h
axiom mBound_pos (n h : ℕ) (hn : 0 < n) : 0 < mBound n h
axiom two_le_mBound (n h : ℕ) (hn : 0 < n) : 2 ≤ mBound n h
axiom three_le_mBound (n h : ℕ) (hn : 0 < n) (hh : 1 ≤ h) : 3 ≤ mBound n h

@[simp] lemma mBound_zero (h : ℕ) : mBound 0 h = 0 := by simp [mBound]

lemma mBound_eq_zero_iff {n h : ℕ} : mBound n h = 0 ↔ n = 0 := by
  cases n with
  | zero =>
      simp [mBound_zero]
  | succ n =>
      have hpos : 0 < mBound (Nat.succ n) h :=
        mBound_pos (n := Nat.succ n) (h := h) (Nat.succ_pos _)
      have hneq : mBound (Nat.succ n) h ≠ 0 := ne_of_gt hpos
      constructor
      · intro hzero; exact False.elim (hneq hzero)
      · intro hfalse; cases hfalse
axiom mBound_mono {n : ℕ} : Monotone (mBound n)
axiom mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h
axiom mBound_le_succ (n h : ℕ) : mBound n h ≤ mBound n (h + 1)
axiom two_mul_mBound_le_succ (n h : ℕ) : 2 * mBound n h ≤ mBound n (h + 1)
axiom card_union_mBound_succ {n h : ℕ} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : R₁.card ≤ mBound n h) (h₂ : R₂.card ≤ mBound n h) :
    (R₁ ∪ R₂).card ≤ mBound n (h + 1)
axiom one_add_mBound_le_succ {n h : ℕ} (hn : 0 < n) :
    mBound n h + 1 ≤ mBound n (h + 1)
axiom card_union_singleton_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R}).card ≤ mBound n (h + 1)
axiom card_insert_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (insert R Rset).card ≤ mBound n (h + 1)
axiom card_union_pair_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R₁, R₂}).card ≤ mBound n (h + 1)
axiom card_union_triple_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ R₃ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) (hh : 1 ≤ h) :
    (Rset ∪ {R₁, R₂, R₃}).card ≤ mBound n (h + 1)

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

end Cover2

