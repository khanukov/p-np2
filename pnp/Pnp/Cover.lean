import Pnp.BoolFunc
import Pnp.Boolcube
import Pnp.Agreement
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset
open Agreement

namespace Cover

/-! ## Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) (hn : 0 < n) : 2 * h + n ≤ mBound n h := by
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  have hmain : (2 * h + n : ℕ) ≤ n * (h + 2) := by
    have h0 : 0 ≤ (h : ℤ) := by exact_mod_cast Nat.zero_le h
    nlinarith
  have : (2 * h + n : ℕ) ≤ n * (h + 2) * 2 ^ (10 * h) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Nat.mul_le_mul_left (n * (h + 2)) (Nat.succ_le_iff.mpr hmain)
  simpa [mBound] using this

/-! ## Auxiliary predicates -/

variable {n : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Point n) : Prop :=
  ∀ R ∈ Rset, ¬ x ∈ₛ R

/-- The set of all uncovered 1-inputs (together with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) : Set ((BFunc n) × Point n) :=
  {p | p.1 ∈ F ∧ p.1 p.2 = true ∧ NotCovered (Rset := Rset) p.2}

/-- Optionally returns the *first* uncovered ⟨f, x⟩. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) : Option ((BFunc n) × Point n) :=
  if h : (uncovered (F := F) (Rset := Rset)).Nonempty then
    some h.some
  else
    none

set_option linter.unusedSimpArgs false in
@[simp] lemma firstUncovered_none_iff (R : Finset (Subcube n)) :
    firstUncovered (F := F) R = none ↔ uncovered (F := F) R = ∅ := by
  classical
  by_cases h : (uncovered (F := F) (Rset := R)).Nonempty
  · simp [firstUncovered, h, Set.nonempty_iff_ne_empty]
  · simp [firstUncovered, h, Set.nonempty_iff_ne_empty]

end Cover
