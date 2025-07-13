import Pnp.BoolFunc
import Pnp.Boolcube
import Pnp.Agreement
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

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

/-! ## Auxiliary predicates -/

variable {n : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Vector Bool n) : Prop :=
  ∀ R ∈ Rset, x ∉ₛ R

/-- The set of all uncovered 1-inputs (together with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) : Set (Σ f : BoolFunc n, Vector Bool n) :=
  {⟨f, x⟩ | f ∈ F ∧ f x = true ∧ NotCovered (Rset := Rset) x}

/-- Optionally returns the *first* uncovered ⟨f, x⟩. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) : Option (Σ f : BoolFunc n, Vector Bool n) :=
  (uncovered (F := F) Rset).choose?  -- `choose?` from Mathlib (classical choice on sets)

@[simp]
lemma firstUncovered_none_iff (R : Finset (Subcube n)) :
    firstUncovered (F := F) R = none ↔ uncovered (F := F) R = ∅ := by
  classical
  simp [firstUncovered, Set.choose?_eq_none]

end Cover
