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

axiom numeric_bound (n h : ℕ) (hn : 0 < n) : 2 * h + n ≤ mBound n h

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
def firstUncovered (_F : Family n) (_Rset : Finset (Subcube n)) : Option ((BFunc n) × Point n) :=
  none

end Cover
