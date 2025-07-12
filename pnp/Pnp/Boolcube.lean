import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Pnp.BoolFunc

open BoolFunc

namespace Boolcube

-- Basic objects: points, subcubes and Boolean functions.

variable {n : ℕ}

abbrev Point (n : ℕ) := Fin n → Bool

structure Subcube (n : ℕ) where
  fix : Fin n → Option Bool -- none ⇒ "coordinate is free"

namespace Subcube

@[simp] def support (C : Subcube n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (C.fix i).isSome

/-- point `x` lies in `C` iff it matches all fixed coordinates. -/
@[simp] def Mem (C : Subcube n) (x : Point n) : Prop :=
  ∀ i, (C.fix i).elim True fun b ↦ x i = b

@[simp] def dim (C : Subcube n) : ℕ := n - C.support.card

@[simp] def full : Subcube n := ⟨fun _ ↦ none⟩
@[simp] def point (x : Point n) : Subcube n := ⟨fun i ↦ some (x i)⟩

@[simp] lemma mem_full (x : Point n) : (full : Subcube n).Mem x := by
  intro; simp [full]

@[simp] lemma mem_point_iff (x y : Point n) : (point x).Mem y ↔ x = y := by
  constructor
  · intro h; funext i; have hi := h i; simpa [point] using hi.symm
  · intro h i; simp [h, point]

/-- Fix exactly one coordinate. -/
@[simp] def fixOne (i : Fin n) (b : Bool) : Subcube n :=
  ⟨fun j ↦ if j = i then some b else none⟩

@[simp] lemma mem_fixOne_iff {i b x} :
    (fixOne (n := n) i b).Mem x ↔ x i = b := by
  constructor
  · intro h; simpa using h i
  · intro h j; by_cases hj : j = i
    · cases hj; simp [fixOne, h]
    · simp [fixOne, hj]

@[simp] lemma dim_full (n : ℕ) :
    (Subcube.full : Subcube n).dim = n := by
  classical
  simp [Subcube.dim, Subcube.support]

@[simp] lemma dim_point (x : Point n) :
    (Subcube.point (n := n) x).dim = 0 := by
  classical
  simp [Subcube.dim, Subcube.support]


end Subcube

abbrev BoolFun (n : ℕ) := Point n → Bool
abbrev Family  (n : ℕ) := Finset (BoolFun n)

namespace Entropy

/-- Collision entropy (uniform measure) – we keep only the logarithmic form. -/
@[simp] noncomputable def H₂ {n} (F : Family n) : ℝ := Real.logb 2 (F.card)

lemma H₂_nonneg {F : Family n} : 0 ≤ H₂ F := by
  classical
  unfold H₂
  by_cases hF : F.card = 0
  · -- `logb` of zero is zero by definition
    simp [hF]
  ·
    have hb : (1 : ℝ) < 2 := by norm_num
    have hx : 1 ≤ (F.card : ℝ) := by
      have hpos : 0 < F.card := Nat.pos_of_ne_zero hF
      exact_mod_cast Nat.succ_le_of_lt hpos
    have := Real.logb_nonneg (b := 2) hb hx
    simpa using this

end Entropy

end Boolcube

