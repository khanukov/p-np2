import Pnp.BoolFunc
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-! ### Collision probability and entropy -/

/-- *Collision probability* of a *uniform* family `F` of Boolean functions.
We work in `ℝ` so that later analytic lemmas can apply. -/
noncomputable
def collProb {n : ℕ} (F : Family n) : ℝ :=
  if F.card = 0 then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne']

@[simp] lemma collProb_zero {n : ℕ} {F : Family n} (h : F.card = 0) :
    collProb F = 0 := by
  simp [collProb, h]

lemma collProb_nonneg {n : ℕ} (F : Family n) :
    0 ≤ collProb F := by
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    simp [collProb, h, inv_nonneg.mpr (le_of_lt this)]

lemma collProb_le_one {n : ℕ} (F : Family n) :
    collProb F ≤ 1 := by
  classical
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have hpos : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hcoll : collProb F = 1 / (F.card : ℝ) := by
      simp [collProb, h]
    have hge : (1 : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    have hbound : 1 / (F.card : ℝ) ≤ 1 := by
      have := (div_le_one (hb := hpos)).mpr hge
      simpa using this
    simpa [hcoll] using hbound

@[simp] lemma collProb_card_one {n : ℕ} {F : Family n} (h : F.card = 1) :
    collProb F = 1 := by
  simp [collProb, h]

lemma collProb_ne_zero_of_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F ≠ 0 := by
  have : (F.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h)
  simpa [collProb, h] using inv_ne_zero this

/-- **Collision entropy** `H₂(F)` (base‑2). -/
noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

@[simp] lemma H₂_eq_log_card {n : ℕ} (F : Family n) :
    H₂ F = Real.logb 2 F.card := rfl

@[simp] lemma H₂_card_one {n : ℕ} (F : Family n) (h : F.card = 1) :
    H₂ F = 0 := by
  simp [H₂, h]

/-!
`Family.restrict i b` fixes one input bit of every function in `F`.
This can only decrease the cardinality of the family.
-/
lemma card_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    (F.restrict i b).card ≤ F.card := by
  classical
  simpa [Family.restrict] using
    (Finset.card_image_le (s := F) (f := fun f : BFunc n => f.restrictCoord i b))

/-- **Existence of a halving restriction (ℝ version)**.  There exists a
coordinate `i` and bit `b` such that restricting every function in the family to
`i = b` cuts its cardinality by at least half (real version). -/
-- TODO: port the analytic halving lemma from the original development.
axiom exists_restrict_half_real_aux {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2

/-- **Existence of a halving restriction.**  Casts the real-valued inequality
from `exists_restrict_half_real_aux` back to natural numbers. -/
lemma exists_restrict_half {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, (F.restrict i b).card ≤ F.card / 2 := by
  classical
  -- Obtain the real-valued inequality and cast back to natural numbers.
  obtain ⟨i, b, h_half_real⟩ :=
    exists_restrict_half_real_aux (F := F) (hn := hn) (hF := hF)
  -- Multiply the real inequality by `2` to avoid division and cast back to `ℕ`.
  have hmul_real :=
    (mul_le_mul_of_nonneg_left h_half_real (by positivity : (0 : ℝ) ≤ 2))
  have hmul_nat : (F.restrict i b).card * 2 ≤ F.card := by
    have h := hmul_real
    have h' : 2 * ((F.card : ℝ) / 2) = (F.card : ℝ) := by
      field_simp
    have h'' : 2 * ((F.restrict i b).card : ℝ) = ((F.restrict i b).card * 2 : ℝ) := by
      ring
    have hfinal : ((F.restrict i b).card * 2 : ℝ) ≤ (F.card : ℝ) := by
      simpa [h', h''] using h
    exact_mod_cast hfinal
  have hle_nat : (F.restrict i b).card ≤ F.card / 2 := by
    exact (Nat.le_div_iff_mul_le (by decide)).mpr hmul_nat
  exact ⟨i, b, hle_nat⟩

/-- **Existence of a halving restriction (ℝ version)** – deduced from the
integer statement. -/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  obtain ⟨i, b, hle⟩ := exists_restrict_half (F := F) (hn := hn) (hF := hF)
  have hle_real' : ((F.restrict i b).card : ℝ) ≤ ((F.card / 2 : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hle_cast_div : ((F.card / 2 : ℕ) : ℝ) ≤ (F.card : ℝ) / 2 := by
    simpa using (Nat.cast_div_le (m := F.card) (n := 2) :
      ((F.card / 2 : ℕ) : ℝ) ≤ (F.card : ℝ) / 2)
  have hle_real : ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 :=
    hle_real'.trans hle_cast_div
  exact ⟨i, b, hle_real⟩

/-- **Entropy‑Drop Lemma.**  There exists a coordinate whose restriction lowers
collision entropy by at least one bit. -/
axiom exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1

end BoolFunc
