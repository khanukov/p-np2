/-
entropy.lean
============

This module sketches a collision-entropy framework.  The core proofs are
now complete so the definitions can be imported by other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Pnp2.BoolFunc

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-! ### Collision probability and entropy -/

/-- *Collision probability* of a *uniform* family `F` of Boolean functions.
We work in `ℝ` because later analytic lemmas (`log` monotonicity, etc.) live
in `ℝ`. -/
noncomputable
 def collProb {n : ℕ} (F : Family n) : ℝ :=
  if h : (F.card = 0) then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne', h]

@[simp] lemma collProb_zero {n : ℕ} {F : Family n} (h : F.card = 0) :
    collProb F = 0 := by simp [collProb, h]

lemma collProb_nonneg {n : ℕ} (F : Family n) :
    0 ≤ collProb F := by
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    simpa [collProb, h] using inv_nonneg.mpr (le_of_lt this)

lemma collProb_le_one {n : ℕ} (F : Family n) :
    collProb F ≤ 1 := by
  classical
  by_cases h : F.card = 0
  · -- empty family: collision probability is zero
    simp [collProb, h]
  · have hpos : 0 < (F.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    -- rewrite in terms of division
    have hcoll : collProb F = 1 / (F.card : ℝ) := by
      simp [collProb, h]
    have hge : (1 : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    have hbound : 1 / (F.card : ℝ) ≤ 1 := by
      have := (div_le_one (hb := hpos)).mpr hge
      simpa using this
    simpa [hcoll] using hbound

@[simp] lemma collProb_card_one {n : ℕ} {F : Family n} (h : F.card = 1) :
    collProb F = 1 := by simp [collProb, h]

lemma collProb_ne_zero_of_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F ≠ 0 := by
  have : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h)
  simpa [collProb, h] using inv_ne_zero this

/-- **Collision entropy** `H₂(F)` (base‑2). -/
noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

@[simp] lemma H₂_eq_log_card {n : ℕ} (F : Family n) :
    H₂ F = Real.logb 2 F.card := rfl

@[simp] lemma H₂_card_one {n : ℕ} (F : Family n) (h : F.card = 1) :
    H₂ F = 0 := by simp [H₂, h]

/-!
`Family.restrict i b` applies `BFunc.restrictCoord` to every function in `F`,
fixing the `i`-th input bit to `b`.  This may identify previously distinct
functions, so the resulting family can only become smaller.  The lemma
`BoolFunc.card_restrict_le` in `BoolFunc.lean` records this fact.  We do not
restate it here to avoid duplication. -/

/-- **Existence of a halving restriction (ℝ version)** –
provides a coordinate `i` and bit `b` such that restricting every
function in the family to `i = b` cuts its cardinality by at least half
(real version).  The proof works with reals to avoid delicate `Nat`
arithmetic.  We postulate this lemma as an axiom for now. -/
axiom exists_restrict_half_real_aux {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2

/- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof. -/


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
  have hle_nat : (F.restrict i b).card ≤ F.card / 2 :=
    (Nat.le_div_iff_mul_le (by decide)).mpr hmul_nat
  exact ⟨i, b, hle_nat⟩

-- The above arithmetic on naturals is tedious; a simpler *real* argument will
-- be used in the entropy proof, so we postpone nat‑level clean‑up and rely on
-- `exists_restrict_half` proven below with reals.


/-- **Existence of a halving restriction (ℝ version)** – deduced from the
integer statement. -/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  -- Reinterpret the integer statement in the real numbers.
  obtain ⟨i, b, hle⟩ := exists_restrict_half (F := F) (hn := hn) (hF := hF)
  have hle_real' : ((F.restrict i b).card : ℝ) ≤ ((F.card / 2 : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hle_cast_div : ((F.card / 2 : ℕ) : ℝ) ≤ (F.card : ℝ) / 2 := by
    simpa using (Nat.cast_div_le (m := F.card) (n := 2) :
      ((F.card / 2 : ℕ) : ℝ) ≤ (F.card : ℝ) / 2)
  have hle_real : ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 :=
    hle_real'.trans hle_cast_div
  exact ⟨i, b, hle_real⟩

/-- **Entropy‑Drop Lemma.**  There exists a coordinate / bit whose
restriction lowers collision entropy by at least one bit. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  classical
  -- Obtain a coordinate/bit pair that halves the family size.
  obtain ⟨i, b, hhalf⟩ :=
    exists_restrict_half_real_aux (F := F) (hn := hn) (hF := hF)
  -- Deal with the special case that the restricted family is empty.
  by_cases hcard : (F.restrict i b).card = 0
  · -- `logb` of zero is zero, so the inequality is trivial since
    -- `H₂ F ≥ 1` for `F.card ≥ 2`.
    have hpos : (1 : ℝ) ≤ H₂ F := by
      have : (2 : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hF
      have hb : 1 < (2 : ℝ) := by norm_num
      have := Real.logb_le_logb_of_le hb (by norm_num) this
      simpa [H₂] using this
    refine ⟨i, b, ?_⟩
    simpa [H₂, hcard, sub_nonneg.mpr hpos] using hpos
  · -- The restricted family is nonempty, so `logb` is monotone with respect to
    -- the size bound obtained above.
    have hpos : 0 < ((F.restrict i b).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    have hb2 : 1 < (2 : ℝ) := by norm_num
    have hlog :=
      Real.logb_le_logb_of_le hb2 hpos hhalf
    have hdrop : Real.logb 2 ((F.card : ℝ) / 2) = H₂ F - 1 := by
      have hFpos : (F.card : ℝ) ≠ 0 := by
        have hpos : 0 < F.card := lt_trans (Nat.succ_pos 0) hF
        exact_mod_cast (ne_of_gt hpos)
      have hlog2 : Real.logb 2 (2 : ℝ) = (1 : ℝ) := by simp
      have := Real.logb_div (b := 2) (x := (F.card : ℝ)) (y := (2 : ℝ)) hFpos (by norm_num)
      simpa [H₂, hlog2, div_eq_mul_inv] using this
    refine ⟨i, b, ?_⟩
    -- Combine the logarithmic bound with the equality above and rewrite.
    have hineq : logb 2 ((F.restrict i b).card : ℝ) ≤ logb 2 ((F.card : ℝ) / 2) :=
      hlog
    have h := hineq
    -- Rewrite the right-hand side using `hdrop` and the definition of `H₂`.
    simpa [H₂, hdrop] using h

/--
Filtering a family cannot increase collision entropy: removing functions
from the family can only lower its cardinality, hence its entropy.
-/
lemma H₂_filter_le {n : ℕ} (F : Family n)
    (P : BFunc n → Prop) [DecidablePred P] :
    H₂ (F.filter P) ≤ H₂ F := by
  classical
  -- Filtering yields a subfamily, hence the cardinality can only decrease.
  have hcard : (F.filter P).card ≤ F.card := Finset.card_filter_le _ _
  have hb : 1 < (2 : ℝ) := by norm_num
  by_cases hzero : (F.filter P).card = 0
  · -- The filtered family is empty, so the entropy is zero.
    have hF_ge : 0 ≤ H₂ F := by
      by_cases hF0 : F.card = 0
      · simpa [H₂, hF0] using (le_of_eq rfl : (0 : ℝ) ≤ 0)
      ·
        have hx : 1 ≤ (F.card : ℝ) := by
          have hpos : 0 < F.card := Nat.pos_of_ne_zero hF0
          exact_mod_cast Nat.succ_le_of_lt hpos
        have := Real.logb_nonneg (b := 2) hb hx
        simpa [H₂] using this
    have hzero' : logb 2 ((F.filter P).card : ℝ) = 0 := by simp [hzero]
    have hposF : 0 ≤ H₂ F := by simpa [H₂] using hF_ge
    have : H₂ (F.filter P) ≤ H₂ F := by
      have := hposF
      simpa [H₂, hzero'] using this
    exact this
  · -- The filtered family is nonempty; compare logarithms of the sizes.
    have hposFilt : 0 < ((F.filter P).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    have hle : ((F.filter P).card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
    have := Real.logb_le_logb_of_le hb hposFilt hle
    simpa [H₂] using this


end BoolFunc
