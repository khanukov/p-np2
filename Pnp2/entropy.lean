/-
entropy.lean
============

This module sketches a collision-entropy framework.  Some of the proofs
are still incomplete (`sorry`), but the definitions can be imported by
other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
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
      have := (div_le_iff hpos).mpr hge
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
`Family.restrict i b` applies `BFunc.restrictCoord` to every function in `F`, fixing the `i`-th input bit to `b`.  This may identify previously distinct functions, so the resulting family can have smaller cardinality.  The next two helper lemmas are straightforward bookkeeping about these cardinalities and need no additional imports.
-/

lemma card_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    (F.restrict i b).card ≤ F.card := by
  classical
  -- `restrict` uses `Finset.image`, hence the size can only shrink.
  simpa [Family.restrict] using
    (Finset.card_image_le (f := fun f : BFunc n => fun x => f (Point.update x i b)) F)

lemma exists_restrict_half {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, (F.restrict i b).card ≤ F.card / 2 := by
  -- Proof omitted.
  classical
  sorry

-- The above arithmetic on naturals is tedious; a simpler *real* argument will
-- be used in the entropy proof, so we postpone nat‑level clean‑up and rely on
-- `exists_restrict_half` proven below with reals.

/-- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof.
-/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  -- We prove the contrapositive: if **no** coordinate yields a half-size
  -- restriction, then we derive a contradiction. Assume every coordinate `i` and
  -- bit `b` gives a restriction larger than half of `F`.
  by_contra H
  push_neg at H  -- Now `H` says: ∀ i b, (F.restrict i b).card > F.card / 2.
  -- Fix an arbitrary coordinate `j` and inject `F` into pairs of restrictions
  -- along `j`.
  have j : Fin n := ⟨0, by simpa using hn⟩
  have inj : F.card ≤ (F.restrict j false).card * (F.restrict j true).card,
  { -- mapping `f` ↦ (f|j=false, f|j=true)` is injective
    classical
    apply Finset.card_image_le
    refine ⟨fun f : BFunc n => (f.restrictCoord j false, f.restrictCoord j true), ?_⟩
    intro f₁ f₂ hfne hpair
    rcases hpair with ⟨h0, h1⟩
    have : ∀ x : Point n, f₁ x = f₂ x := by
      intro x
      by_cases hx : x j = false
      · -- compare via restrictCoord_agrees
        have := congrArg (fun g => g x) h0
        simpa [BoolFunc.restrictCoord, hx] using this
      · have := congrArg (fun g => g x) h1
        have : x j = true := by cases x j <;> tauto
        simpa [BoolFunc.restrictCoord, hx, this] using this
    exact hfne (funext this) },
  -- Apply base-2 logarithms to this inequality
  have log_ineq :
      Real.logb 2 (F.card) ≤
        Real.logb 2 ((F.restrict j false).card) +
          Real.logb 2 ((F.restrict j true).card) := by
    have := Real.logb_mul (by norm_num : (2 : ℝ) ≠ 1) (by positivity) (by positivity)
    simpa using congrArg (Real.logb 2) inj,
  -- From `H`, each log term on the RHS is > log₂(F.card/2) = log₂ F.card - 1.
  have half_log :
      Real.logb 2 ((F.restrict j false).card) > Real.logb 2 F.card - 1 ∧
        Real.logb 2 ((F.restrict j true).card) > Real.logb 2 F.card - 1,
  { specialize H j
    constructor
    · apply Real.logb_lt_logb (by norm_num : (2 : ℝ) > 1)
      exact_mod_cast H _
    · apply Real.logb_lt_logb (by norm_num : (2 : ℝ) > 1)
      exact_mod_cast H _ },
  -- Summing these inequalities
  have sum_log :
      Real.logb 2 ((F.restrict j false).card) +
          Real.logb 2 ((F.restrict j true).card) >
            2 * Real.logb 2 F.card - 2 := by
    linarith [half_log.1, half_log.2]
  -- Combine with `log_ineq` to reach a contradiction
  have := lt_of_le_of_lt log_ineq sum_log
  linarith

/-- **Entropy‑Drop Lemma.**  There exists a coordinate / bit whose
restriction lowers collision entropy by ≥ 1 bit. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  classical
  obtain ⟨i, b, h_half⟩ := exists_restrict_half_real (F := F) hn hF
  have hlog := Real.logb_le_logb (by norm_num : (2:ℝ) > 1) h_half
  rw [Real.logb_div (by norm_num) (Nat.cast_ne_zero.mpr (Nat.one_ne_zero)),
      Real.logb_two] at hlog
  exact ⟨i, b, hlog⟩

end BoolFunc
