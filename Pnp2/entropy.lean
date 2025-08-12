/-
entropy.lean
============

This module sketches a collision-entropy framework.  The core proofs are
now complete so the definitions can be imported by other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
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
  if F.card = 0 then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne']

@[simp] lemma collProb_zero {n : ℕ} {F : Family n} (h : F.card = 0) :
    collProb F = 0 := by simp [collProb, h]

lemma collProb_nonneg {n : ℕ} (F : Family n) :
    0 ≤ collProb F := by
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have hpos : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hnonneg : 0 ≤ (F.card : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
    simp [collProb, h, hnonneg]

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

/-- Restricting on any coordinate/bit cannot increase collision entropy. -/
lemma H₂_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    H₂ (F.restrict i b) ≤ H₂ F := by
  classical
  have hb : 1 < (2 : ℝ) := by norm_num
  -- If restriction empties the family, entropy is zero and the claim is trivial.
  by_cases h0 : (F.restrict i b).card = 0
  ·
    -- Show `0 ≤ H₂ F` and conclude.
    have hF_nonneg : 0 ≤ H₂ F := by
      by_cases hF0 : F.card = 0
      · simpa [H₂, hF0]
      ·
        have hx : 1 ≤ (F.card : ℝ) := by
          have hpos : 0 < F.card := Nat.pos_of_ne_zero hF0
          exact_mod_cast Nat.succ_le_of_lt hpos
        simpa [H₂] using Real.logb_nonneg (b := 2) hb hx
    simpa [H₂, h0] using hF_nonneg
  ·
    -- Otherwise, logarithm monotonicity on the cardinality bound.
    have hpos : 0 < ((F.restrict i b).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h0
    have hle : ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast (Family.card_restrict_le (F := F) (i := i) (b := b))
    have := Real.logb_le_logb_of_le hb hpos hle
    simpa [H₂] using this

/-- There exists some coordinate/bit making the entropy non‑increase
    (trivial since it holds for every coordinate). -/
lemma exists_coord_entropy_noninc {n : ℕ} (F : Family n) (hn : 0 < n) :
    ∃ i : Fin n, ∃ b : Bool, H₂ (F.restrict i b) ≤ H₂ F := by
  classical
  -- Pick the first coordinate (exists since `n > 0`) and `false`.
  refine ⟨⟨0, hn⟩, false, ?_⟩
  simpa using (H₂_restrict_le (F := F) (i := ⟨0, hn⟩) (b := false))

/-- **Entropy non‑increase Lemma.**
There exists a coordinate/bit whose restriction does not increase
collision entropy. -/
lemma exists_coord_entropy_noninc' {n : ℕ} (F : Family n)
    (hn : 0 < n) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F :=
  exists_coord_entropy_noninc (F := F) (hn := hn)

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
      · simp [H₂, hF0]
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

/-!
### Entropy-based measure

The recursion for the decision-tree cover will rely on a simple
numeric measure of a family.  We choose the integer ceiling of the
collision entropy `H₂ F`.  Any real drop in entropy lowers this
measure by at least one, giving a convenient well-founded order.
-/

/-- Complexity measure for a family `F` of Boolean functions:
the integer ceiling of its collision entropy. -/
noncomputable def measure {n : ℕ} (F : Family n) : ℕ :=
  Nat.ceil (H₂ F)

/-- Restricting a family along a coordinate cannot increase the measure. -/
lemma measure_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    measure (F.restrict i b) ≤ measure F := by
  classical
  -- Restricting lowers or preserves the entropy, see `H₂_restrict_le`.
  have h := H₂_restrict_le (F := F) (i := i) (b := b)
  -- `Nat.ceil` is monotone on `ℝ`, so the inequality lifts to the measure.
  unfold measure
  -- `Nat.ceil_mono` converts the entropy inequality into one on the ceiling.
  exact Nat.ceil_mono h

/-- Filtering a family along a predicate cannot increase the measure. -/
lemma measure_filter_le {n : ℕ} (F : Family n)
    (P : BFunc n → Prop) [DecidablePred P] :
    measure (F.filter P) ≤ measure F := by
  classical
  -- Filtering the family lowers or preserves the entropy, see `H₂_filter_le`.
  have h := H₂_filter_le (F := F) (P := P)
  -- The `Nat.ceil` function is monotone, so the inequality transfers.
  unfold measure
  exact Nat.ceil_mono h

/-!
Some concrete values of the measure are handy later on.  They also serve as
sanity checks for the definitions above.
-/

/-- The empty family carries no information and hence has measure `0`. -/
@[simp] lemma measure_empty {n : ℕ} :
    measure (∅ : Family n) = 0 := by
  classical
  unfold measure
  -- The entropy of an empty set is zero by definition of `H₂`.
  simp [H₂]

/-- A family containing a single Boolean function has zero measure. -/
@[simp] lemma measure_singleton {n : ℕ} (f : BFunc n) :
    measure ({f} : Family n) = 0 := by
  classical
  unfold measure
  -- The entropy of a singleton family is zero.
  simp [H₂]

/-- If a family has at least two distinct functions, then its measure is
    strictly positive.  This fact helps show that any reduction in entropy
    forces a decrease in the measure. -/
lemma measure_pos_of_card_two_le {n : ℕ} {F : Family n}
    (hF : 2 ≤ F.card) : 0 < measure F := by
  classical
  -- Since `card F ≥ 2`, the entropy `H₂ F` is at least `1`.
  have hb : 1 < (2 : ℝ) := by norm_num
  have hpos : 0 < (2 : ℝ) := by norm_num
  have hx : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hF
  have hlog : (1 : ℝ) ≤ H₂ F := by
    -- Monotonicity of `logb` transfers the bound on cardinalities to entropies.
    have := Real.logb_le_logb_of_le (b := 2) hb hpos hx
    simpa [H₂] using this
  -- A lower bound `1 ≤ H₂ F` implies the measure, as ceiling, is positive.
  have hposH : 0 < H₂ F := by
    -- Start from `0 < 1` and chain the inequalities.
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this hlog
  unfold measure
  exact Nat.ceil_pos.mpr hposH

/-- If a restriction of a family cuts its size by at least half,
    then the entropy-based measure strictly decreases. -/
lemma measure_restrict_lt_of_card_le_half {n : ℕ} {F : Family n}
    (i : Fin n) (b : Bool)
    (hF : 2 ≤ F.card)
    (hhalf : ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2) :
    measure (F.restrict i b) < measure F := by
  classical
  by_cases h0 : (F.restrict i b).card = 0
  · -- The restriction wipes out the family entirely.
    have hpos : 0 < measure F :=
      measure_pos_of_card_two_le (F := F) (hF := hF)
    simpa [measure, h0] using hpos
  ·
    -- Positivity of the restricted cardinality.
    have hpos_restrict : 0 < ((F.restrict i b).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h0
    have hb : 1 < (2 : ℝ) := by norm_num
    -- `F.card` is positive thanks to the assumption `2 ≤ F.card`.
    have hFposNat : 0 < F.card := lt_of_lt_of_le Nat.zero_lt_two hF
    have hpos_half : 0 < (F.card : ℝ) / 2 := by
      have hcard_pos : 0 < (F.card : ℝ) := by exact_mod_cast hFposNat
      exact div_pos hcard_pos (by norm_num)
    -- Compare entropies via logarithm monotonicity.
    have h :=
      (Real.logb_le_logb (b := 2) hb hpos_restrict hpos_half).mpr hhalf
    -- Rewrite the right-hand side using `logb_div`.
    have hcard_ne_zero : (F.card : ℝ) ≠ 0 := by
      have : 0 < (F.card : ℝ) := by exact_mod_cast hFposNat
      exact ne_of_gt this
    have htwo_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    have hrewrite : Real.logb 2 ((F.card : ℝ) / 2) = H₂ F - 1 := by
        simp [H₂, Real.logb_div hcard_ne_zero htwo_ne_zero]
    have hHle : H₂ (F.restrict i b) ≤ H₂ F - 1 := by
      simpa [H₂, hrewrite] using h
    -- Transfer the bound through the ceiling function.
    have hceil := Nat.ceil_mono hHle
    have hceilsimp : Nat.ceil (H₂ F - 1) = measure F - 1 := by
      unfold measure
      simpa using (Nat.ceil_sub_one (H₂ F))
    have hmeasure_le : measure (F.restrict i b) ≤ measure F - 1 := by
      simpa [measure, hceilsimp] using hceil
    -- Finish with elementary arithmetic on naturals.
    have hFpos : 0 < measure F :=
      measure_pos_of_card_two_le (F := F) (hF := hF)
    have hlt : measure F - 1 < measure F :=
      Nat.sub_lt hFpos Nat.one_pos
    exact lt_of_le_of_lt hmeasure_le hlt

end BoolFunc
