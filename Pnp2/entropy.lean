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
import Pnp2.BoolFunc.Sensitivity

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

/--
A bound on the integer measure immediately bounds the collision entropy.  This
lemma is convenient when switching from the `measure` abstraction back to the
real-valued quantity `H₂ F` required by entropy-based cover constructions.
-/
lemma H₂_le_of_measure_le {n : ℕ} (F : Family n) {h : ℕ}
    (hμ : measure F ≤ h) : H₂ F ≤ (h : ℝ) := by
  -- First relate the entropy directly to the ceiling-based measure.
  have hH₂ : H₂ F ≤ (measure F : ℝ) := by
    -- `Nat.le_ceil` specializes to `H₂ F ≤ ⌈H₂ F⌉₊`, which is `measure F`.
    simpa [measure] using (Nat.le_ceil (a := H₂ F))
  -- Cast the natural bound to the reals and combine both inequalities.
  have hcast : (measure F : ℝ) ≤ h := by exact_mod_cast hμ
  exact hH₂.trans hcast

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

/-- If restricting along a coordinate identifies at least half of the
    functions, the measure drops strictly.  This criterion will later
    ensure progress in the decision‑tree construction once we know that
    many functions agree after fixing a bit. -/
lemma measure_restrict_lt_of_card_le_half {n : ℕ} (F : Family n)
    (i : Fin n) (b : Bool)
    (hpos : 0 < (F.restrict i b).card)
    (hhalf : 2 * (F.restrict i b).card ≤ F.card) :
    measure (F.restrict i b) < measure F := by
  classical
  -- Work with real numbers to leverage logarithm monotonicity.
  have hb : 1 < (2 : ℝ) := by norm_num
  have hposR : 0 < ((F.restrict i b).card : ℝ) := by exact_mod_cast hpos
  -- The size after doubling remains positive in the reals.
  have hpos2 :
      0 < ((2 * (F.restrict i b).card : ℕ) : ℝ) := by
    have : 0 < (2 : ℝ) * ((F.restrict i b).card : ℝ) := by
      have h2pos : 0 < (2 : ℝ) := by norm_num
      exact mul_pos h2pos hposR
    simpa [Nat.cast_mul, Nat.cast_ofNat] using this
  -- Cast the cardinality inequality to `ℝ`.
  have hhalfR :
      ((2 * (F.restrict i b).card : ℕ) : ℝ) ≤ (F.card : ℝ) :=
    by exact_mod_cast hhalf
  -- Compare logarithms of the doubled restricted family with the original.
  have hlog :=
      Real.logb_le_logb_of_le (b := 2) hb hpos2 hhalfR
  -- Rewrite `logb 2 (2 * |F_b|)` as `1 + logb 2 |F_b|`.
  have hlogb2 : Real.logb 2 (2 : ℝ) = 1 := by simp
  have hy0 : ((F.restrict i b).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hmul :
      Real.logb 2 ((2 : ℝ) * ((F.restrict i b).card : ℝ)) =
        Real.logb 2 (2 : ℝ) + Real.logb 2 ((F.restrict i b).card : ℝ) :=
    Real.logb_mul (b := 2) (hx := by norm_num) (hy := hy0)
  have hcast :
      ((2 * (F.restrict i b).card : ℕ) : ℝ) =
        (2 : ℝ) * ((F.restrict i b).card : ℝ) := by
    norm_cast
  have hlog' :
      H₂ (F.restrict i b) + 1 ≤ H₂ F := by
    -- The previous inequality becomes an entropy bound after rewriting.
    simpa [H₂, hcast, hmul, hlogb2, add_comm, add_left_comm, add_assoc]
      using hlog
  -- Convert the entropy inequality into one on the integer ceiling.
  have hceil :
      Nat.ceil (H₂ (F.restrict i b) + 1) ≤ Nat.ceil (H₂ F) :=
    Nat.ceil_mono hlog'
  -- Simplify `ceil (x + 1)` using nonnegativity of the entropy.
  have hposH : 0 ≤ H₂ (F.restrict i b) := by
    -- since the restricted family is nonempty, its entropy is nonnegative
    have hcard : 1 ≤ (F.restrict i b).card := Nat.succ_le_of_lt hpos
    have hx : 1 ≤ ((F.restrict i b).card : ℝ) := by exact_mod_cast hcard
    have hb' : 1 < (2 : ℝ) := by norm_num
    simpa [H₂] using Real.logb_nonneg (b := 2) hb' hx
  have hceq :
      Nat.ceil (H₂ (F.restrict i b) + 1) =
        measure (F.restrict i b) + 1 := by
    have := Nat.ceil_add_one (a := H₂ (F.restrict i b)) (ha := hposH)
    simpa [measure] using this
  have hfinal :
      measure (F.restrict i b) + 1 ≤ measure F := by
    -- Replace the left-hand ceiling using `hceq` without invoking extra simp rules.
    have htemp := hceil
    rw [hceq] at htemp
    -- Now substitute the definition of `measure F` for the remaining ceiling.
    simpa [measure] using htemp
  -- Translating `a + 1 ≤ b` to `a < b` concludes the proof.
  have hsucc : Nat.succ (measure (F.restrict i b)) ≤ measure F := by
    simpa [Nat.succ_eq_add_one] using hfinal
  have hlt : measure (F.restrict i b) < Nat.succ (measure (F.restrict i b)) :=
    Nat.lt_succ_self _
  exact lt_of_lt_of_le hlt hsucc

/-- A convenient restatement of `measure_restrict_lt_of_card_le_half`.
The lemma asserts that if restricting the family to the `i`‑th coordinate
leaves at most half of its members, then the integer measure strictly
decreases.  It is phrased as a thin wrapper to ease later use. -/
lemma measure_restrict_decreases {n : ℕ} (F : Family n)
    (i : Fin n) (b : Bool)
    (hpos : 0 < (F.restrict i b).card)
    (hhalf : 2 * (F.restrict i b).card ≤ F.card) :
    measure (F.restrict i b) < measure F :=
  measure_restrict_lt_of_card_le_half (F := F) (i := i) (b := b)
    (hpos := hpos) (hhalf := hhalf)

/-- If filtering the family retains at most half of its members, the measure
    strictly decreases.  This is a generalisation of
    `measure_restrict_lt_of_card_le_half` from coordinate restrictions to
    arbitrary predicates. -/
lemma measure_filter_lt_of_card_le_half {n : ℕ} (F : Family n)
    (P : BFunc n → Prop) [DecidablePred P]
    (hpos : 0 < (F.filter P).card)
    (hhalf : 2 * (F.filter P).card ≤ F.card) :
    measure (F.filter P) < measure F := by
  classical
  -- Work with real numbers as in the restricted case.
  have hb : 1 < (2 : ℝ) := by norm_num
  have hposR : 0 < ((F.filter P).card : ℝ) := by exact_mod_cast hpos
  -- Doubling the size preserves positivity.
  have hpos2 : 0 < ((2 * (F.filter P).card : ℕ) : ℝ) := by
    have : 0 < (2 : ℝ) * ((F.filter P).card : ℝ) := by
      have h2pos : 0 < (2 : ℝ) := by norm_num
      exact mul_pos h2pos hposR
    simpa [Nat.cast_mul, Nat.cast_ofNat] using this
  -- Cast the cardinality inequality to the reals.
  have hhalfR : ((2 * (F.filter P).card : ℕ) : ℝ) ≤ (F.card : ℝ) :=
    by exact_mod_cast hhalf
  -- Show the original family is nonempty to justify logarithms on the RHS.
  have hFpos : 0 < (F.card : ℝ) := by
    -- from 0 < |F.filter P| and 2|F.filter P| ≤ |F|
    have : 0 < 2 * (F.filter P).card := Nat.mul_pos (by decide) hpos
    exact_mod_cast lt_of_lt_of_le this hhalf

  -- Compare logarithms of the doubled filtered family with the original.
  have hlog :=
      Real.logb_le_logb_of_le (b := 2) hb hpos2 hhalfR
  -- Rewrite `logb` of the product as a sum.
  have hlogb2 : Real.logb 2 (2 : ℝ) = 1 := by simp
  have hy0 : ((F.filter P).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hmul :
      Real.logb 2 ((2 : ℝ) * ((F.filter P).card : ℝ)) =
        Real.logb 2 (2 : ℝ) + Real.logb 2 ((F.filter P).card : ℝ) :=
    Real.logb_mul (b := 2) (hx := by norm_num) (hy := hy0)
  have hcast :
      ((2 * (F.filter P).card : ℕ) : ℝ) =
        (2 : ℝ) * ((F.filter P).card : ℝ) := by
    norm_cast
  have hlog' :
      H₂ (F.filter P) + 1 ≤ H₂ F := by
    simpa [H₂, hcast, hmul, hlogb2, add_comm, add_left_comm, add_assoc]
      using hlog
  -- Lift the entropy inequality to one on the integer ceiling.
  have hceil : Nat.ceil (H₂ (F.filter P) + 1) ≤ Nat.ceil (H₂ F) :=
    Nat.ceil_mono hlog'
  -- Entropy of a nonempty family is nonnegative.
  have hposH : 0 ≤ H₂ (F.filter P) := by
    have hcard : 1 ≤ (F.filter P).card := Nat.succ_le_of_lt hpos
    have hx : 1 ≤ ((F.filter P).card : ℝ) := by exact_mod_cast hcard
    have hb' : 1 < (2 : ℝ) := by norm_num
    simpa [H₂] using Real.logb_nonneg (b := 2) hb' hx
  -- Simplify the left-hand side using `Nat.ceil_add_one`.
  have hceq :
      Nat.ceil (H₂ (F.filter P) + 1) = measure (F.filter P) + 1 := by
    have := Nat.ceil_add_one (a := H₂ (F.filter P)) (ha := hposH)
    simpa [measure] using this

  have hfinal :
      measure (F.filter P) + 1 ≤ measure F := by
    have htemp := hceil
    rw [hceq] at htemp
    simpa [measure] using htemp
  -- Convert the natural inequality to a strict one.
  have hsucc : Nat.succ (measure (F.filter P)) ≤ measure F := by
    simpa [Nat.succ_eq_add_one] using hfinal
  have hlt : measure (F.filter P) < Nat.succ (measure (F.filter P)) :=
    Nat.lt_succ_self _
  exact lt_of_lt_of_le hlt hsucc

/-!
### Lexicographic measure

For the recursive cover construction it is convenient to combine the
entropy-based `measure` with the raw cardinality of the family.  The
resulting pair is ordered lexicographically; any drop in either
component therefore witnesses a strict decrease in the overall
complexity.
-/

/-- Lexicographic complexity measure `(measure F, F.card)` for a family. -/
@[simp] noncomputable def measureLex {n : ℕ} (F : Family n) : ℕ × ℕ :=
  (measure F, F.card)

/-- Relation implementing the lexicographic order on the pair measure. -/
abbrev measureLexRel : (ℕ × ℕ) → (ℕ × ℕ) → Prop :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).rel

/-- The lexicographic order on measures is well-founded. -/
lemma measureLexRel_wf : WellFounded measureLexRel :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- If the entropy measure drops strictly, the lexicographic measure decreases. -/
lemma measureLexRel_of_measure_lt {n : ℕ} {F G : Family n}
    (h : measure F < measure G) :
    measureLexRel (measureLex F) (measureLex G) := by
  dsimp [measureLexRel, measureLex, Prod.lex]
  exact Prod.Lex.left _ _ h

/-- If the entropy measures coincide but the cardinality drops, the
lexicographic measure still decreases. -/
lemma measureLexRel_of_measure_eq_card_lt {n : ℕ} {F G : Family n}
    (hμ : measure F = measure G) (hc : F.card < G.card) :
    measureLexRel (measureLex F) (measureLex G) := by
  dsimp [measureLexRel, measureLex, Prod.lex]
  simpa [hμ] using Prod.Lex.right _ hc

/-- Restricting along a coordinate strictly decreases the lexicographic
measure provided the restricted family is smaller.  The proof analyses the
entropy inequality `measure_restrict_le` and falls back to a cardinality drop
when the entropies coincide. -/
lemma measureLex_restrict_decreases {n : ℕ} (F : Family n)
    (i : Fin n) (b : Bool)
    (hc : (F.restrict i b).card < F.card) :
    measureLexRel (measureLex (F.restrict i b)) (measureLex F) := by
  classical
  -- Restricting cannot increase the entropy measure.
  have hμ : measure (F.restrict i b) ≤ measure F :=
    measure_restrict_le (F := F) (i := i) (b := b)
  -- Either the entropy drops strictly, or we rely on the cardinality drop.
  rcases lt_or_eq_of_le hμ with hlt | hEq
  · exact measureLexRel_of_measure_lt (F := F.restrict i b) (G := F) hlt
  · exact
      measureLexRel_of_measure_eq_card_lt (F := F.restrict i b) (G := F)
        hEq hc

/--
If two distinct functions from a family collapse to the same function after
restricting a coordinate, the lexicographic measure strictly decreases on that
branch.  This is a convenient wrapper combining
`Family.card_restrict_lt_of_restrict_eq` with
`measureLex_restrict_decreases`.-/
lemma measureLex_restrict_lt_of_restrict_eq {n : ℕ} {F : Family n}
    {i : Fin n} {b : Bool} {f g : BFunc n}
    (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g)
    (heq : BFunc.restrictCoord f i b = BFunc.restrictCoord g i b) :
    measureLexRel (measureLex (F.restrict i b)) (measureLex F) := by
  classical
  -- The coinciding restrictions guarantee a strict drop in the branch size.
  have hc : (F.restrict i b).card < F.card :=
    Family.card_restrict_lt_of_restrict_eq (F := F) (i := i) (b := b)
      (f := f) (g := g) hf hg hfg heq
  -- Feed this inequality into the general measure monotonicity lemma.
  exact measureLex_restrict_decreases (F := F) (i := i) (b := b) hc

/--
If restricting along a coordinate leaves at most half of the functions,
the lexicographic measure drops strictly.  This convenience lemma packages
`measure_restrict_decreases` for later use in the recursive construction. -/
lemma measureLex_restrict_lt_of_card_le_half {n : ℕ} (F : Family n)
    (i : Fin n) (b : Bool)
    (hpos : 0 < (F.restrict i b).card)
    (hhalf : 2 * (F.restrict i b).card ≤ F.card) :
    measureLexRel (measureLex (F.restrict i b)) (measureLex F) := by
  -- First obtain the strict entropy drop from the cardinality condition.
  have hμ :
      measure (F.restrict i b) < measure F :=
    measure_restrict_decreases (F := F) (i := i) (b := b)
      (hpos := hpos) (hhalf := hhalf)
  -- Translating this entropy inequality to the lexicographic measure
  -- yields the desired well-founded relation step.
  exact measureLexRel_of_measure_lt (F := F.restrict i b) (G := F) hμ

/--
From a witness that one branch of a restriction contains at most half of the
family, we immediately obtain a strict drop in the lexicographic measure.
This lemma is a convenient wrapper around
`measureLex_restrict_lt_of_card_le_half` for existential statements.  It will
allow the recursive construction to invoke the measure decrease in a single
step once such a branch is identified.-/
lemma exists_branch_lex_smaller_of_half {n : ℕ} (F : Family n) (i : Fin n)
    (h : ∃ b : Bool,
      0 < (F.restrict i b).card ∧ 2 * (F.restrict i b).card ≤ F.card) :
    ∃ b : Bool,
      measureLexRel (measureLex (F.restrict i b)) (measureLex F) := by
  classical
  -- Unpack the witness branch and apply the previous lemma.
  rcases h with ⟨b, hpos, hhalf⟩
  exact ⟨b,
    measureLex_restrict_lt_of_card_le_half (F := F) (i := i) (b := b)
      (hpos := hpos) (hhalf := hhalf)⟩

/--
If two distinct functions from the family become identical after restricting a
coordinate, the lexicographic measure drops on that branch.  This lemma packages
`measureLex_restrict_lt_of_restrict_eq` in an existential form.
-/
lemma exists_branch_lex_smaller_of_merge {n : ℕ} (F : Family n) (i : Fin n)
    (h : ∃ f ∈ F, ∃ g ∈ F, f ≠ g ∧ ∃ b : Bool,
      BFunc.restrictCoord f i b = BFunc.restrictCoord g i b) :
    ∃ b : Bool,
      measureLexRel (measureLex (F.restrict i b)) (measureLex F) := by
  classical
  rcases h with ⟨f, hf, g, hg, hfg, b, heq⟩
  exact ⟨b,
    measureLex_restrict_lt_of_restrict_eq (F := F) (i := i) (b := b)
      (f := f) (g := g) hf hg hfg heq⟩

/-!
### Three-component lexicographic measure with dimension

To guarantee progress of the recursive cover construction even in degenerate
cases (e.g. when restricting along a sensitive coordinate neither decreases the
measure nor the cardinality), we enrich the lexicographic measure with a third
component tracking the number of *available* coordinates.  This allows us to
prove termination solely from the fact that each recursive step removes one
coordinate from the set `A` of yet-unfixed indices.
-/

/-- Three-component lexicographic complexity measure
`(measure F, F.card, A.card)` for a family `F` with a set of available
coordinates `A`.  The measure is represented as a pair-of-a-pair to reuse
`Prod.lex`. -/
@[simp] noncomputable
def measureLex3 {n : ℕ} (F : Family n) (A : Finset (Fin n)) : (ℕ × ℕ) × ℕ :=
  ((measure F, F.card), A.card)

/-- Relation implementing the lexicographic order on triples.  It is the
lexicographic order on the first two components, with the third component used
as a final tie breaker. -/
abbrev measureLex3Rel : ((ℕ × ℕ) × ℕ) → ((ℕ × ℕ) × ℕ) → Prop :=
  (Prod.lex (Prod.lex Nat.lt_wfRel Nat.lt_wfRel) Nat.lt_wfRel).rel

/-- The three-component lexicographic relation is well-founded. -/
lemma measureLex3Rel_wf : WellFounded measureLex3Rel :=
  (Prod.lex (Prod.lex Nat.lt_wfRel Nat.lt_wfRel) Nat.lt_wfRel).wf

/--
If the two-component lexicographic measure drops, then the
three-component measure also decreases, regardless of the dimension
component.  This lemma allows us to lift measure decreases proved for
`measureLex` to the extended measure `measureLex3`.
-/
lemma measureLex3Rel_of_measureLex {n : ℕ} {F G : Family n}
    {A B : Finset (Fin n)}
    (h : measureLexRel (measureLex F) (measureLex G)) :
    measureLex3Rel (measureLex3 F A) (measureLex3 G B) := by
  -- The relation on triples prioritises the first pair.  A strict drop in
  -- that pair therefore yields a lexicographic decrease for the whole
  -- triple, irrespective of the third component.
  dsimp [measureLex3, measureLex3Rel]
  exact Prod.Lex.left _ _ h

/--
If two distinct functions from `F` collapse to the same function after
restricting a coordinate, the three-component lexicographic measure
strictly decreases on that branch.  This is a direct lift of
`measureLex_restrict_lt_of_restrict_eq` to `measureLex3`.
-/
lemma measureLex3_restrict_lt_of_restrict_eq {n : ℕ} (F : Family n)
    (A : Finset (Fin n)) {i : Fin n} {b : Bool}
    {f g : BFunc n} (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g)
    (heq : BFunc.restrictCoord f i b = BFunc.restrictCoord g i b) :
    measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
      (measureLex3 F A) := by
  -- First obtain the decrease for the two-component measure and then lift it
  -- to `measureLex3`.
  have h :=
    measureLex_restrict_lt_of_restrict_eq (F := F) (i := i) (b := b)
      (f := f) (g := g) hf hg hfg heq
  exact
    measureLex3Rel_of_measureLex (F := F.restrict i b) (G := F)
      (A := A.erase i) (B := A) h

/--
If restricting on a coordinate leaves at most half of the functions in the
family, the three-component measure drops strictly on that branch.  This is a
`measureLex3` version of `measureLex_restrict_lt_of_card_le_half`.
-/
lemma measureLex3_restrict_lt_of_card_le_half {n : ℕ} (F : Family n)
    (A : Finset (Fin n)) (i : Fin n) (b : Bool)
    (hpos : 0 < (F.restrict i b).card)
    (hhalf : 2 * (F.restrict i b).card ≤ F.card) :
    measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
      (measureLex3 F A) := by
  -- Apply the two-component lemma and lift the result.
  have h :=
    measureLex_restrict_lt_of_card_le_half (F := F) (i := i) (b := b)
      (hpos := hpos) (hhalf := hhalf)
  exact
    measureLex3Rel_of_measureLex (F := F.restrict i b) (G := F)
      (A := A.erase i) (B := A) h

/--
Existential form of `measureLex3_restrict_lt_of_card_le_half`.  Given a
witness branch where the restricted family is at most half of the original,
we obtain a corresponding decrease of the three-component measure.
-/
lemma exists_branch_measureLex3_smaller_of_half {n : ℕ} (F : Family n)
    (A : Finset (Fin n)) (i : Fin n)
    (h : ∃ b : Bool,
      0 < (F.restrict i b).card ∧ 2 * (F.restrict i b).card ≤ F.card) :
    ∃ b : Bool,
      measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
        (measureLex3 F A) := by
  classical
  rcases exists_branch_lex_smaller_of_half (F := F) (i := i) h with ⟨b, hb⟩
  exact
    ⟨b,
      measureLex3Rel_of_measureLex (F := F.restrict i b) (G := F)
        (A := A.erase i) (B := A) hb⟩

/--
Existential form of `measureLex3_restrict_lt_of_restrict_eq`.  If two members
of the family merge after restricting a coordinate, there exists a Boolean
branch where the three-component measure decreases.
-/
lemma exists_branch_measureLex3_smaller_of_merge {n : ℕ} (F : Family n)
    (A : Finset (Fin n)) (i : Fin n)
    (h : ∃ f ∈ F, ∃ g ∈ F, f ≠ g ∧ ∃ b : Bool,
      BFunc.restrictCoord f i b = BFunc.restrictCoord g i b) :
    ∃ b : Bool,
      measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
        (measureLex3 F A) := by
  classical
  rcases exists_branch_lex_smaller_of_merge (F := F) (i := i) h with ⟨b, hb⟩
  exact
    ⟨b,
      measureLex3Rel_of_measureLex (F := F.restrict i b) (G := F)
        (A := A.erase i) (B := A) hb⟩

/--
Restricting a family along a coordinate from the available set strictly
decreases the three-component measure because the set of available coordinates
shrinks.  The entropy and cardinality components may stay the same, but the
dimension component drops by one.
-/
lemma measureLex3_restrict_lt_dim {n : ℕ} (F : Family n) (A : Finset (Fin n))
    {i : Fin n} (hi : i ∈ A) (b : Bool) :
    measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
      (measureLex3 F A) := by
  classical
  -- Entropy and cardinality do not increase upon restriction.
  have hμ : measure (F.restrict i b) ≤ measure F :=
    measure_restrict_le (F := F) (i := i) (b := b)
  have hc : (F.restrict i b).card ≤ F.card :=
    Family.card_restrict_le (F := F) (i := i) (b := b)
  -- Removing `i` from `A` strictly decreases its cardinality.
  have hA : (A.erase i).card < A.card := by
    have hss : A.erase i ⊂ A := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      refine ⟨Finset.erase_subset _ _, ?_⟩
      intro h
      have hi_not : i ∉ A.erase i := by simpa using Finset.not_mem_erase i A
      have hi_in : i ∈ A.erase i := by simpa [h] using hi
      exact hi_not hi_in
    exact Finset.card_lt_card hss
  -- Split into cases depending on whether entropy or cardinality drop.
  dsimp [measureLex3, measureLex3Rel]
  by_cases hμlt : measure (F.restrict i b) < measure F
  · -- Entropy strictly decreases: conclude immediately.
    have hx := measureLexRel_of_measure_lt (F := F.restrict i b) (G := F) hμlt
    exact Prod.Lex.left _ _ hx
  · -- Entropy preserved; analyse cardinality.
    have hμeq : measure (F.restrict i b) = measure F :=
      le_antisymm hμ (le_of_not_gt hμlt)
    have hc' := lt_or_eq_of_le hc
    cases hc' with
    | inl hc_lt =>
        -- Cardinality strictly decreases.
        have hx :=
          measureLexRel_of_measure_eq_card_lt (F := F.restrict i b) (G := F)
            hμeq hc_lt
        exact Prod.Lex.left _ _ hx
    | inr hc_eq =>
        -- Both entropy and cardinality coincide; rely on the dimension drop.
        have hpair :
            (measure (F.restrict i b), (F.restrict i b).card) =
              (measure F, F.card) := by simpa [hμeq, hc_eq]
        -- After unfolding the relation, the goal reduces to applying
        -- `Prod.Lex.right` with this equality and the strict drop `hA`.
        -- Expand the goal and perform the substitution.
        have hx :
            (Prod.lex (Prod.lex Nat.lt_wfRel Nat.lt_wfRel) Nat.lt_wfRel).rel
              ((measure F, F.card), (A.erase i).card)
              ((measure F, F.card), A.card) :=
          Prod.Lex.right (a := (measure F, F.card))
            (b₁ := (A.erase i).card) (b₂ := A.card) hA
        have :
            measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
              (measureLex3 F A) := by
          simpa [measureLex3Rel, measureLex3, hpair] using hx
        exact this

/--
If the family `F` exhibits sensitivity on some coordinate inside the set `A`,
then fixing that coordinate strictly decreases the three-component measure
`measureLex3`.  This remains true even for counterexamples such as the family
`{id, not}` on one bit: restricting along the unique sensitive coordinate does
not shrink the family, yet the dimension component drops from `A.card`,
ensuring progress for the recursive construction.
-/
lemma exists_branch_measure_drop_of_sensitive {n : ℕ}
    (F : Family n) (A : Finset (Fin n))
    (h : ∃ i ∈ A, sensitiveCoord F i) :
    ∃ i ∈ A, ∀ b : Bool,
        measureLex3Rel (measureLex3 (F.restrict i b) (A.erase i))
          (measureLex3 F A) := by
  classical
  rcases h with ⟨i, hiA, _hi⟩
  refine ⟨i, hiA, ?_⟩
  intro b
  exact
    measureLex3_restrict_lt_dim (F := F) (A := A) (i := i) hiA (b := b)

/-!
Removing a single function from the family strictly decreases the
`measureLex3` complexity measure: the entropy component cannot increase
because `erase` is realised by filtering, while the cardinality drops by one.
The dimension component `A.card` stays unchanged.  This lemma is useful for
preprocessing steps that discard trivially false functions before selecting a
splitting coordinate.
-/
lemma measureLex3_erase_lt {n : ℕ} (F : Family n) (A : Finset (Fin n))
    {f : BFunc n} (hf : f ∈ F) :
    measureLex3Rel (measureLex3 (Finset.erase F f) A) (measureLex3 F A) := by
  classical
  -- Filtering by `≠ f` realises `erase`, so the measure cannot increase.
  have hμ : measure (Finset.erase F f) ≤ measure F := by
    simpa [Finset.filter_ne'] using
      (measure_filter_le (F := F) (P := fun g : BFunc n => g ≠ f))
  -- Removing an element strictly decreases the family size.
  have hc : (Finset.erase F f).card < F.card := by
    -- `erase` lowers the cardinality by one.
    have hpos : 0 < F.card := Finset.card_pos.mpr ⟨f, hf⟩
    have hcard := Finset.card_erase_of_mem hf
    -- Rephrase `card (erase f) = card F - 1` in a form convenient for `lt`.
    have hsucc : (Finset.erase F f).card + 1 = F.card := by
      have hsub : F.card - 1 + 1 = F.card :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      simpa [hcard, hsub, Nat.succ_eq_add_one] using
        congrArg (fun t => t + 1) hcard
    -- `a < a + 1` gives the desired strict inequality.
    have hlt : (Finset.erase F f).card < (Finset.erase F f).card + 1 :=
      Nat.lt_succ_self _
    simpa [hsucc] using hlt
  -- Combine the entropy and cardinality facts to obtain the lexicographic drop.
  dsimp [measureLex3, measureLex3Rel]
  by_cases hμlt : measure (Finset.erase F f) < measure F
  · -- Entropy decreased, so the whole measure drops immediately.
    have hx :=
      measureLexRel_of_measure_lt (F := Finset.erase F f) (G := F) hμlt
    exact Prod.Lex.left _ _ hx
  · -- Entropy preserved; rely on the cardinality decrease.
    have hμeq : measure (Finset.erase F f) = measure F :=
      le_antisymm hμ (le_of_not_gt hμlt)
    have hx :=
      measureLexRel_of_measure_eq_card_lt (F := Finset.erase F f) (G := F)
        hμeq hc
    exact Prod.Lex.left _ _ hx

/--
If the family contains a function that is everywhere `false`, erasing that
function strictly decreases the three-component measure `measureLex3`.  This
lemma packages `measureLex3_erase_lt` in an existential form convenient for
recursive constructions that peel off constantly `false` functions before
branching on a sensitive coordinate.-/
lemma exists_measureLex3_drop_const_false {n : ℕ} (F : Family n)
    (A : Finset (Fin n))
    (h : ∃ f ∈ F, ∀ x, f x = false) :
    ∃ f ∈ F,
      measureLex3Rel (measureLex3 (Finset.erase F f) A) (measureLex3 F A) := by
  classical
  rcases h with ⟨f, hfF, hfconst⟩
  exact ⟨f, hfF, measureLex3_erase_lt (F := F) (A := A) (f := f) hfF⟩

end BoolFunc
