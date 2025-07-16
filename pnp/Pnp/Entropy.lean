import Pnp.BoolFunc
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open Classical
open Real
open BoolFunc
open scoped BigOperators

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

/-!  ## Вспомогательные определения для halving‑леммы -/

open Finset

/-- Вклад функции `f` в координату `i`:
* `2`, если `f` одинаковa на парах `x, x ⟪i := !x i⟫`
  (то есть от `i` не зависит);
* `1` — в противном случае. -/
private def contrib {n : ℕ} (f : BFunc n) (i : Fin n) : ℕ :=
  if h : ∀ x, f x = f (Point.update x i (!x i)) then 2 else 1

/-- Явное неравенство `contrib ≤ 2`, нужное для последующих оценок. -/
private lemma contrib_le_two {n : ℕ} (f : BFunc n) (i : Fin n) :
    contrib f i ≤ 2 := by
  unfold contrib; split <;> simp

/-- Сумма вкладов одной функции по всем координатам раскладывается
на `n` постоянных единиц и отдельный счёт координат, на которых
функция константна. -/
private lemma sum_contrib {n : ℕ} (f : BFunc n) :
    (∑ i : Fin n, contrib f i) =
      n + ∑ i : Fin n,
        (if _ : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) := by
  classical
  -- сначала перепишем каждое `contrib` как `1 + …`
  have h_single :
      ∀ i : Fin n,
        contrib f i =
          1 +
            (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) := by
    intro i
    by_cases h : ∀ x, f x = f (Point.update x i (!x i))
    · have hc : contrib f i = 2 := by
        unfold contrib
        exact if_pos h
      have ho :
          (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) = 1 :=
        if_pos h
      have hsum : 1 + (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) = 2 := by
        simpa [ho]
      simpa [hc, ho] using hsum
    · have hc : contrib f i = 1 := by
        unfold contrib
        exact if_neg h
      have ho :
          (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) = 0 :=
        if_neg h
      have hsum : 1 + (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0) = 1 := by
        simpa [ho]
      simpa [hc, ho] using hsum
  have h_sum :
      (∑ i : Fin n, contrib f i) =
        ∑ i : Fin n,
          (1 +
            (if h : ∀ x, f x = f (Point.update x i (!x i)) then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [h_single i] using h_single i
  -- теперь `∑ (1 + …) = n + ∑ …`
  simpa [Finset.sum_add_distrib, Finset.card_fin] using h_sum

/-- Helper lemma: a finset with at least two elements contains two distinct
elements. -/
private lemma Finset.card_ge_two.mp {α} [DecidableEq α] {s : Finset α}
    (h : 2 ≤ s.card) : ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  have h1 : 1 < s.card := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) h
  simpa [Finset.one_lt_card] using h1

/-- **Halving lemma (ℝ version, формулировка).**
Если в семействе нет *обеих* констант `true` и `false`
одновременно, то существует координата, фиксирование которой
сокращает мощность семейства хотя бы в два раза. -/
lemma exists_restrict_half_real_aux
    {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
  ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  by_contra! h
  have h0false := h ⟨0, hn⟩ false
  have h0true  := h ⟨0, hn⟩ true

  -- 1) Определяем пару
  let pair : BFunc n → BFunc n × BFunc n := fun f =>
    (f.restrictCoord ⟨0, hn⟩ false, f.restrictCoord ⟨0, hn⟩ true)

  -- 2) Доказываем, что пара инъективна
  have pair_inj : Function.Injective pair := by
    intro f₁ f₂ hpair
    have hf := congr_arg Prod.fst hpair
    have ht := congr_arg Prod.snd hpair
    ext x
    cases hx : x ⟨0, hn⟩
    · -- в ветке `x 0 = false` сравниваем fst
      have h := congrArg (fun g => g x) hf
      simpa [pair, restrictCoord_agrees hx] using h
    · -- в ветке `x 0 = true` сравниваем snd
      have h := congrArg (fun g => g x) ht
      simpa [pair, restrictCoord_agrees hx] using h

  -- 3) Оценка кардинальностей: |F| ≤ |F.restrict false| * |F.restrict true|
  have prod_upper : F.card ≤
      (F.restrict ⟨0, hn⟩ false).card *
      (F.restrict ⟨0, hn⟩ true).card := by
    -- образ pair лежит в декартове произведение
    have subset_prod :
        (F.image pair) ⊆
        (F.restrict ⟨0, hn⟩ false).product
        (F.restrict ⟨0, hn⟩ true) := by
      rintro ⟨g₀, g₁⟩ hmem
      rcases Finset.mem_image.1 hmem with ⟨f, hf, hpair⟩
      refine Finset.mem_product.2 ?_
      constructor
      · refine Finset.mem_image.2 ?_
        refine ⟨f, hf, ?_⟩
        simpa [pair] using congrArg Prod.fst hpair
      · refine Finset.mem_image.2 ?_
        refine ⟨f, hf, ?_⟩
        simpa [pair] using congrArg Prod.snd hpair
    have card_le : (F.image pair).card ≤
        (F.restrict ⟨0, hn⟩ false).card *
        (F.restrict ⟨0, hn⟩ true).card := by
      simpa [Finset.card_product] using Finset.card_le_card subset_prod
    -- но pair_inj даёт equality
    have eqF : (F.image pair).card = F.card :=
      (Finset.card_image_of_injective (s := F) pair_inj)
    simpa [eqF] using card_le

  -- 4) Нижняя граница из h0false, h0true
  have prod_lower :
      ((F.card : ℝ) / 2) ^ 2 <
        (F.restrict ⟨0, hn⟩ false).card *
        (F.restrict ⟨0, hn⟩ true).card := by
    have h1 := h0false
    have h2 := h0true
    have := mul_lt_mul'' h1 h2 (by positivity) (by positivity)
    simpa [pow_two] using this

  ----------------------------------------------------------------
  -- 5.  Сводим две несовместные оценки к противоречию.
  ----------------------------------------------------------------
  have prod_upper' :
      (F.card : ℝ) ≤
        (F.restrict ⟨0, hn⟩ false).card *
        (F.restrict ⟨0, hn⟩ true).card := by
    -- переводим `prod_upper` в ℝ
    exact_mod_cast prod_upper

  have prod_lower' :
      (F.card : ℝ) < 4 * (
        (F.restrict ⟨0, hn⟩ false).card *
        (F.restrict ⟨0, hn⟩ true).card) := by
    -- (|F|/2)² < RHS  ⇒  |F| < 4·RHS
    have hmul :=
      (mul_lt_mul_of_pos_left prod_lower (show (0 : ℝ) < 4 by norm_num))
    have hcard : (4 : ℝ) * ((F.card : ℝ) / 2) ^ 2 = (F.card : ℝ) := by
      field_simp [pow_two]
    simpa [hcard] using hmul

  have : (F.card : ℝ) < (F.card : ℝ) :=
    lt_of_lt_of_le prod_lower' prod_upper'
  exact (lt_irrefl _ this).elim

/-- **Existence of a halving restriction.**  Casts the real-valued inequality
from `exists_restrict_half_real_aux` back to natural numbers. -/
lemma exists_restrict_half
    {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
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
lemma exists_restrict_half_real
    {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  obtain ⟨i, b, hle⟩ :=
    exists_restrict_half (F := F) (hn := hn) (hF := hF)
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
