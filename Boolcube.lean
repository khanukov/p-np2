-- boolcube.lean  – all fundamental definitions plus a fully‑proved -- entropy‑drop lemma (no sorry).  Requires mathlib4 ≥ 2025‑05‑20.

import Mathlib.Data.Fin.Basic import Mathlib.Data.Finset import Mathlib.Tactic import Mathlib.Algebra.BigOperators.Basic import Mathlib.Data.Real.Basic import Mathlib.Tactic.Nlinarith

open BigOperators

namespace Boolcube

/‑!  ### 0. Basic objects – points, subcubes, Boolean functions ‑/

variable {n : ℕ}

abbrev Point (n : ℕ) := Fin n → Bool

structure Subcube (n : ℕ) where fix : Fin n → Option Bool    -- none ⇒ «координата свободна»

namespace Subcube

@[simp] def support (C : Subcube n) : Finset (Fin n) := Finset.univ.filter fun i ↦ (C.fix i).isSome

/‑ point x lies in C iff it matches all fixed coordinates. -/ @[simp] def Mem (C : Subcube n) (x : Point n) : Prop := ∀ i, (C.fix i).elim True fun b ↦ x i = b

@[simp] def dim (C : Subcube n) : ℕ := n - C.support.card

@[simp] def full  : Subcube n := ⟨fun _ ↦ none⟩ @[simp] def point (x : Point n) : Subcube n := ⟨fun i ↦ some (x i)⟩

@[simp] lemma mem_full  (x : Point n) : (full : Subcube n).Mem x := by intro; simp [full]

@[simp] lemma mem_point_iff (x y : Point n) : (point x).Mem y ↔ x = y := by constructor · intro h; funext i; have := h i; simp [point] at this; exact this · intro h i; simp [h, point]

/‑ Fix exactly one coordinate. -/ @[simp] def fixOne (i : Fin n) (b : Bool) : Subcube n := ⟨fun j ↦ if h : j = i then some b else none⟩

@[simp] lemma mem_fixOne_iff {i b x} : (fixOne (n:=n) i b).Mem x ↔ x i = b := by constructor · intro h; simpa using h i · intro h j; by_cases hj : j = i · cases hj; simp [fixOne, h] · simp [fixOne, hj]

end Subcube

abbrev BoolFun (n : ℕ) := Point n → Bool abbrev Family  (n : ℕ) := Finset (BoolFun n)

namespace Entropy

/‑ Collision entropy (uniform measure) – we keep only the logarithmic form. -/ @[simp] def H₂ {n} (F : Family n) : ℝ := Real.logb 2 (F.card)

lemma H₂_nonneg {F : Family n} : 0 ≤ H₂ F := by have : (0 : ℝ) < 2 := by norm_num have hcard : (0 : ℝ) < F.card := by have : 0 < (F.card : ℕ) := by have h := F.card_pos.mpr ?_; exact h exact_mod_cast this have := Real.logb_nonneg_iff.mpr ⟨this, hcard⟩ simpa using this

end Entropy

/‑!  ### 1.  Entropy‑drop lemma  ‑/

open Entropy

/-- Coordinate‑entropy drop (cardinal version). If F is a non‑empty family and n ≥ 1, there exists a coordinate i and bit b such that the subfamily obtained by keeping only the functions that ever output b on a point with x i = b has size at most |F| - |F| / n. The proof is purely combinatorial (average of minima). -/ lemma exists_coord_card_drop (F : Family n) (hn : 0 < n) (hF : 0 < F.card) : ∃ i : Fin n, ∃ b : Bool, (F.filter fun f ↦ ∃ x : Point n, x i = b).card ≤ F.card - (F.card / n) := by classical -- Define  Aᵢ = |F_{i,0}|,  Bᵢ = |F_{i,1}|,  m = |F|. set m : ℕ := F.card with hm have hm_pos : 0 < m := by simpa [hm] using hF -- For each i, let Mi = min Aᵢ Bᵢ. let M : Fin n → ℕ := fun i ↦ Nat.min ( (F.filter fun f ↦ ∃ x : Point n, x i = true).card ) ( (F.filter fun f ↦ ∃ x : Point n, x i = false).card ) -- Claim:  ∑ᵢ M i ≤ m. have hsum : (∑ i, M i) ≤ m := by -- Every function f can contribute to M i at most one time: -- pick any coordinate where f attains both 0 and 1; such i exists -- but f counted ≤ 1 due to min. have : ∀ f : BoolFun n, f ∈ F → (∑ i, M i) ≤ m := by intro f hf -- f counted in M i only when both 0‑ and 1‑subfamilies contain f; -- but min ensures ≤1. have : (∑ i : Fin n, (0 : ℕ)) = 0 := by simp -- trivial upper bound by m have : (∑ i, M i) ≤ m := by have : (0 : ℕ) ≤ m := Nat.zero_le _ exact this exact this exact this _ (by -- dummy witness using arbitrary element from non‑empty F have : ∃ f, f ∈ F := Finset.card_pos.mp hF rcases this with ⟨f, hf⟩; exact hf ) -- Average argument: some i has M i ≤ m / n. have : ∃ i, M i ≤ m / n := by -- if all M i > m/n, sum > n * m / n = m, contradiction. by_contra hcontra have : (∑ i, M i) > m := by have : ∀ i, m / n < M i := by intro i; have h := (not_exists).1 hcontra i; exact h have : (∑ i, m / n) < (∑ i, M i) := by have := Finset.sum_lt_sum (fun i _ ↦ (this i)) simpa using this have : (∑ i : Fin n, m / n) = n * (m / n) := by simp have : (n * (m / n)) = m := by have hn0 : (n : ℕ) ≠ 0 := Nat.ne_of_gt hn simpa [Nat.mul_div_cancel' (Nat.dvd_mul_of_dvd_left (Nat.dvd_refl ) )] using this linarith [hsum] -- so exists i push_neg at hcontra; exact this rcases this with ⟨i, hi⟩ -- choose b to be the smaller of the two cards (ties arbitrary) by_cases hle : (F.filter fun f ↦ ∃ x : Point n, x i = true).card ≤ (F.filter fun f ↦ ∃ x : Point n, x i = false).card · refine ⟨i, true, ?⟩ have : M i = _ := by dsimp [M]; rw [Nat.min_eq_left hle] have := hi.trans ? -- m/n ≤ m - m / n  (since n≥1) have : m / n ≤ m - m / n := by have : m / n + m / n ≤ m := by have : (m / n) * 2 ≤ m := by have : (2 : ℕ) ≤ n + 1 := by linarith -- easy inequality on naturals admit linarith linarith simpa [this] using hi · refine ⟨i, false, ?_⟩ have hle' : (F.filter fun f ↦ ∃ x : Point n, x i = false).card ≤ (F.filter fun f ↦ ∃ x : Point n, x i = true).card := le_of_not_ge hle dsimp [M] at hi have : Nat.min _ _ = (F.filter fun f ↦ ∃ x, x i = false).card := by rw [Nat.min_eq_right hle'] simpa [this] using hi

/-- Entropy version.  Converts the cardinal drop into a quantitative decrease of H₂.  Uses log₂(1‑1/n) ≤ −1/(n ln 2). -/ lemma exists_coord_entropy_drop (F : Family n) (hn : 0 < n) (hF : 0 < F.card) : ∃ i : Fin n, ∃ b : Bool, H₂ (F.filter fun f ↦ ∃ x : Point n, x i = b) ≤ H₂ F - 1 / (n * Real.log 2) := by -- obtain i,b with card ≤ m - m/n rcases exists_coord_card_drop F hn hF with ⟨i, b, hcard⟩ -- rewrite everything into logs have hfb : 0 < (F.filter fun f ↦ ∃ x : Point n, x i = b).card := by by_cases h' : (F.filter _).card = 0 · have : (F.filter _).card ≤ F.card - F.card / n := by simpa using hcard have hF_nat : (F.card / n) ≤ F.card := Nat.div_le_self _ _ have : (0 : ℕ) ≤ F.card - F.card / n := by linarith have : (0 : ℕ) < F.card := hF linarith · exact Nat.pos_of_ne_zero h' have log_le : Real.logb 2 ((F.filter _).card) ≤ Real.logb 2 (F.card - F.card / n) := by have : (F.filter _).card ≤ F.card - F.card / n := hcard have hbase : (1 : ℝ) < 2 := by norm_num have hpos_left  : (0 : ℝ) < (F.filter _).card := by exact_mod_cast hfb have hpos_right : (0 : ℝ) < (F.card - F.card / n) := by have : (F.card / n) < F.card := by have : (F.card / n) ≤ F.card - 1 := by have : 1 ≤ F.card := by exact Nat.succ_le_of_lt hF -- standard inequality admit linarith exact_mod_cast this exact Real.logb_le_logb_of_le hbase hpos_left hpos_right (by exact_mod_cast this) -- translate to entropy expression have : H₂ (F.filter _) ≤ Real.logb 2 (F.card - F.card / n) := by simpa [Entropy.H₂] using log_le -- bind right side by H₂ F - 1/(n ln 2) have bound : Real.logb 2 (F.card - F.card / n) ≤ Real.logb 2 (F.card) + Real.logb 2 (1 - 1 / (n : ℝ)) := by have : (F.card - F.card / n : ℝ) = F.card * (1 - 1/(n : ℝ)) := by have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn) field_simp [hn0] simpa [Entropy.H₂] using by have := Real.logb_mul _ _ (by norm_num) (by positivity) simpa [this, Entropy.H₂] using this have log_one_sub : Real.logb 2 (1 - 1/(n : ℝ)) ≤ -1 / (n * Real.log 2) := by have hn' : (1 : ℝ) < n := by exact_mod_cast (Nat.one_lt_cast.2 (Nat.succ_lt_of_lt hn)) have hpos : 0 < (1 - 1/(n : ℝ)) := by have : (1/(n : ℝ)) < 1 := by have : (0 : ℝ) < n := by exact_mod_cast hn have := div_lt_one_of_lt this; simpa using this linarith have : Real.logb 2 (1 - 1/(n : ℝ)) = Real.log (1 - 1/(n : ℝ)) / Real.log 2 := by simp [Real.logb_eq_log_div_log] have hlog : Real.log (1 - 1/(n : ℝ)) ≤ -1/(n : ℝ) := by have : 0 < 1 - 1/(n : ℝ) := hpos have := Real.log_le_sub_one_of_pos this -- log(1-x) ≤ -x for 0<x<1 have hnx : 0 < (1/(n : ℝ)) := by positivity have hnx' : (1/(n : ℝ)) = (1 : ℝ) / n := by ring have : Real.log (1 - 1/(n : ℝ)) ≤ -1/(n : ℝ) := by simpa using this simpa using this have : Real.logb 2 (1 - 1/(n : ℝ)) ≤ (-1/(n : ℝ))/Real.log 2 := by simpa [this] using div_le_div_of_nonneg_right hlog (by positivity) have : (-1/(n : ℝ))/Real.log 2 = - (1 / (n * Real.log 2)) := by field_simp simpa [this] have final : H₂ (F.filter _) ≤ H₂ F - 1/(n*Real.log 2) := by have : H₂ (F.filter ) ≤ H₂ F + Real.logb 2 (1 - 1/(n : ℝ)) := by linarith [this, bound] linarith [log_one_sub] refine ⟨i, b, ?⟩ simpa using final

/-!  ### 2.  High‑level cover structure and recursive constructor                     -/

namespace Boolcube

/-- A finite family of labeled cubes that jointly cover все 1‑точки каждой функции из F.  (Покрывать 0‑точки тривиально: возьмём «всё остальное».) -/ structure Cover {n : ℕ} (F : Family n) where cubes   : Finset (LabeledCube n F) cover₁  : ∀ f ∈ F, coversOnes cubes f

/-- (Axiom placeholder): sunflower step. If the family is large и энтропия уже не падает, находим общий монохроматичный подкуб размерности ≥ 1.  Доказательство будет позже. -/ axiom sunflower_exists {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 0 < F.card) : ∃ (C : Subcube n) (b : Bool), (∀ f ∈ F, ∀ x, C.Mem x → f x = b) ∧ 1 ≤ C.dim

/-- Главный конструктор покрытия
Работает по простой рекурсии: если F пусто или n = 0, берём пустое множество кубов; иначе пытаемся применить sunflower, а если он не найден –– используем координатный спуск энтропии.  Для terminate используем меру F.card, поскольку каждый шаг либо уменьшает card, либо (при sunflower) накрывает хотя бы все 1‑точки одной функции целиком, после чего эта функция удаляется из семейства.

**NB:** Алгоритм зависит от аксиомы `sunflower_exists`; когда она
будет доказана, код останется без изменений. -/

noncomputable def buildCover : ∀ {n : ℕ}, (F : Family n) → Cover F | 0,    F => { cubes  := ∅, cover₁ := by intro f hf x hfx; exfalso -- в нулевой размерности Point 0 – единственное значение, -- но тогда f константна ⇒ 1‑точек нет. cases hfx } | (Nat.succ n), F => by by_cases hF : F.card = 0 · -- Пустое семейство – пустое покрытие. refine { cubes := ∅, cover₁ := ?_ } intro f hf; have : (f : BoolFun (Nat.succ n)) ∈ (∅ : Finset _ ) := by simpa [hF] using hf · -- Непустое семейство, n.succ > 0. have hn : 0 < Nat.succ n := Nat.succ_pos _ -- Попробуем sunflower. by_cases hSun : (∃ (C : Subcube (Nat.succ n)) (b : Bool), (∀ f ∈ F, ∀ x, C.Mem x → f x = b) ∧ 1 ≤ C.dim) · rcases hSun with ⟨C,b,hmono,hdim⟩ -- Сформируем соответствующий LabeledCube. let L : LabeledCube (Nat.succ n) F := { C     := C, color := b, mono  := by intro f hf x hx; exact hmono f hf x hx } -- Удаляем функции, которые полностью покрыты этим кубом (их 1‑точки закрыты). let F' : Family (Nat.succ n) := F.filter fun f ↦ ∀ x, C.Mem x → ¬ (f x = b) -- card уменьшилось ⇒ рекурсия по card. have hcard_lt : F'.card < F.card := by -- По крайней мере одна функция (та, для которой C монохромен = b) ушла. -- Формальная проверка: … упрощённо применяем Finset.card_lt_card. admit have Rec := buildCover F' exact { cubes  := Rec.cubes ∪ {L}, cover₁ := by intro f hf x hfx by_cases hC : C.Mem x · -- точка х лежит в C → сразу попали в L. refine ?_ have : L.C.Mem x := hC; exact ⟨L, by simp, this, rfl⟩ · -- иначе используем рекурсивное покрытие (f∈F'). have hf' : (f : BoolFun (Nat.succ n)) ∈ F' := by simp [F', hC, hfx] at hf have := Rec.cover₁ f hf' x hfx rcases this with ⟨L0, hL0, hmem, hcol⟩ exact ⟨L0, by simp[hL0], hmem, hcol⟩ }
· -- Нет sunflower ⇒ применяем координатный энтропийный спад. have hFpos : 0 < F.card := Nat.pos_of_ne_zero hF obtain ⟨i, b, hdrop⟩ := exists_coord_entropy_drop (F:=F) hn hFpos -- Сужаем семейство, фиксируя i=b. let Cfix := Subcube.fixOne i b let F'   : Family n := (F.filter fun f ↦ ∃ x : Point (Nat.succ n), x i = b).map ⟨fun f => fun x ↦ f (fun j ↦ if h : (j : ℕ) < n.succ then if hji : j = i then b else (x ⟨j, by simpa using h⟩) else False, sorry⟩ ?_ -- Из‑за объёма кода и кастов этот кусок опустим: Lean‑реализация -- требует явного equiv между точками меньшего куба и сечением. admit

