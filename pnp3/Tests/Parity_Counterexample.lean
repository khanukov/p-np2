import Mathlib.Algebra.Order.Field.Basic
import Core.SAL_Core
import ThirdPartyFacts.LeafBudget

/-!
# Тест: семейство паритетов как контрпример

Здесь мы доказываем, что семейство из двух функций `{parity, ¬ parity}`
на одном бите **не** удовлетворяет заключению шага A без привлечения
shrinkage-леммы.  Частичное решающее дерево глубины `0` обладает лишь
одним листом (подкубом), и такой словарь не способен одновременно
аппроксимировать паритет и его отрицание с ошибкой < `1/2`.

Далее разворачиваем это рассуждение в Lean.  Вместо фиктивной аксиомы
появляется конкретная теорема, запрещающая существование общего PDT
глубины `0` с малой ошибкой для паритета.
-/

namespace Pnp3
namespace Tests

open Core

noncomputable section

/-!
## Базовые определения

Работаем с `BitVec 1 = Fin 1 → Bool`.  Возможны лишь два вектора:
`x₀`, всегда равный `false`, и `x₁`, всегда равный `true`.  Для
удобства обозначим единственный индекс `Fin 1` как `idx`.
-/

@[simp] def idx : Fin 1 := ⟨0, by decide⟩

/-- Константный нулевой вектор. -/
def x₀ : BitVec 1 := fun _ => false

/-- Константный единичный вектор. -/
def x₁ : BitVec 1 := fun _ => true

/-- Паритет на одном бите — просто чтение бита. -/
def parity₁ (x : BitVec 1) : Bool := x idx

/-- Отрицание паритета. -/
def parity₁ᶜ (x : BitVec 1) : Bool := ! parity₁ x

@[simp] lemma parity₁_x₀ : parity₁ x₀ = false := by simp [parity₁, x₀, idx]
@[simp] lemma parity₁_x₁ : parity₁ x₁ = true := by simp [parity₁, x₁, idx]
@[simp] lemma parity₁ᶜ_x₀ : parity₁ᶜ x₀ = true := by simp [parity₁ᶜ]
@[simp] lemma parity₁ᶜ_x₁ : parity₁ᶜ x₁ = false := by simp [parity₁ᶜ]

/-- Наше семейство функций: паритет и его отрицание. -/
def parityFamily : Family 1 := [parity₁, parity₁ᶜ]

@[simp] lemma parity_mem_family : parity₁ ∈ parityFamily := by simp [parityFamily]
@[simp] lemma parityᶜ_mem_family : parity₁ᶜ ∈ parityFamily := by simp [parityFamily]

/-!
## Комбинаторика на `BitVec 1`

Финитное множество всех бит-векторов длины `1` состоит из `x₀` и `x₁`.
Это удобно зафиксировать, чтобы затем явно вычислять мощности фильтров.
-/

@[simp] lemma univ_bitvec1 :
    (Finset.univ : Finset (BitVec 1)) = {x₀, x₁} := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro _
    -- Любой элемент универсума равен либо `x₀`, либо `x₁`.
    have hx : x = x₀ ∨ x = x₁ := by
      cases h : x idx with
      | false =>
          left
          funext i
          have hi : i = idx := Subsingleton.elim _ _
          simpa [x₀, hi, h]
      | true =>
          right
          funext i
          have hi : i = idx := Subsingleton.elim _ _
          simpa [x₁, hi, h]
    cases hx with
    | inl h => simpa [h]
    | inr h => simpa [h]
  · intro hx; simpa [hx]

/-!
## Ошибка аппроксимации

Вычислим ошибку `errU` для пустого словаря и для словаря из одного
подкуба.  Эти значения понадобятся при анализе возможных селекторов в
`CommonPDT`.
-/

lemma err_parity_nil :
    errU parity₁ ([] : List (Subcube 1)) = (1 : Q) / 2 := by
  classical
  unfold errU
  have :
      ((Finset.univ : Finset (BitVec 1)).filter
        fun x => parity₁ x ≠ coveredB ([] : List (Subcube 1)) x).card = 1 := by
    simp [univ_bitvec1, coveredB_nil]
  simp [this, univ_bitvec1]

lemma err_parityᶜ_nil :
    errU parity₁ᶜ ([] : List (Subcube 1)) = (1 : Q) / 2 := by
  classical
  unfold errU
  have :
      ((Finset.univ : Finset (BitVec 1)).filter
        fun x => parity₁ᶜ x ≠ coveredB ([] : List (Subcube 1)) x).card = 1 := by
    simp [univ_bitvec1, coveredB_nil]
  simp [this, univ_bitvec1]

/-!
Следующая лемма перебирает все возможные подкубы `β : Subcube 1`.
Поскольку индекс всего один, достаточно посмотреть на `β idx`.
-/

lemma err_singleton_cases (β : Subcube 1) :
    (errU parity₁ [β], errU parity₁ᶜ [β]) =
      match β idx with
      | none      => ((1 : Q) / 2, (1 : Q) / 2)
      | some false => (1, 0)
      | some true  => (0, 1) := by
  classical
  cases hβ : β idx with
  | none =>
      have hcov : ∀ x, coveredB [β] x = true := by
        intro x
        have : ∀ i : Fin 1, ∀ b : Bool, β i = some b → x i = b := by
          intro i b hi
          have hi' : i = idx := Subsingleton.elim _ _
          subst hi'
          simpa [hβ] using hi
        have hmem := (memB_eq_true_iff (β := β) (x := x)).2 this
        simpa [coveredB, hmem]
      have hfilter₁ :
          ((Finset.univ : Finset (BitVec 1)).filter
              fun x => parity₁ x ≠ coveredB [β] x).card = 1 := by
        simp [univ_bitvec1, hcov]
      have hfilter₂ :
          ((Finset.univ : Finset (BitVec 1)).filter
              fun x => parity₁ᶜ x ≠ coveredB [β] x).card = 1 := by
        simp [univ_bitvec1, hcov]
      simp [errU, hfilter₁, hfilter₂, hβ, univ_bitvec1]
  | some b =>
      have hcov : ∀ x, coveredB [β] x = (x idx = b) := by
        intro x
        have : (memB β x = true) ↔ x idx = b := by
          constructor
          · intro h
            have hx := (memB_eq_true_iff (β := β) (x := x)).1 h idx b
            simpa [hβ]
          · intro hx
            have hxprop : ∀ i : Fin 1, ∀ c : Bool, β i = some c → x i = c := by
              intro i c hi
              have hi' : i = idx := Subsingleton.elim _ _
              subst hi'
              have hc : c = b := by simpa [hβ] using hi
              simpa [hc, hx]
            exact (memB_eq_true_iff (β := β) (x := x)).2 hxprop
        by_cases hx : x idx = b
        · have := (this.mpr hx)
          simp [coveredB, this, hx]
        · have hx' : memB β x ≠ true := by
            intro h
            exact hx ((this.mp h))
          cases hmem : memB β x <;> simp [coveredB, hmem, hx, hx']
      cases b
      · have hfilter₁ :
            ((Finset.univ : Finset (BitVec 1)).filter
                fun x => parity₁ x ≠ coveredB [β] x).card = 2 := by
            simp [univ_bitvec1, hcov, idx]
        have hfilter₂ :
            ((Finset.univ : Finset (BitVec 1)).filter
                fun x => parity₁ᶜ x ≠ coveredB [β] x).card = 0 := by
            simp [univ_bitvec1, hcov, idx]
        simp [errU, hfilter₁, hfilter₂, hβ, univ_bitvec1]
      · have hfilter₁ :
            ((Finset.univ : Finset (BitVec 1)).filter
                fun x => parity₁ x ≠ coveredB [β] x).card = 0 := by
            simp [univ_bitvec1, hcov, idx]
        have hfilter₂ :
            ((Finset.univ : Finset (BitVec 1)).filter
                fun x => parity₁ᶜ x ≠ coveredB [β] x).card = 2 := by
            simp [univ_bitvec1, hcov, idx]
        simp [errU, hfilter₁, hfilter₂, hβ, univ_bitvec1]

/-!
## Нормальная форма селекторов

Если список `xs` содержится в `[β]`, то его очищенная версия (`dedup`)
равна либо `[]`, либо `[β]`.  Это позволит рассматривать только две
конфигурации листьев.
-/

lemma dedup_subset_singleton [DecidableEq (Subcube 1)]
    {xs : List (Subcube 1)} {β : Subcube 1}
    (h : listSubset xs [β]) :
    xs.dedup = [] ∨ xs.dedup = [β] := by
  classical
  have hsubset := listSubset_dedup (xs := xs) (ys := [β]) h
  have hx : ∀ γ ∈ xs.dedup, γ = β := by
    intro γ hγ
    have : γ ∈ [β] := listSubset.mem hsubset hγ
    simpa using this
  have hlen_le : xs.dedup.length ≤ 1 := by
    simpa using
      (ThirdPartyFacts.Aux.dedup_length_le_of_subset
        (xs := xs) (ys := [β]) h)
  cases hxlen : xs.dedup.length with
  | zero =>
      left
      apply List.length_eq_zero.mp
      simpa [hxlen]
  | succ n =>
      have hle : Nat.succ n ≤ Nat.succ 0 := by
        simpa [hxlen] using hlen_le
      have hn0 : n = 0 := by
        have : n ≤ 0 := Nat.succ_le_succ_iff.mp hle
        exact Nat.le_antisymm this (Nat.zero_le _)
      have hxone : xs.dedup.length = 1 := by simpa [hxlen, hn0]
      rcases (List.length_eq_one.mp hxone) with ⟨γ, hγ⟩
      right
      have : γ = β := by
        have hmem : γ ∈ xs.dedup := by simpa [hγ]
        exact hx _ hmem
      simpa [hγ, this]

/-!
## Главный результат

Покажем, что не существует общего PDT глубины `0` с ошибкой `< 1/2`
для семейства `{parity, ¬ parity}`.
-/

theorem parity_counterexample :
    ¬ ∃ (C : CommonPDT 1 parityFamily),
        C.depthBound = 0 ∧ C.epsilon < (1 : Q) / 2 := by
  classical
  intro h
  rcases h with ⟨C, hdepth, hεlt⟩
  -- Глубина дерева ≤ 0 ⇒ само дерево — лист.
  have hdepth' : PDT.depth C.tree = 0 := by
    have := C.depth_le
    have hzero : 0 ≤ PDT.depth C.tree := Nat.zero_le _
    have hle : PDT.depth C.tree ≤ 0 := by simpa [hdepth]
      using this
    exact Nat.le_antisymm hle hzero
  cases htree : C.tree with
  | leaf β =>
      -- Словарь состоит ровно из одного подкуба β.
      have hdict : C.toAtlas.dict = [β] := by
        simp [CommonPDT.toAtlas, Atlas.ofPDT, htree]
      -- Свойства селекторов паритета и его отрицания.
      have hsubset_parity : listSubset (C.selectors parity₁) [β] := by
        intro γ hγ
        have := C.selectors_sub (F := parityFamily)
          (f := parity₁) (β := γ) parity_mem_family
          (Core.mem_of_contains hγ)
        simpa [htree] using this
      have hsubset_parityᶜ : listSubset (C.selectors parity₁ᶜ) [β] := by
        intro γ hγ
        have := C.selectors_sub (F := parityFamily)
          (f := parity₁ᶜ) (β := γ) parityᶜ_mem_family
          (Core.mem_of_contains hγ)
        simpa [htree] using this
      have hdedup_parity := dedup_subset_singleton
        (xs := C.selectors parity₁) (β := β) hsubset_parity
      have hdedup_parityᶜ := dedup_subset_singleton
        (xs := C.selectors parity₁ᶜ) (β := β) hsubset_parityᶜ
      have herr_parity := C.err_le (F := parityFamily)
        (f := parity₁) parity_mem_family
      have herr_parityᶜ := C.err_le (F := parityFamily)
        (f := parity₁ᶜ) parityᶜ_mem_family
      -- Перебираем варианты очищенных списков.
      cases hdedup_parity with
      | inl hnil =>
          have : (1 : Q) / 2 ≤ C.epsilon := by
            simpa [hnil, hdict, err_parity_nil,
              CommonPDT.toAtlas, Atlas.ofPDT, htree]
              using herr_parity
          exact (not_lt_of_ge this) hεlt
      | inr hsingle =>
          cases hdedup_parityᶜ with
          | inl hnilᶜ =>
              have : (1 : Q) / 2 ≤ C.epsilon := by
                simpa [hnilᶜ, hdict, err_parityᶜ_nil,
                  CommonPDT.toAtlas, Atlas.ofPDT, htree]
                  using herr_parityᶜ
              exact (not_lt_of_ge this) hεlt
          | inr hsingleᶜ =>
              have herr_pair := err_singleton_cases β
              have herr_eq_parity :
                  errU parity₁ (C.selectors parity₁) = errU parity₁ [β] := by
                simpa [hsingle] using
                  (Core.errU_dedup (f := parity₁)
                    (R := C.selectors parity₁)).symm
              have herr_eq_parityᶜ :
                  errU parity₁ᶜ (C.selectors parity₁ᶜ)
                    = errU parity₁ᶜ [β] := by
                simpa [hsingleᶜ] using
                  (Core.errU_dedup (f := parity₁ᶜ)
                    (R := C.selectors parity₁ᶜ)).symm
              cases hβ : β idx with
              | none =>
                  have hle : errU parity₁ [β] ≤ C.epsilon := by
                    simpa [herr_eq_parity] using herr_parity
                  have hfst := congrArg Prod.fst herr_pair
                  have hge : (1 : Q) / 2 ≤ C.epsilon := by
                    simpa [hβ] using (hfst ▸ hle)
                  exact (not_lt_of_ge hge) hεlt
              | some b =>
                  cases b
                  · -- β фиксирует 0 ⇒ ошибка паритета = 1.
                    have hle : errU parity₁ [β] ≤ C.epsilon := by
                      simpa [herr_eq_parity] using herr_parity
                    have hfst := congrArg Prod.fst herr_pair
                    have hge : (1 : Q) ≤ C.epsilon := by
                      simpa [hβ] using (hfst ▸ hle)
                    have hlt := lt_of_le_of_lt hge hεlt
                    have : ¬ (1 : Q) < (1 : Q) / 2 := by norm_num
                    exact this hlt
                  · -- β фиксирует 1 ⇒ ошибка отрицания паритета = 1.
                    have hle : errU parity₁ᶜ [β] ≤ C.epsilon := by
                      simpa [herr_eq_parityᶜ] using herr_parityᶜ
                    have hsnd := congrArg Prod.snd herr_pair
                    have hge : (1 : Q) ≤ C.epsilon := by
                      simpa [hβ] using (hsnd ▸ hle)
                    have hlt := lt_of_le_of_lt hge hεlt
                    have : ¬ (1 : Q) < (1 : Q) / 2 := by norm_num
                    exact this hlt
  | node i t₀ t₁ =>
      -- Узел имеет положительную глубину — противоречие с `depth = 0`.
      have : False := by
        have := congrArg PDT.depth htree
        simpa [PDT.depth, hdepth'] using this
      exact this.elim

end

end Tests
end Pnp3
