import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Core.SAL_Core
import Core.BooleanBasics

/-!
  pnp3/ThirdPartyFacts/LeafBudget.lean

  Этот модуль отвечает за извлечение **единой** верхней границы на число листьев,
  используемых для аппроксимации каждой функции из shrinkage-семейства.  В новой
  версии мы делаем два ключевых улучшения по сравнению с предыдущей итерацией:

  * убираем повторы листьев в выборе `Rsel f` (через `List.dedup`), не меняя
    при этом ошибку аппроксимации;
  * ограничиваем длину очищенных списков простым и прозрачным числом —
    `|leaves(tree)|`, то есть количеством листьев PDT.

  Благодаря этому сценарии SAL → Covering-Power могут оперировать конкретной
  численной оценкой `k`, а не абстрактным максимумом по семейству.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

namespace Aux

variable {α : Type*}

/--
  Если каждый элемент списка `xs` встречается в `ys`, то после удаления
  дубликатов длина `xs` не превосходит длину `ys`.  Доказательство основано на
  переводе обоих списков в `Finset`: включение множеств даёт оценку кардиналов,
  а `List.dedup` гарантирует, что кардинал `xs.toFinset` совпадает с длиной
  очищенного списка `xs.dedup`.
-/
lemma dedup_length_le_of_subset [DecidableEq α]
    {xs ys : List α} (h : Core.listSubset xs ys) :
    xs.dedup.length ≤ ys.length := by
  classical
  have hsubset : xs.toFinset ⊆ ys.toFinset := by
    intro a ha
    -- переводим принадлежность `Finset` обратно в список
    have hmem : a ∈ xs := (List.mem_toFinset.mp ha)
    have hcontains : xs.contains a = true :=
      Core.contains_of_mem (xs := xs) hmem
    have hycontains := h a hcontains
    have hymem : a ∈ ys := Core.mem_of_contains (xs := ys) hycontains
    exact List.mem_toFinset.mpr hymem
  have hcard_le : xs.toFinset.card ≤ ys.toFinset.card :=
    Finset.card_le_card hsubset
  have hxcard : xs.toFinset.card = xs.dedup.length := by
    change xs.toFinset.1.card = xs.dedup.length
    simp [List.toFinset_val]
  have hycard : ys.toFinset.card = ys.dedup.length := by
    change ys.toFinset.1.card = ys.dedup.length
    simp [List.toFinset_val]
  have hy_le : ys.dedup.length ≤ ys.length :=
    (List.dedup_sublist (l := ys)).length_le
  have hx_le : xs.dedup.length ≤ ys.toFinset.card := by
    have hcard_le' := hcard_le
    -- заменяем кардинал `Finset` на длину очищенного списка
    rw [hxcard] at hcard_le'
    exact hcard_le'
  have hy_bound : ys.toFinset.card ≤ ys.length := by
    have hy_le' := hy_le
    -- подменяем левую часть на кардинал `Finset`
    rw [← hycard] at hy_le'
    exact hy_le'
  exact hx_le.trans hy_bound

end Aux

/-
  На уровне `CommonPDT` удобно формулировать границу листьев без привязки к
  конкретному shrinkage-сертификату.  Мы сразу переходим к этой более общей
  версии: для любого общего PDT длина очищенных списков селекторов не превосходит
  числа листьев дерева.
-/
theorem leaf_budget_from_commonPDT {n : Nat}
    [DecidableEq (Core.Subcube n)] {F : Core.Family n}
    (C : Core.CommonPDT n F) :
    ∃ k : Nat,
      k ≤ (Core.PDT.leaves C.tree).length ∧
      ∀ {f : Core.BitVec n → Bool},
        f ∈ F → ((C.selectors f).dedup).length ≤ k := by
  classical
  refine ⟨(Core.PDT.leaves C.tree).length, ?_⟩
  refine And.intro ?_ ?_
  · exact le_rfl
  · intro f hf
    have hsubset : Core.listSubset (C.selectors f) (Core.PDT.leaves C.tree) := by
      refine Core.listSubset_of_mem ?_
      intro β hβ
      exact C.selectors_sub (F := F) (f := f) (β := β) hf hβ
    have hbound := Aux.dedup_length_le_of_subset (xs := C.selectors f)
      (ys := Core.PDT.leaves C.tree) hsubset
    exact hbound

/--
  Обратно к shrinkage сертификату: подставляем извлечённый `CommonPDT` и
  получаем точь-в-точь прежнюю формулировку для `S.Rsel`.
-/
theorem leaf_budget_from_shrinkage {n : Nat}
    [DecidableEq (Subcube n)] (S : Core.Shrinkage n) :
    ∃ k : Nat,
      k ≤ (Core.PDT.leaves S.tree).length ∧
      ∀ {f : Core.BitVec n → Bool},
        f ∈ S.F → ((S.Rsel f).dedup).length ≤ k := by
  classical
  obtain ⟨k, hk₁, hk₂⟩ :=
    (leaf_budget_from_commonPDT (n := n) (F := S.F) (C := S.commonPDT))
  refine ⟨k, ?_, ?_⟩
  · have hk₁'' : k ≤ (Core.PDT.leaves S.tree).length := by
      calc
        k ≤ (Core.PDT.leaves S.commonPDT.tree).length := hk₁
        _ = (Core.PDT.leaves S.tree).length := by
              simp [Core.Shrinkage.commonPDT_tree]
    exact hk₁''
  · intro f hf
    have hk₂' : ((S.Rsel f).dedup).length ≤ k := by
      calc
        ((S.Rsel f).dedup).length
            = ((S.commonPDT.selectors f).dedup).length := by
                  simp [Core.Shrinkage.commonPDT_selectors]
        _ ≤ k := by
              exact hk₂ hf
    exact hk₂'

/--
  Очищение списка листьев не ухудшает ошибку аппроксимации.  Сначала доказываем
  это утверждение для `CommonPDT`.
-/
lemma err_le_of_dedup_commonPDT {n : Nat}
    [DecidableEq (Core.Subcube n)] {F : Core.Family n}
    (C : Core.CommonPDT n F) {f : Core.BitVec n → Bool} (hf : f ∈ F) :
  Core.errU f ((C.selectors f).dedup) ≤ C.epsilon := by
  classical
  -- Сравниваем ошибки напрямую через цепочку равенств/неравенств.
  have h := C.err_le (F := F) (f := f) hf
  calc
    Core.errU f ((C.selectors f).dedup)
        = Core.errU f (C.selectors f) :=
            Core.errU_dedup (f := f) (R := C.selectors f)
    _ ≤ C.epsilon := h

/-- Версия предыдущего утверждения, специализированная под shrinkage. -/
lemma err_le_of_dedup {n : Nat} [DecidableEq (Subcube n)]
    (S : Core.Shrinkage n) {f : Core.BitVec n → Bool} (hf : f ∈ S.F) :
  Core.errU f ((S.Rsel f).dedup) ≤ S.ε := by
  have h :=
    (err_le_of_dedup_commonPDT (C := S.commonPDT) (F := S.F) (f := f) hf)
  have h' := h
  -- Автоматически переписываем селекторы и ε через shrinkage-поля.
  simp at h'
  exact h'

/--
  Корреляция с оценкой на число листьев: полученную границу можно сразу
  переписать через глубину PDT, применив стандартную оценку `|leaves| ≤ 2^t`.
-/
lemma leaf_budget_le_pow_depth_commonPDT {n : Nat}
    [DecidableEq (Core.Subcube n)] {F : Core.Family n}
    (C : Core.CommonPDT n F) :
    ∀ {f : Core.BitVec n → Bool},
      f ∈ F →
        ((C.selectors f).dedup).length ≤ Nat.pow 2 C.depthBound := by
  classical
  intro f hf
  obtain ⟨k, hk⟩ := leaf_budget_from_commonPDT (n := n)
    (F := F) (C := C)
  have hlen' := hk.2 hf
  have hdepth :
      (Core.PDT.leaves C.tree).length ≤ Nat.pow 2 (Core.PDT.depth C.tree) := by
    exact Core.leaves_count_bound (t := C.tree)
  have hdepthBound : Nat.pow 2 (Core.PDT.depth C.tree)
      ≤ Nat.pow 2 C.depthBound :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) C.depth_le
  exact hlen'.trans (hk.1.trans (hdepth.trans hdepthBound))

/-- Специализация оценки на случай shrinkage. -/
lemma leaf_budget_le_pow_depth {n : Nat} [DecidableEq (Subcube n)]
    (S : Core.Shrinkage n) :
    ∀ {f : Core.BitVec n → Bool},
      f ∈ S.F →
        ((S.Rsel f).dedup).length ≤ Nat.pow 2 S.t := by
  classical
  intro f hf
  have h :=
    leaf_budget_le_pow_depth_commonPDT
      (n := n) (F := S.F) (C := S.commonPDT) (f := f) hf
  have h' := h
  simp at h'
  exact h'

end ThirdPartyFacts
end Pnp3
