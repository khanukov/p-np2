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
    have hmem : a ∈ xs := by
      simpa [List.mem_toFinset] using ha
    have hcontains : xs.contains a = true :=
      Core.contains_of_mem (xs := xs) hmem
    have hycontains := h a hcontains
    have hymem : a ∈ ys := Core.mem_of_contains (xs := ys) hycontains
    simpa [List.mem_toFinset] using hymem
  have hcard_le : xs.toFinset.card ≤ ys.toFinset.card :=
    Finset.card_le_card hsubset
  have hxcard : xs.toFinset.card = xs.dedup.length := by
    change xs.toFinset.1.card = xs.dedup.length
    simpa [List.toFinset_val]
  have hycard : ys.toFinset.card = ys.dedup.length := by
    change ys.toFinset.1.card = ys.dedup.length
    simpa [List.toFinset_val]
  have hy_le : ys.dedup.length ≤ ys.length :=
    (List.dedup_sublist (l := ys)).length_le
  have hx_le : xs.dedup.length ≤ ys.toFinset.card := by
    simpa [hxcard] using hcard_le
  have hy_bound : ys.toFinset.card ≤ ys.length := by
    simpa [hycard] using hy_le
  exact hx_le.trans hy_bound

end Aux

/--
  Для любого shrinkage сертификата можно выбрать единую границу `k`, равную
  количеству листьев PDT, так что очищенные (без дубликатов) списки листьев не
  длиннее `k`.
-/
theorem leaf_budget_from_shrinkage {n : Nat}
    [DecidableEq (Subcube n)] (S : Core.Shrinkage n) :
    ∃ k : Nat,
      k ≤ (Core.PDT.leaves S.tree).length ∧
      ∀ {f : Core.BitVec n → Bool},
        f ∈ S.F → ((S.Rsel f).dedup).length ≤ k := by
  classical
  refine ⟨(Core.PDT.leaves S.tree).length, ?_⟩
  refine And.intro ?_ ?_
  · exact le_rfl
  · intro f hf
    have hsubset := S.Rsel_sub f hf
    have hbound := Aux.dedup_length_le_of_subset (xs := S.Rsel f)
      (ys := Core.PDT.leaves S.tree) hsubset
    simpa using hbound

/--
  Очищение списка листьев не ухудшает ошибку аппроксимации.  Удобная форма для
  дальнейших сценариев: можно заменить `S.Rsel f` на `S.Rsel f`.dedup, сохранив
  ту же погрешность.
-/
lemma err_le_of_dedup {n : Nat} [DecidableEq (Subcube n)]
    (S : Core.Shrinkage n) {f : Core.BitVec n → Bool} (hf : f ∈ S.F) :
  Core.errU f ((S.Rsel f).dedup) ≤ S.ε := by
  classical
  -- Сравниваем ошибки напрямую через цепочку равенств/неравенств.
  have h := S.err_le f hf
  calc
    Core.errU f ((S.Rsel f).dedup)
        = Core.errU f (S.Rsel f) := Core.errU_dedup (f := f) (R := S.Rsel f)
    _ ≤ S.ε := h

/--
  Корреляция с оценкой на число листьев: полученную границу можно сразу
  переписать через глубину PDT, применив стандартную оценку `|leaves| ≤ 2^t`.
-/
lemma leaf_budget_le_pow_depth {n : Nat} [DecidableEq (Subcube n)]
    (S : Core.Shrinkage n) :
    ∀ {f : Core.BitVec n → Bool},
      f ∈ S.F →
        ((S.Rsel f).dedup).length ≤ Nat.pow 2 S.t := by
  classical
  intro f hf
  obtain ⟨k, hk⟩ := leaf_budget_from_shrinkage (n := n) S
  have hlen' := hk.2 hf
  have hdepth :
      (Core.PDT.leaves S.tree).length ≤ Nat.pow 2 S.t := by
    exact (Core.leaves_count_bound (t := S.tree)).trans
      (Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) S.depth_le)
  exact hlen'.trans (hk.1.trans hdepth)

end ThirdPartyFacts
end Pnp3
