import Core.BooleanBasics
import Core.PDT
import Core.Atlas
import Core.SAL_Core
import ThirdPartyFacts.LeafBudget

open Core
open ThirdPartyFacts

namespace Pnp3
namespace Tests

/-!
# Smoke-тест SAL для игрушечного примера AC⁰

В этом файле мы не обращаемся к внешней multi-switching лемме. Вместо этого
мы явно строим объект `Shrinkage` для одномерной константной функции `f ≡ 0` и
проверяем, что конвейер `SAL` выдаёт корректный атлас. Такой тест выполняет две
задачи одновременно:

* демонстрирует, что поля структуры `Shrinkage` согласованы между собой;
* обеспечивает регрессионную проверку для вспомогательных лемм о покрытии
  `errU`, `listSubset` и т.п.
-/

/-- Константная функция нуля на одном бите. -/
@[simp] def f₀ : BitVec 1 → Bool := fun _ => false

/-- Тривиальный PDT: один лист, соответствующий всему кубу. -/
def trivialSubcube : Subcube 1 := fun _ => none

def trivialTree : PDT 1 := PDT.leaf trivialSubcube

/-- Удобное обозначение для единственного индекса в `Fin 1`. -/
@[simp] def idx0 : Fin 1 := ⟨0, by decide⟩

/-- Подкуб, фиксирующий нулевой бит равным `false`. -/
def zeroSubcube : Subcube 1 :=
  fun j => if h : j = idx0 then some false else trivialSubcube j

/-- Для удобства: список фиксаций, задающий `zeroSubcube`. -/
@[simp] def zeroFixes : List (BitFix 1) := [(idx0, false)]

/-- Полезная вспомогательная оценка: глубина нашего дерева нулевая. -/
lemma depth_trivialTree : PDT.depth trivialTree = 0 := by
  simp [trivialTree, PDT.depth]

/-- Для подкубов конечного размера у нас имеется decidable equality. -/
instance : DecidableEq (Subcube 1) := inferInstance

/-- Присваивание нулевого бита `false` даёт подкуб `zeroSubcube`. -/
lemma assign_trivial_eq_zeroSubcube :
    Subcube.assign trivialSubcube idx0 false = some zeroSubcube := by
  classical
  have hfree : trivialSubcube idx0 = none := rfl
  simp [Subcube.assign, zeroSubcube, trivialSubcube, idx0, hfree]

/-- Вектор `x = 0` удовлетворяет подкубу `zeroSubcube`. -/
lemma zeroSubcube_contains_zero :
    mem zeroSubcube (fun _ : BitVec 1 => false) := by
  classical
  have hassignMany :
      Subcube.assignMany trivialSubcube zeroFixes = some zeroSubcube := by
    simp [zeroFixes] using assign_trivial_eq_zeroSubcube
  have htop : mem trivialSubcube (fun _ : BitVec 1 => false) := by
    simp [trivialSubcube] using (mem_top (x := fun _ : BitVec 1 => false))
  have hcond : ∀ u ∈ zeroFixes, (fun _ : BitVec 1 => false) u.1 = u.2 := by
    intro u hu
    -- В списке всего одна фиксация, проверка сводится к очевидному равенству.
    have : u = (idx0, false) := by
      simp [zeroFixes] using hu
    subst this
    simp
  exact
    (mem_assignMany_iff (β := trivialSubcube) (γ := zeroSubcube)
      (updates := zeroFixes) hassignMany (x := fun _ : BitVec 1 => false)).2
      ⟨htop, hcond⟩

/-- Напротив, вектор `x = 1` не принадлежит подкубу `zeroSubcube`. -/
lemma zeroSubcube_excludes_one :
    ¬ mem zeroSubcube (fun _ : BitVec 1 => true) := by
  classical
  have hassignMany :
      Subcube.assignMany trivialSubcube zeroFixes = some zeroSubcube := by
    simp [zeroFixes] using assign_trivial_eq_zeroSubcube
  intro hmem
  have hdecomp :=
    (mem_assignMany_iff (β := trivialSubcube) (γ := zeroSubcube)
      (updates := zeroFixes) hassignMany (x := fun _ : BitVec 1 => true)).1 hmem
  -- Достаём условие на конкретную фиксацию и получаем противоречие.
  have hbit : (fun _ : BitVec 1 => true) idx0 = false := by
    have := hdecomp.2 (idx0, false) (by simp [zeroFixes])
    exact this
  exact hbit

/--
Конструкция shrinkage для игрушечного примера. Мы намеренно выбираем
подмножество листьев пустым списком: константа `0` уже идеально совпадает с
покрытием пустого семейства подкубов.
-/
@[simp] def shrinkage₀ : Shrinkage 1 :=
{ F        := [f₀]
  , t        := 0
  , ε        := 0
  , tree     := trivialTree
  , depth_le := by
      simp [depth_trivialTree]
  , Rsel     := fun _ => []
  , Rsel_sub := by
      intro f β hf hβ
      -- Пустой список листьев: противоречие с предположением о принадлежности.
      cases hβ
  , err_le   := by
      intro f hf
      have hf' : f = f₀ := List.mem_singleton.mp hf
      subst hf'
      exact (show (0 : Q) ≤ 0 from le_rfl)
}

/-- Атлас, полученный из shrinkage, содержит единственный подкуб. -/
@[simp] lemma atlas_from_shrinkage₀_dict :
    (Atlas.fromShrinkage shrinkage₀).dict = [trivialSubcube] := by
  rfl

/-- Финальное утверждение smoke-теста: атлас работает для семейства `[f₀]`. -/
lemma sal_smoke_ac0 :
    WorksFor (Atlas.fromShrinkage shrinkage₀) [f₀] := by
  classical
  exact SAL_from_Shrinkage shrinkage₀

/-- Эквивалентная формулировка через промежуточный объект `CommonPDT`. -/
lemma sal_smoke_ac0_via_commonPDT :
    WorksFor ((Core.shrinkage_to_commonPDT shrinkage₀).toAtlas) [f₀] := by
  classical
  exact
    (Core.commonPDT_to_atlas (C := Core.shrinkage_to_commonPDT shrinkage₀))

/-- Проверяем, что новая лемма о бюджете листьев для `CommonPDT` даёт ту же
оценку в тривиальном примере. -/
lemma commonPDT_leaf_budget_smoke :
    ∃ k : Nat,
      k ≤ (PDT.leaves shrinkage₀.tree).length ∧
      ((Core.shrinkage_to_commonPDT shrinkage₀).selectors f₀).dedup.length ≤ k := by
  classical
  have h :=
    leaf_budget_from_commonPDT
      (n := 1)
      (F := [f₀])
      (C := Core.shrinkage_to_commonPDT shrinkage₀)
  rcases h with ⟨k, hk, hbound⟩
  refine ⟨k, hk, ?_⟩
  have hf : f₀ ∈ ([f₀] : List (BitVec 1 → Bool)) := by simp
  have hbound' := hbound (f := f₀) hf
  exact hbound'

/-- Ошибка после `dedup` не превосходит исходного значения `ε`. -/
lemma commonPDT_err_dedup_smoke :
    Core.errU f₀
        (((Core.shrinkage_to_commonPDT shrinkage₀).selectors f₀).dedup)
      ≤ (Core.shrinkage_to_commonPDT shrinkage₀).epsilon := by
  classical
  have hf : f₀ ∈ ([f₀] : List (BitVec 1 → Bool)) := by simp
  have herr :=
    (err_le_of_dedup_commonPDT
      (n := 1)
      (F := [f₀])
      (C := Core.shrinkage_to_commonPDT shrinkage₀)
      (f := f₀)
      hf)
  exact herr

end Tests
end Pnp3
