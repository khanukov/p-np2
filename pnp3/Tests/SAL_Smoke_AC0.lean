/--
# Smoke-тест SAL для игрушечного примера AC⁰

В этом файле мы не обращаемся к внешней multi-switching лемме. Вместо этого
мы явно строим объект `Shrinkage` для одномерной константной функции `f ≡ 0` и
проверяем, что конвейер `SAL` выдаёт корректный атлас. Такой тест выполняет две
задачи одновременно:

* демонстрирует, что поля структуры `Shrinkage` согласованы между собой;
* обеспечивает регрессионную проверку для вспомогательных лемм о покрытии
  `errU`, `listSubset` и т.п.
-/
import PnP3.Core.BooleanBasics
import PnP3.Core.PDT
import PnP3.Core.Atlas
import PnP3.Core.SAL_Core

open PnP3.Core

namespace PnP3.Tests

/-- Константная функция нуля на одном бите. -/
@[simp] def f₀ : BitVec 1 → Bool := fun _ => false

/-- Тривиальный PDT: один лист, соответствующий всему кубу. -/
def trivialSubcube : Subcube 1 := fun _ => none

def trivialTree : PDT 1 := PDT.leaf trivialSubcube

/-- Полезная вспомогательная оценка: глубина нашего дерева нулевая. -/
lemma depth_trivialTree : PDT.depth trivialTree = 0 := by
  simp [trivialTree, PDT.depth]

/-- Для подкубов конечного размера у нас имеется decidable equality. -/
instance : DecidableEq (Subcube 1) := inferInstance

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
  , depth_le := by simpa [depth_trivialTree]
  , Rsel     := fun _ => []
  , Rsel_sub := by
      intro f hf
      simp [listSubset]
  , err_le   := by
      intro f hf
      have hf' : f = f₀ := by simpa using hf
      subst hf'
      simpa using (show (0 : Q) ≤ 0 from le_rfl)
}

/-- Атлас, полученный из shrinkage, содержит единственный подкуб. -/
@[simp] lemma atlas_from_shrinkage₀_dict :
    (Atlas.fromShrinkage shrinkage₀).dict = [trivialSubcube] := by
  rfl

/-- Финальное утверждение smoke-теста: атлас работает для семейства `[f₀]`. -/
lemma sal_smoke_ac0 :
    WorksFor (Atlas.fromShrinkage shrinkage₀) [f₀] := by
  classical
  simpa using SAL_from_Shrinkage shrinkage₀

end PnP3.Tests
