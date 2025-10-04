import Core.SAL_Core

/-!
  pnp3/ThirdPartyFacts/LeafBudget.lean

  В этом модуле мы фиксируем "внешний" факт о равномерной границе
  на число листьев, используемых в Shrinkage-конструкции.  Multi-switching
  леммы (Servedio–Tan, Håstad и др.) гарантируют, что существует глобальное
  число `k`, ограничивающее длину списков `Rsel f` для всех функций из
  семейства.  Нам достаточно интерфейса этого факта, поэтому формализуем его
  как Lean-аксиому: позднее её можно заменить на доказательство или импорт
  из полноценной библиотеки.

  Эта граница служит ключевым мостиком между SAL и ёмкостными оценками:
  зная общий `k`, мы сможем автоматически строить `BoundedAtlasScenario`
  и запускать Covering-Power.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

/--
  Внешний факт (аксиома): для любого сертификата shrinkage существует
  одно и то же натуральное число `k`, ограничивающее длину списков `Rsel f`
  для всех `f ∈ S.F`.  На практике `k = O(t * log(1/ε))`, но для конвейера
  нижних оценок нам важно лишь само существование такого ограничения.
-/
axiom leaf_budget_from_shrinkage {n : Nat} [DecidableEq (Subcube n)]
    (S : Core.Shrinkage n) :
    ∃ k : Nat, ∀ {f : Core.BitVec n → Bool}, f ∈ S.F → (S.Rsel f).length ≤ k

end ThirdPartyFacts
end Pnp3
