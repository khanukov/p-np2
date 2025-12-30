/-
  pnp3/Core/PDTPartial.lean

  Частичные PDT: общий "ствол" и локальные хвосты для каждого листа.
  Эти структуры удобны при формализации multi-switching лемм: сначала
  строим общее дерево, после чего каждый лист уточняется отдельным
  небольшим решающим деревом.
-/
import Mathlib.Data.List.Basic
import Core.PDT

namespace Pnp3
namespace Core

/--
`PartialDT n ℓ` хранит общий "ствол" PDT на `n` переменных и для каждого листа
предоставляет хвост глубины ≤ `ℓ`.  Структура включает функцию `tails`, которая
по листу возвращает уточняющее дерево, и доказательство ограничения глубины
для каждого хвоста.  В дальнейшем сюда можно добавить дополнительные инварианты
(например, согласованность хвостов по листьям).
-/
structure PartialDT (n ℓ : Nat) where
  trunk : PDT n
  tails : ∀ β, β ∈ PDT.leaves trunk → PDT n
  tail_depth_le : ∀ β hβ, PDT.depth (tails β hβ) ≤ ℓ

namespace PartialDT

variable {n ℓ : Nat}

/--
Из обычного PDT можно получить частичное дерево с нулевой глубиной хвостов.
Это полезно для адаптации существующих shrinkage-сертификатов и служит простым
источником тестовых примеров.
-/
def ofPDT (t : PDT n) : PartialDT n 0 where
  trunk := t
  tails := fun β _ => PDT.leaf β
  tail_depth_le := by
    intro β hβ
    -- глубина листа равна нулю
    simp [PDT.depth]

/--
Словарь частичного PDT — просто список листьев его ствола.  Выделяем
это определение отдельно, чтобы единообразно говорить о длине словаря
и применять существующие оценки на число листьев.
-/
@[simp] def leafDict (Q : PartialDT n ℓ) : List (Subcube n) :=
  PDT.leaves Q.trunk

/--
«Реализация» частичного PDT в полноценное дерево решений: раскрываем
все хвосты с помощью операции `PDT.refine`.-/
def realize (Q : PartialDT n ℓ) : PDT n :=
  PDT.refine Q.trunk Q.tails

/-- Реализация тривиального частичного дерева возвращает исходное PDT. -/
@[simp] lemma realize_ofPDT (t : PDT n) :
    (PartialDT.ofPDT t).realize = t := by
  induction t with
  | leaf β =>
      simp [PartialDT.realize, PartialDT.ofPDT, PDT.refine]
  | node i t0 t1 ih0 ih1 =>
      have hleft : PDT.refine t0 (fun β _ => PDT.leaf β) = t0 := by
        have htmp := ih0
        simp [PartialDT.realize, PartialDT.ofPDT] at htmp
        exact htmp
      have hright : PDT.refine t1 (fun β _ => PDT.leaf β) = t1 := by
        have htmp := ih1
        simp [PartialDT.realize, PartialDT.ofPDT] at htmp
        exact htmp
      calc
        (PartialDT.ofPDT (PDT.node i t0 t1)).realize
            = PDT.node i (PDT.refine t0 (fun β _ => PDT.leaf β))
                (PDT.refine t1 (fun β _ => PDT.leaf β)) := by
              simp [PartialDT.realize, PartialDT.ofPDT, PDT.refine]
        _ = PDT.node i t0 (PDT.refine t1 (fun β _ => PDT.leaf β)) := by
              simp [hleft]
        _ = PDT.node i t0 t1 := by
              simp [hright]

/-- Глубина реализованного дерева ограничена глубиной ствола плюс `ℓ`. -/
lemma depth_realize_le (Q : PartialDT n ℓ) :
    PDT.depth (Q.realize) ≤ PDT.depth Q.trunk + ℓ := by
  have h := PDT.depth_refine_le
    (t := Q.trunk) (tails := Q.tails) (ℓ := ℓ) (htails := Q.tail_depth_le)
  exact h

/--
  Глубина реализованного дерева не меньше глубины ствола.  Это комплементарная
  оценка к `depth_realize_le` и удобна при индукционных «склейках» деревьев:
  ствол никогда не «схлопывается» при уточнении хвостами.
-/
lemma depth_trunk_le_realize (Q : PartialDT n ℓ) :
    PDT.depth Q.trunk ≤ PDT.depth Q.realize := by
  -- Это прямое следствие монотонности уточнения (`PDT.depth_refine_ge`).
  simpa [PartialDT.realize] using
    (PDT.depth_refine_ge (t := Q.trunk) (tails := Q.tails))

/--
Число листьев частичного PDT не превосходит `2 ^ depth(trunk)`.  Это
непосредственно следует из оценки для обычных PDT и понадобится при
связке шага A (усадка) с шагом B (Covering/Leaf Budget).
-/
lemma leafDict_length_le_pow_depth (Q : PartialDT n ℓ) :
    Q.leafDict.length ≤ Nat.pow 2 (PDT.depth Q.trunk) := by
  change (PDT.leaves Q.trunk).length ≤ Nat.pow 2 (PDT.depth Q.trunk)
  exact PDT.leaves_length_le_pow_depth Q.trunk

/-- Глубина реализованного дерева также контролирует число листьев. -/
lemma realize_leaves_length_le (Q : PartialDT n ℓ) :
    (PDT.leaves Q.realize).length ≤ Nat.pow 2 (PDT.depth Q.trunk + ℓ) := by
  have hdepth := depth_realize_le (Q := Q)
  have hbound :
      (PDT.leaves Q.realize).length ≤ Nat.pow 2 (PDT.depth Q.realize) :=
    PDT.leaves_length_le_pow_depth Q.realize
  exact Nat.le_trans hbound
    (Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepth)

end PartialDT

end Core
end Pnp3
