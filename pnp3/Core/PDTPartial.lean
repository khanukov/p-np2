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

/--
  «Склейка» двух частичных PDT: к каждому хвосту `Q` приписываем дополнительный
  частичный разбор.  Новый объект имеет тот же ствол, а глубина хвостов растёт
  не более чем на `ℓ₂`.  Такая конструкция понадобится при рекурсивном
  построении multi-switching дерева, когда на каждом шаге требуется уточнить
  хвосты свежеполученными частичными сертификатами.
-/
def splice {ℓ₁ ℓ₂ : Nat} (Q : PartialDT n ℓ₁)
    (R : ∀ β : Subcube n, β ∈ PDT.leaves Q.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, (R β hβ).trunk = Q.tails β hβ) :
    PartialDT n (ℓ₁ + ℓ₂) where
  trunk := Q.trunk
  tails := fun β hβ => (R β hβ).realize
  tail_depth_le := by
    intro β hβ
    have hdepth := PartialDT.depth_realize_le (Q := R β hβ)
    have hbound :
        PDT.depth (R β hβ).trunk ≤ ℓ₁ := by
      simpa [htrunk β hβ] using Q.tail_depth_le β hβ
    have := Nat.add_le_add_right hbound ℓ₂
    exact Nat.le_trans hdepth this

@[simp] lemma splice_trunk {ℓ₁ ℓ₂ : Nat}
    (Q : PartialDT n ℓ₁)
    (R : ∀ β : Subcube n, β ∈ PDT.leaves Q.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, (R β hβ).trunk = Q.tails β hβ) :
    (splice (Q := Q) R htrunk).trunk = Q.trunk := rfl

@[simp] lemma splice_tails {ℓ₁ ℓ₂ : Nat}
    (Q : PartialDT n ℓ₁)
    (R : ∀ β : Subcube n, β ∈ PDT.leaves Q.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, (R β hβ).trunk = Q.tails β hβ)
    (β : Subcube n) (hβ : β ∈ PDT.leaves Q.trunk) :
    (splice (Q := Q) R htrunk).tails β hβ = (R β hβ).realize := rfl

lemma splice_tail_depth_le {ℓ₁ ℓ₂ : Nat}
    (Q : PartialDT n ℓ₁)
    (R : ∀ β : Subcube n, β ∈ PDT.leaves Q.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, (R β hβ).trunk = Q.tails β hβ)
    (β : Subcube n) (hβ : β ∈ PDT.leaves Q.trunk) :
    PDT.depth ((splice (Q := Q) R htrunk).tails β hβ)
      ≤ ℓ₁ + ℓ₂ := by
  have := (splice (Q := Q) R htrunk).tail_depth_le β hβ
  simpa using this

@[simp] lemma realize_splice {ℓ₁ ℓ₂ : Nat}
    (Q : PartialDT n ℓ₁)
    (R : ∀ β : Subcube n, β ∈ PDT.leaves Q.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, (R β hβ).trunk = Q.tails β hβ) :
    (splice (Q := Q) R htrunk).realize
      = PDT.refine Q.trunk (fun β hβ => (R β hβ).realize) := rfl

end PartialDT

end Core
end Pnp3
