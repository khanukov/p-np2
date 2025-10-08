/-
  pnp3/ThirdPartyFacts/Facts_Switching.lean

  Здесь мы концентрируем все внешние допущения типа "мульти-switching лемма",
  которые в дальнейшем подключаются как готовые факты.  Формально они оформлены
  как Lean-аксиомы, но снабжены подробными комментариями, чтобы позднее было
  понятно, какие именно параметры предстоит доказать (или импортировать из
  внешних источников).

  На данном шаге нам достаточно интерфейса: "из параметров семейства AC⁰"
  следует существование объекта `Shrinkage`, который затем конвейер SAL
  превращает в общий атлас.
-/
import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.SAL_Core
import AC0.Formulas

/-!
  В дополнение к основному shrinkage-факту нам понадобится ещё одна
  элементарная арифметическая оценка: если ошибка аппроксимации
  ограничена как `ε ≤ 1/(n+2)`, то автоматически `ε ≤ 1/2`.  Это
  полезно при связке с энтропийными оценками (Covering-Power).
-/

namespace Pnp3

namespace Core

/-- Подкуб, задающий ровно точку `x`. -/
@[simp] def pointSubcube {n : Nat} (x : BitVec n) : Subcube n :=
  fun i => some (x i)

/-- Точка всегда принадлежит своему точечному подкубу. -/
@[simp] lemma mem_pointSubcube_self {n : Nat} (x : BitVec n) :
    mem (pointSubcube x) x := by
  classical
  apply (mem_iff (β := pointSubcube x) (x := x)).mpr
  intro i b hb
  have hsome : some (x i) = some b := by
    simpa [pointSubcube] using hb
  exact Option.some.inj hsome

/-- Принадлежность точечному подкубу означает точное совпадение вектора. -/
@[simp] lemma mem_pointSubcube_iff {n : Nat} {x y : BitVec n} :
    mem (pointSubcube x) y ↔ x = y := by
  classical
  constructor
  · intro hmem
    have hprop := (mem_iff (β := pointSubcube x) (x := y)).mp hmem
    funext i
    have : pointSubcube x i = some (x i) := by simp [pointSubcube]
    have hy := hprop i (x i) this
    exact hy.symm
  · intro hxy
    subst hxy
    exact mem_pointSubcube_self x

end Core

namespace ThirdPartyFacts

open Core

/-- Параметры класса AC⁰, которые обычно фигурируют в switching-леммах.

* `n` — число входных переменных.
* `M` — размер формулы/схемы (число вентилей, листьев и т.д.).
* `d` — глубина схемы (число слоёв).

В более сложных вариантах добавляются ограничения на ширину DNF, число слоёв
OR/AND и пр., но для текущего интерфейса достаточно этих трёх чисел. -/
structure AC0Parameters where
  n : Nat
  M : Nat
  d : Nat
  deriving Repr

/--
  Параметры для класса «локальных схем».  Мы сохраняем только наиболее
  необходимые числовые характеристики:

  * `n` — число входных бит (длина таблицы истинности).
  * `M` — общий размер схемы (например, число вентилей).
  * `ℓ` — параметр локальности: каждое выходное значение зависит не более
    чем от `ℓ` входов.
  * `depth` — число слоёв (глубина схемы).

  В дальнейшем эта структура служит лишь для записи тех величин, которые
  фигурируют в внешнем факте о shrinkage для локальных схем.  Дополнительные
  ограничения (например, на тип вентилей) можно будет добавить позже, не
  меняя интерфейс Lean.
-/
structure LocalCircuitParameters where
  n      : Nat
  M      : Nat
  ℓ      : Nat
  depth  : Nat
  deriving Repr

/-- Уточняющая структура, описывающая гарантии shrinkage.

`depthBound` и `errorBound` — ожидаемые верхние оценки на глубину PDT и ошибку
аппроксимации, получаемые из multi-switching леммы.  Мы оставляем их в явном
виде, чтобы позднее подставлять сюда конкретные полиномиальные/квазиполиномиальные
формулы. -/
structure ShrinkageBounds where
  depthBound : Nat
  errorBound : Q
  deriving Repr

/-- Заготовка для "внешнего" факта: псевдослучайная multi-switching лемма
Servedio–Tan/Håstad.  Возвращает объект `Shrinkage`, совместимый с конвейером
SAL.  Параметры оценок записаны максимально прозрачно; их значения будут
уточняться по мере подключения конкретных источников.

Обратите внимание: мы фиксируем семейство функций `F` (список) и утверждаем,
что существует общая PDT глубины `t` и ошибка `ε`, удовлетворяющие стандартным
для SAL условиям.  В дальнейшем этот факт будет служить мостом между
комбинаторным ядром и оценками размера атласа. -/
axiom shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2)

/--
  Внешний факт для локальных схем: после применения подходящих ограничений
  схема становится «малой» PDT.  Конкретные численные границы отражают
  стандартные оценки: глубина дерева пропорциональна произведению локальности
  и логарифмических факторов по размеру и глубине схемы.
-/
axiom shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2)

/--
  Техническая лемма: при любом `n` имеем `1 / (n + 2) ≤ 1 / 2`.
  Доказательство — аккуратная алгебра на ℚ: сводим утверждение к
  очевидному неравенству `2 ≤ n + 2` и раскрываем деление.
-/
lemma inv_nat_succ_succ_le_half (n : Nat) :
    (1 : Q) / (n + 2) ≤ (1 : Q) / 2 := by
  have hNat : (2 : Q) ≤ (n + 2 : Q) := by
    exact_mod_cast (Nat.le_add_left 2 n)
  have hpos : (0 : Q) < (2 : Q) := by norm_num
  have hdiv :=
    (one_div_le_one_div_of_le (a := (2 : Q)) (b := (n + 2 : Q)) hpos hNat)
  exact hdiv

/--
  Из оценки `ε ≤ 1 / (n + 2)` немедленно следует `ε ≤ 1 / 2`.
  Это условие нужно для дальнейших энтропийных оценок шара Хэмминга.
-/
lemma eps_le_half_of_eps_le_inv_nplus2 (n : Nat) {ε : Q}
    (h : ε ≤ (1 : Q) / (n + 2)) : ε ≤ (1 : Q) / 2 :=
  h.trans (inv_nat_succ_succ_le_half n)

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
noncomputable def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n) : Atlas params.n := by
  classical
  let h := shrinkage_for_AC0 params F
  let t := Classical.choose h
  let h₁ := Classical.choose_spec h
  let ε := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let S := Classical.choose h₂
  exact Atlas.fromShrinkage S

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n) :
    WorksFor (atlas_from_AC0 params F) F := by
  classical
  let h := shrinkage_for_AC0 params F
  let t := Classical.choose h
  let h₁ := Classical.choose_spec h
  let ε := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let S := Classical.choose h₂
  have hspec := Classical.choose_spec h₂
  have hF : S.F = F := hspec.left
  have hworks : WorksFor (Atlas.fromShrinkage S) S.F :=
    SAL_from_Shrinkage S
  have hdict : Atlas.fromShrinkage S = atlas_from_AC0 params F := rfl
  have hworks' := hworks
  simp [hdict] at hworks'
  have hworks'' := hworks'
  simp [hF] at hworks''
  exact hworks''

end ThirdPartyFacts
end Pnp3
