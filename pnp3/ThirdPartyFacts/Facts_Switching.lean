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
import PnP3.Core.BooleanBasics
import PnP3.Core.SAL_Core

namespace PnP3.ThirdPartyFacts

open PnP3.Core

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
        ε ≤ (1 : Q) / (Nat.pow 2 (Nat.log2 (params.n + 2)))

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n) : Atlas params.n :=
  match shrinkage_for_AC0 params F with
  | ⟨_t, ⟨_ε, ⟨S, _⟩⟩⟩ => Atlas.fromShrinkage S

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n) :
    WorksFor (atlas_from_AC0 params F) F := by
  classical
  -- Разворачиваем аксиому и применяем SAL.
  obtain ⟨t, ht⟩ := shrinkage_for_AC0 params F
  obtain ⟨ε, hε⟩ := ht
  obtain ⟨S, hS⟩ := hε
  have hworks : WorksFor (Atlas.fromShrinkage S) S.F :=
    SAL_from_Shrinkage S
  -- Из заключения аксиомы следует `S.F = F`.
  rcases hS with ⟨hF, _ht, _hε, _htBound, _hεBound⟩
  -- Приводим всё к нужному виду.
  have : Atlas.fromShrinkage S = atlas_from_AC0 params F := rfl
  -- Переупорядочиваем `WorksFor` с учётом `hF`.
  simpa [this, hF] using hworks

end PnP3.ThirdPartyFacts
