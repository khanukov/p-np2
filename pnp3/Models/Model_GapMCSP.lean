import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Core.BooleanBasics
import Complexity.Promise
import Complexity.Interfaces

/-!
  pnp3/Models/Model_GapMCSP.lean

  На шаге C нам требуется лишь минималистичная модель параметров GapMCSP.
  Мы фиксируем число входных переменных `n` для функции, чью таблицу истинности
  длины `N = 2^n` рассматривает MCSP, а также два порога размеров схем —
  `sYES` и `sNO`, отвечающие за YES- и NO-слои gap-версии задачи.

  Эти данные будут использоваться в ядре нижней оценки: гипотеза о существовании
  «малого» решателя GapMCSP формулируется через такие параметры, а далее
  связывается с SAL и Covering-Power.
-/
namespace Pnp3
namespace Models

open Core
open Complexity
open ComplexityInterfaces

/--
  Параметры GapMCSP.  Нам достаточно знать количество переменных `n` и два
  порога размера схем `sYES < sNO`, задающих разрыв (gap) между YES- и NO-слоями.

  * `n` — число входных переменных функции. Таблица истинности имеет длину `2^n`.
  * `sYES` — верхняя граница на размер схемы, свидетельствующей ответ YES.
  * `sNO` — нижняя граница на размер схемы для NO-инстансов; по определению
    требуем `sYES + 1 ≤ sNO`, чтобы gap был ненулевым.
-/
structure GapMCSPParams where
  n : Nat
  sYES : Nat
  sNO : Nat
  gap_ok : sYES + 1 ≤ sNO
  /-- В дальнейших оценках предполагаем «достаточно большой» размер таблицы. -/
  n_large : 8 ≤ n
  deriving Repr

/-- Длина входа MCSP: `N = 2^n`. Это основная числовая характеристика задачи. -/
def inputLen (p : GapMCSPParams) : Nat := Nat.pow 2 p.n

/--
  Полилогарифмический бюджет, используемый в части C для ограничения размера
  тест-наборов античекера.  Определение выбрано произвольным, но удобным:
  четвёртая степень `log₂ (N + 1)`, увеличенная на единицу для избежания нулевых
  значений.  Такой бюджет достаточно мал (polylog `N`) и положителен для любых
  ненулевых `N`.
-/
def polylogBudget (N : Nat) : Nat :=
  (Nat.succ (Nat.log2 (Nat.succ N))) ^ 4

/-!
  ### Promise-формализация GapMCSP

  В текущей версии мы сохраняем минимальный интерфейс: YES/NO-множества
  определяются через язык `gapMCSP_Language`.  Пока этот язык является
  заглушкой (см. ниже), но структура позволяет заменить его на реальную
  формализацию без изменения типов решателей.
-/

/-- Язык GapMCSP в текущей модели (заглушка). -/
def gapMCSP_Language (_p : GapMCSPParams) : Language := fun _ _ => False

/-- Тип входов promise-версии GapMCSP: таблица истинности длины `2^n`. -/
abbrev GapMCSPInput (p : GapMCSPParams) := Core.BitVec (inputLen p)

/-- Promise-задача GapMCSP, определяемая через язык `gapMCSP_Language`. -/
def GapMCSPPromise (p : GapMCSPParams) : PromiseProblem (GapMCSPInput p) :=
  { Yes := fun x => gapMCSP_Language p (inputLen p) x = true
    No := fun x => gapMCSP_Language p (inputLen p) x = false
    disjoint := by
      classical
      refine Set.disjoint_left.mpr ?_
      intro x hYes hNo
      cases hNo
      cases hYes }

/--
  `SolvesPromise` for the GapMCSP promise is equivalent to pointwise
  agreement with the GapMCSP language.  This is the main bridge that lets
  us replace promise-style correctness with a concrete equality of Boolean
  functions whenever we need to reason about membership in families.
-/
theorem solvesPromise_gapMCSP_iff
    {p : GapMCSPParams} {decide : GapMCSPInput p → Bool} :
    SolvesPromise (GapMCSPPromise p) decide ↔
      ∀ x, decide x = gapMCSP_Language p (inputLen p) x := by
  constructor
  · intro h x
    -- Split on the language value and use the corresponding promise side.
    cases hlang : gapMCSP_Language p (inputLen p) x
    · have hNo : x ∈ (GapMCSPPromise p).No := by
        simpa [GapMCSPPromise] using hlang
      simpa [hlang] using h.2 x hNo
    · have hYes : x ∈ (GapMCSPPromise p).Yes := by
        simpa [GapMCSPPromise] using hlang
      simpa [hlang] using h.1 x hYes
  · intro h
    constructor
    · intro x hx
      -- In the YES region, the language evaluates to `true`.
      have hx' : gapMCSP_Language p (inputLen p) x = true := by
        simpa [GapMCSPPromise] using hx
      have hdec := h x
      simpa [hx'] using hdec
    · intro x hx
      -- In the NO region, the language evaluates to `false`.
      have hx' : gapMCSP_Language p (inputLen p) x = false := by
        simpa [GapMCSPPromise] using hx
      have hdec := h x
      simpa [hx'] using hdec

end Models
end Pnp3
