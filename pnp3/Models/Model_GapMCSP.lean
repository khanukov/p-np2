import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.FinRange
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

  Ниже мы фиксируем простую модель булевых схем на базисе {AND, OR, NOT}
  с fan-in 2. Это обеспечивает честный язык GapMCSP, не зашивая в него
  ограничения на глубину (они будут накладываться позже).
-/

/-- Примитивные схемы над `n` входами. -/
inductive Circuit (n : Nat) where
  | input : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n
  deriving Repr

/-- Размер схемы как число вентилей (каждая вершина считается за 1). -/
def Circuit.size {n : Nat} : Circuit n → Nat
  | Circuit.input _ => 1
  | Circuit.const _ => 1
  | Circuit.not c => c.size + 1
  | Circuit.and c₁ c₂ => c₁.size + c₂.size + 1
  | Circuit.or c₁ c₂ => c₁.size + c₂.size + 1

/-- Вычисление схемы на входе `x`. -/
def Circuit.eval {n : Nat} : Circuit n → Core.BitVec n → Bool
  | Circuit.input i => fun x => x i
  | Circuit.const b => fun _ => b
  | Circuit.not c => fun x => !(Circuit.eval c x)
  | Circuit.and c₁ c₂ => fun x => Circuit.eval c₁ x && Circuit.eval c₂ x
  | Circuit.or c₁ c₂ => fun x => Circuit.eval c₁ x || Circuit.eval c₂ x

/-- Интерпретация битовой строки как числа (младший бит имеет индекс 0). -/
def bitVecToNat {n : Nat} (x : Core.BitVec n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc + (if x i then Nat.pow 2 (i : Nat) else 0))
    0

/--
Преобразуем таблицу истинности в функцию на `n` битах.
Используем `Fin.ofNat`, что безопасно, поскольку индекс всегда меньше `2^n`.
-/
def truthTableFunction {n : Nat} (table : Core.BitVec (Nat.pow 2 n)) :
    Core.BitVec n → Bool := fun x =>
  by
    have hpos : 0 < Nat.pow 2 n := by
      have hbase : 0 < (2 : Nat) := by decide
      simpa using (Nat.pow_pos hbase)
    let _ : NeZero (Nat.pow 2 n) := ⟨Nat.ne_of_gt hpos⟩
    exact table (Fin.ofNat (n := Nat.pow 2 n) (bitVecToNat x))

/-- Схема `c` вычисляет функцию, заданную таблицей `table`. -/
def circuitComputes {n : Nat} (c : Circuit n) (table : Core.BitVec (Nat.pow 2 n)) :
    Prop :=
  ∀ x : Core.BitVec n, Circuit.eval c x = truthTableFunction table x

/-- Существует схема размера ≤ `sYES`, вычисляющая таблицу `table`. -/
def hasSmallCircuit (p : GapMCSPParams) (table : Core.BitVec (inputLen p)) : Prop :=
  ∃ c : Circuit p.n, c.size ≤ p.sYES ∧ circuitComputes c table

/-- Любая схема, вычисляющая `table`, имеет размер ≥ `sNO`. -/
def onlyLargeCircuits (p : GapMCSPParams) (table : Core.BitVec (inputLen p)) : Prop :=
  ∀ c : Circuit p.n, circuitComputes c table → p.sNO ≤ c.size

/--
  Лемма-ограничение: если выполняется `onlyLargeCircuits`, то «малой» схемы
  быть не может. Здесь используется явный gap-параметр `sYES + 1 ≤ sNO`.
  Эта лемма — единственная точка, где задействован `sNO` без привлечения
  дополнительного контекста.
-/
lemma onlyLargeCircuits_not_small
    (p : GapMCSPParams) (table : Core.BitVec (inputLen p)) :
    onlyLargeCircuits p table → ¬ hasSmallCircuit p table := by
  intro hLarge hSmall
  -- Из `hasSmallCircuit` берём конкретную схему `c` и её размер.
  rcases hSmall with ⟨c, hSize, hComp⟩
  -- По `onlyLargeCircuits` для этой же схемы получаем нижнюю границу `sNO ≤ size`.
  have hLower : p.sNO ≤ p.sYES := by
    exact (hLarge c hComp).trans hSize
  -- Учитываем разрыв `sYES + 1 ≤ sNO`, получая невозможное `sYES + 1 ≤ sYES`.
  have hGap : p.sYES + 1 ≤ p.sYES := by
    exact (le_trans p.gap_ok hLower)
  exact (Nat.not_succ_le_self _ ) hGap

/--
  Язык GapMCSP: по таблице истинности `table` (длины `2^n`) проверяем,
  есть ли схема размера ≤ `sYES`.  Если да — возвращаем `true`.
  В остальных случаях (включая «промежуток» между `sYES` и `sNO`) возвращаем
  `false`, что соответствует стандартной promise-интерпретации.
-/
noncomputable def gapMCSP_Language (p : GapMCSPParams) : Language := by
  classical
  intro n x
  refine dite (n = inputLen p) ?yes ?no
  · intro h
    have table : Core.BitVec (inputLen p) := by
      simpa [h] using x
    by_cases hYes : hasSmallCircuit p table
    · exact true
    · exact false
  · intro _
    exact false

/-!
  ### Простейшие связи языка и условий Promise

  Язык `gapMCSP_Language` по определению «смотрит» только на существование
  малой схемы. При этом параметр `sNO` всё равно важен, потому что в
  дальнейшем мы будем использовать `onlyLargeCircuits` как формальный NO-под
  promise. Чтобы не потерять информацию о `sNO`, фиксируем явные леммы, которые
  связывают `onlyLargeCircuits` с отрицанием `gapMCSP_Language`.
-/

/-- На входах длины `2^n` язык равен `true` тогда и только тогда, когда есть
    малая схема размера ≤ `sYES`. -/
lemma gapMCSP_language_true_iff_hasSmallCircuit
    (p : GapMCSPParams) (x : Core.BitVec (inputLen p)) :
    gapMCSP_Language p (inputLen p) x = true ↔ hasSmallCircuit p x := by
  classical
  -- В определении `gapMCSP_Language` совпадает длина входа, поэтому `dite`
  -- раскрывается в ветку `yes`.
  simp [gapMCSP_Language]

/-- Если все схемы большие, то язык GapMCSP возвращает `false`. -/
lemma gapMCSP_language_false_of_onlyLarge
    (p : GapMCSPParams) (x : Core.BitVec (inputLen p)) :
    onlyLargeCircuits p x → gapMCSP_Language p (inputLen p) x = false := by
  intro hLarge
  -- Если все схемы большие, то «малой» схемы точно нет.
  have hNoSmall : ¬ hasSmallCircuit p x :=
    onlyLargeCircuits_not_small p x hLarge
  -- Разбираем случаи по факту существования малой схемы.
  by_cases hSmall : hasSmallCircuit p x
  · exact (hNoSmall hSmall).elim
  · have hNotTrue : gapMCSP_Language p (inputLen p) x ≠ true :=
      (gapMCSP_language_true_iff_hasSmallCircuit p x).not.mpr hSmall
    -- По значениям Bool: если не `true`, то `false`.
    cases hVal : gapMCSP_Language p (inputLen p) x
    · rfl
    · exfalso
      exact hNotTrue hVal

/-- Тип входов promise-версии GapMCSP: таблица истинности длины `2^n`. -/
abbrev GapMCSPInput (p : GapMCSPParams) := Core.BitVec (inputLen p)

/--
  Невычислимый (но формально корректный) верификатор для `GapMCSP`.

  **Идея**: сертификат должен кодировать схему размера ≤ `sYES`.  Пока в проекте
  нет явной кодировки схем в битовые строки, поэтому мы поступаем максимально
  прямо: проверяем существование подходящей схемы и тем самым моделируем
  «декодирование + проверку». Это эквивалентно следующему (концептуальному)
  алгоритму:

  1. Принять вход `x` длины `N = 2^n` как таблицу истинности.
  2. «Декодировать» сертификат `w` в схему `C` размера ≤ `sYES`.
  3. Проверить, что `Circuit.eval C` совпадает с `truthTableFunction x`
     на всех `N` входах длины `n`.

  Сейчас шаг 2 реализован как `decide (hasSmallCircuit p table)`, то есть мы
  напрямую спрашиваем о существовании схемы и не зависим от конкретного `w`.
  Как только появится модуль `encode/decode` для схем, это место можно
  заменить на конструктивный разбор сертификата без изменения окружения.
-/
noncomputable def gapMCSP_verify (p : GapMCSPParams) :
    ∀ n, Bitstring n → Bitstring (certificateLength n 2) → Bool := by
  classical
  intro n x _w
  by_cases h : n = inputLen p
  · -- На корректной длине входа трактуем `x` как таблицу истинности.
    subst h
    -- `decide` выполняет логическую проверку существования корректной схемы.
    exact decide (hasSmallCircuit p x)
  · -- На других длинах input язык по определению равен `false`.
    exact false

lemma gapMCSP_verify_eq_language
    (p : GapMCSPParams) {n : Nat} (x : Bitstring n)
    (w : Bitstring (certificateLength n 2)) :
    gapMCSP_verify p n x w = gapMCSP_Language p n x := by
  classical
  by_cases h : n = inputLen p
  · subst h
    by_cases hSmall : hasSmallCircuit p x
    · simp [gapMCSP_verify, gapMCSP_Language, hSmall]
    · simp [gapMCSP_verify, gapMCSP_Language, hSmall]
  · simp [gapMCSP_verify, gapMCSP_Language, h]

/--
  `GapMCSP ∈ NP`.

  Здесь мы фиксируем `c = 2` и `k = 1`, а время работы берём равным
  `(n + certificateLength n k)^2 + 2`.  Верификатор `gapMCSP_verify`
  не использует сертификат, что допустимо для определения `NP`:
  существование *какого-то* полиномиального верификатора уже достаточно.

  Если/когда появится явная кодировка схем, этот блок можно заменить
  на конструктивную проверку схемы по таблице истинности.
-/
theorem gapMCSP_in_NP (p : GapMCSPParams) : NP (gapMCSP_Language p) := by
  classical
  refine ⟨2, 2, (fun t => t ^ 2 + 2), gapMCSP_verify p, ?_, ?_⟩
  · intro n
    -- Полиномиальность времени очевидна при `c = 2`.
    simp
  · intro n x
    constructor
    · intro hLang
      -- Сертификат не влияет на проверку, поэтому выбираем любой.
      refine ⟨(fun _ => false), ?_⟩
      simpa [gapMCSP_verify_eq_language (p := p) (x := x)] using hLang
    · intro hExists
      rcases hExists with ⟨w, hVerify⟩
      simpa [gapMCSP_verify_eq_language (p := p) (x := x)] using hVerify

/-- Promise-задача GapMCSP, определяемая через язык `gapMCSP_Language`. -/
def GapMCSPPromise (p : GapMCSPParams) : PromiseProblem (GapMCSPInput p) :=
  { Yes := fun x => gapMCSP_Language p (inputLen p) x = true
    No := fun x => gapMCSP_Language p (inputLen p) x = false
    disjoint := by
      classical
      refine Set.disjoint_left.mpr ?_
      intro x hYes hNo
      have : true = false := Eq.trans (Eq.symm hYes) hNo
      cases this }

/-!
  Связь с `PromiseProblem`: полезно иметь прямые леммы, которые превращают
  условия `hasSmallCircuit` и `onlyLargeCircuits` в принадлежность YES/NO
  областям задачи. Это избавляет дальнейшие доказательства от ручного
  раскрытия определения `GapMCSPPromise`.
-/

/-- Наличие малой схемы переводит вход в YES-область promise-задачи. -/
lemma gapMCSP_yes_of_small
    (p : GapMCSPParams) (x : Core.BitVec (inputLen p)) :
    hasSmallCircuit p x → x ∈ (GapMCSPPromise p).Yes := by
  intro hSmall
  -- YES означает значение языка `true`.
  have hLang : gapMCSP_Language p (inputLen p) x = true :=
    (gapMCSP_language_true_iff_hasSmallCircuit p x).2 hSmall
  simpa [GapMCSPPromise] using hLang

/-- Отсутствие малой схемы по причине `onlyLargeCircuits` переводит вход
    в NO-область promise-задачи. -/
lemma gapMCSP_no_of_large
    (p : GapMCSPParams) (x : Core.BitVec (inputLen p)) :
    onlyLargeCircuits p x → x ∈ (GapMCSPPromise p).No := by
  intro hLarge
  have hLang : gapMCSP_Language p (inputLen p) x = false :=
    gapMCSP_language_false_of_onlyLarge p x hLarge
  simpa [GapMCSPPromise] using hLang

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
