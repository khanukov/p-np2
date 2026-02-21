import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Core.BooleanBasics

/-!
  pnp3/Models/PartialTruthTable.lean

  Базовые типы и операции для частичных таблиц истинности (Partial MCSP).

  В этом файле мы фиксируем:
  * каноническую длину таблицы `tableLen n = 2^n`;
  * длину кодировки `inputLen n = 2 * 2^n`, где первая половина — маска
    определённости, а вторая — значения;
  * декодирование `decodePartial` из `Core.BitVec (inputLen n)` в частичную функцию;
  * операции применения рестрикций к кодировке и к частичной таблице;
  * минимальную лемму о том, что результат рестрикции остаётся корректной
    частичной таблицей (типовая замкнутость).

  Важно: все определения — в модельном слое. Мы избегаем аксиом и не
  смешиваем эти факты с леммами про схемы/AC0.
-/

namespace Pnp3
namespace Models

open Core

namespace Partial

/-- Длина таблицы истинности для `n` переменных: `2^n`. -/
def tableLen (n : Nat) : Nat := Nat.pow 2 n

/-- Длина входа partial-MCSP: маска + значения, т.е. `2 * 2^n`. -/
def inputLen (n : Nat) : Nat := 2 * tableLen n

/-- Вспомогательная лемма: `tableLen n ≤ inputLen n`. -/
lemma tableLen_le_inputLen (n : Nat) : tableLen n ≤ inputLen n := by
  have hpos : 0 < 2 := by decide
  -- `tableLen n ≤ 2 * tableLen n` по монотонности умножения.
  dsimp [inputLen]
  exact Nat.le_mul_of_pos_left (tableLen n) hpos

/-- Индекс в маску: `i` остаётся тем же, но живёт в `Fin (inputLen n)`. -/
def maskIndex {n : Nat} (i : Fin (tableLen n)) : Fin (inputLen n) :=
  ⟨i.1, lt_of_lt_of_le i.2 (tableLen_le_inputLen n)⟩

/-- Индекс в значение: смещение на `tableLen n`. -/
def valIndex {n : Nat} (i : Fin (tableLen n)) : Fin (inputLen n) :=
  ⟨tableLen n + i.1, by
    -- Так как `i < tableLen`, то `tableLen + i < tableLen + tableLen`.
    have hlt : tableLen n + i.1 < tableLen n + tableLen n :=
      Nat.add_lt_add_left i.2 _
    -- А `tableLen + tableLen = 2 * tableLen`.
    -- Переписываем цель через `inputLen` и закрываем её `hlt`.
    -- Переписываем цель и завершаем одним `simp`.
    convert hlt using 1; simp [inputLen, two_mul]⟩

/-- Вытаскиваем маску из кодировки `mask ++ values`. -/
def maskPart {n : Nat} (x : Core.BitVec (inputLen n)) : Core.BitVec (tableLen n) :=
  fun i => x (maskIndex i)

/-- Вытаскиваем значения из кодировки `mask ++ values`. -/
def valPart {n : Nat} (x : Core.BitVec (inputLen n)) : Core.BitVec (tableLen n) :=
  fun i => x (valIndex i)

end Partial

/-- Каноническое представление частичной функции. -/
def PartialFunction (n : Nat) := Fin (Partial.tableLen n) → Option Bool

/-- Алиас для читабельности. -/
def PartialTruthTable (n : Nat) := PartialFunction n

instance (n : Nat) : Fintype (PartialFunction n) := by
  dsimp [PartialFunction]
  infer_instance

noncomputable instance (n : Nat) : DecidableEq (PartialFunction n) := by
  classical
  infer_instance

/--
Декодирование `mask ++ values` в частичную функцию.

Если маска равна 0, значение считается `none`.
Если маска равна 1, читаем соответствующее значение из `valPart`.
-/
def decodePartial {n : Nat} (x : Core.BitVec (Partial.inputLen n)) : PartialFunction n :=
  fun i => if Partial.maskPart x i = true then some (Partial.valPart x i) else none

/-- Вспомогательная лемма: индекс `maskIndex i` всегда попадает в первую половину. -/
lemma maskIndex_lt_tableLen {n : Nat} (i : Fin (Partial.tableLen n)) :
    (Partial.maskIndex i).1 < Partial.tableLen n := by
  exact i.2

/-- Вспомогательная лемма: индекс `valIndex i` не лежит в первой половине. -/
lemma valIndex_not_lt_tableLen {n : Nat} (i : Fin (Partial.tableLen n)) :
    ¬ (Partial.valIndex i).1 < Partial.tableLen n := by
  -- `valIndex i` равен `tableLen + i`, значит он не меньше `tableLen`.
  have hge : Partial.tableLen n ≤ (Partial.valIndex i).1 := by
    -- По определению `valIndex` первая компонента равна `tableLen + i`.
    simp [Partial.valIndex]
  exact Nat.not_lt.mpr hge

/-!
  ### Проекция индексов на половины кодировки

  Эти леммы явно фиксируют, что `maskIndex` указывает на левую половину,
  а `valIndex` — на правую. Они полезны для «документации» проекций
  при работе с кодировкой `mask ++ values`.
-/

/-- Индекс маски находится строго левее границы `tableLen`. -/
lemma maskIndex_in_left_half {n : Nat} (i : Fin (Partial.tableLen n)) :
    (Partial.maskIndex i : Fin (Partial.inputLen n)).1 < Partial.tableLen n := by
  exact maskIndex_lt_tableLen i

/-- Индекс значения находится в правой половине: `tableLen ≤ valIndex`. -/
lemma valIndex_in_right_half {n : Nat} (i : Fin (Partial.tableLen n)) :
    Partial.tableLen n ≤ (Partial.valIndex i : Fin (Partial.inputLen n)).1 := by
  -- По определению `valIndex` это `tableLen + i`.
  simp [Partial.valIndex]

/--
Кодирование частичной функции обратно в `mask ++ values`.

* Маска равна `isSome`.\n
* Значение равно `getD false`.\n

Замечание: `false` используется как «заглушка» для `none`, но это безопасно,
поскольку `mask = 0` сигнализирует, что значение не читается.
-/
def encodePartial {n : Nat} (T : PartialFunction n) : Core.BitVec (Partial.inputLen n) :=
  fun i =>
    if h : (i : Nat) < Partial.tableLen n then
      (T ⟨i, h⟩).isSome
      else
        let jNat := (i : Nat) - Partial.tableLen n
      have hlt : jNat < Partial.tableLen n := by
        -- Так как `i < 2 * tableLen` и `i ≥ tableLen`, то `i - tableLen < tableLen`.
        have hlt' : (i : Nat) < Partial.tableLen n + Partial.tableLen n := by
          simpa [Partial.inputLen, two_mul] using i.2
        have hge : Partial.tableLen n ≤ (i : Nat) := Nat.le_of_not_gt h
        have hlt_decomp :
            (i : Nat) - Partial.tableLen n + Partial.tableLen n <
              Partial.tableLen n + Partial.tableLen n := by
          simpa [Nat.sub_add_cancel hge] using hlt'
        have hlt'': (i : Nat) - Partial.tableLen n < Partial.tableLen n :=
          lt_of_add_lt_add_right hlt_decomp
        simpa [jNat] using hlt''
      (T ⟨jNat, hlt⟩).getD false

/--
Применение рестрикции к битовой строке.

Мы сначала приводим вход к канонической кодировке `encodePartial (decodePartial x)`,
чтобы игнорировать «мусорные» биты значений, которые не читаются маской.
Затем заданные биты перезаписываются, а свободные остаются как в канонической строке.
Это гарантирует согласованность с `applyRestrictionToTable`.
-/
def applyRestrictionToInput {n : Nat}
    (x : Core.BitVec (Partial.inputLen n)) (ρ : Restriction (Partial.inputLen n)) :
    Core.BitVec (Partial.inputLen n) :=
  let canonical := encodePartial (decodePartial x)
  fun i => match ρ.mask i with
    | some b => b
    | none => canonical i

/--
Применение рестрикции к обычному присваиванию (битовому вектору) длины `n`.
Полностью аналогично `applyRestrictionToInput`, но для «чистых» входов схемы.
-/
def applyRestrictionToAssignment {n : Nat}
    (x : Core.BitVec n) (ρ : Restriction n) : Core.BitVec n :=
  fun i => match ρ.mask i with
    | some b => b
    | none => x i

/-!
  ### Каноническая кодировка после декодирования

  Эти леммы позволяют раскрывать `encodePartial (decodePartial x)` по индексам
  маски и значений. Они используются в связке «рестрикция на входе ↔ рестрикция
  на таблице».
-/

lemma encodePartial_decodePartial_maskIndex {n : Nat}
    (x : Core.BitVec (Partial.inputLen n)) (i : Fin (Partial.tableLen n)) :
    encodePartial (decodePartial x) (Partial.maskIndex i) =
      x (Partial.maskIndex i) := by
  classical
  have hmask : (Partial.maskIndex i : Fin (Partial.inputLen n)).1 <
      Partial.tableLen n := maskIndex_lt_tableLen i
  have hfin : (⟨(Partial.maskIndex i).1, hmask⟩ : Fin (Partial.tableLen n)) = i := by
    apply Fin.ext
    rfl
  calc
    encodePartial (decodePartial x) (Partial.maskIndex i)
        = (decodePartial x i).isSome := by
            simp [encodePartial, hmask, hfin]
    _ = x (Partial.maskIndex i) := by
          cases hxb : x (Partial.maskIndex i) with
          | false =>
              have hxb' : x (Partial.maskIndex i) = false := hxb
              have hxb'' : x ⟨i.1, lt_of_lt_of_le i.2 (Partial.tableLen_le_inputLen n)⟩ = false := by
                simpa [Partial.maskIndex] using hxb'
              simp [decodePartial, Partial.maskPart, Partial.maskIndex, hxb'']
          | true =>
              have hxb' : x (Partial.maskIndex i) = true := hxb
              have hxb'' : x ⟨i.1, lt_of_lt_of_le i.2 (Partial.tableLen_le_inputLen n)⟩ = true := by
                simpa [Partial.maskIndex] using hxb'
              simp [decodePartial, Partial.maskPart, Partial.valPart, Partial.maskIndex, hxb'']

lemma encodePartial_decodePartial_valIndex {n : Nat}
    (x : Core.BitVec (Partial.inputLen n)) (i : Fin (Partial.tableLen n)) :
    encodePartial (decodePartial x) (Partial.valIndex i) =
      (if x (Partial.maskIndex i) = true then x (Partial.valIndex i) else false) := by
  classical
  have hlt : ¬ ((Partial.valIndex i : Fin (Partial.inputLen n)).1 <
      Partial.tableLen n) := by
    exact valIndex_not_lt_tableLen i
  have hjNat :
      ((Partial.valIndex i : Fin (Partial.inputLen n)).1 - Partial.tableLen n) = i.1 := by
    simp [Partial.valIndex]
  have hfin :
      (⟨(Partial.valIndex i : Fin (Partial.inputLen n)).1 - Partial.tableLen n,
        by
          have hge : Partial.tableLen n ≤ (Partial.valIndex i : Fin (Partial.inputLen n)).1 :=
            valIndex_in_right_half (i := i)
          have hlt' : (Partial.valIndex i : Fin (Partial.inputLen n)).1 <
              Partial.tableLen n + Partial.tableLen n := by
            simpa [Partial.inputLen, two_mul] using (Partial.valIndex i).2
          have hlt_decomp :
              (Partial.valIndex i : Fin (Partial.inputLen n)).1 - Partial.tableLen n +
                Partial.tableLen n < Partial.tableLen n + Partial.tableLen n := by
            simpa [Nat.sub_add_cancel hge] using hlt'
          exact lt_of_add_lt_add_right hlt_decomp⟩ :
      Fin (Partial.tableLen n)) = i := by
    apply Fin.ext
    simp [hjNat]
  calc
    encodePartial (decodePartial x) (Partial.valIndex i)
        = (decodePartial x i).getD false := by
            simp [encodePartial, hlt, hjNat]
    _ =
        (if x (Partial.maskIndex i) = true then x (Partial.valIndex i) else false) := by
          cases hxb : x (Partial.maskIndex i) with
          | false =>
              have hxb' : x (Partial.maskIndex i) = false := hxb
              have hxb'' : x ⟨i.1, lt_of_lt_of_le i.2 (Partial.tableLen_le_inputLen n)⟩ = false := by
                simpa [Partial.maskIndex] using hxb'
              simp [decodePartial, Partial.maskPart, Partial.maskIndex, hxb'']
          | true =>
              have hxb' : x (Partial.maskIndex i) = true := hxb
              have hxb'' : x ⟨i.1, lt_of_lt_of_le i.2 (Partial.tableLen_le_inputLen n)⟩ = true := by
                simpa [Partial.maskIndex] using hxb'
              simp [decodePartial, Partial.maskPart, Partial.valPart, Partial.maskIndex, hxb'']

/-!
  ### Комбинаторные мощности

  Эти леммы дают базовые оценки числа частичных таблиц — важный шаг для
  анти-чекера в стиле «подсчёт вместо вероятности».
-/

/-- Число всех частичных таблиц на `n` переменных равно `3^(2^n)`. -/
lemma card_partialTables (n : Nat) :
    Fintype.card (PartialFunction n) = 3 ^ Partial.tableLen n := by
  classical
  -- `PartialFunction n = Fin (2^n) → Option Bool`, значит кардинал равен `3^(2^n)`.
  simp [PartialFunction, Partial.tableLen]

/-- Верхняя оценка на число частичных таблиц: `3^(2^n)`. -/
@[simp] def allPartialFunctionsBound (n : Nat) : Nat :=
  3 ^ Partial.tableLen n

@[simp] lemma card_partialTables_eq_bound (n : Nat) :
    Fintype.card (PartialFunction n) = allPartialFunctionsBound n := by
  simp [allPartialFunctionsBound, card_partialTables]

/-!
  ### Базовые операции над частичными таблицами

  Мы фиксируем минимальный набор преобразований, необходимых в рассуждениях
  о рестрикциях и «забывании» значений. Все операции чисто функциональные.
-/

/-- Удалить значения на фиксированном множестве позиций. -/
def forget {n : Nat} (T : PartialFunction n) (S : Finset (Fin (Partial.tableLen n))) :
    PartialFunction n :=
  fun i => if i ∈ S then none else T i

/-- Явно задать значение в позиции `i`. -/
def setDefined {n : Nat} (T : PartialFunction n) (i : Fin (Partial.tableLen n))
    (b : Bool) : PartialFunction n :=
  fun j => if j = i then some b else T j

/--
Объединение частичных таблиц с приоритетом слева:
если слева определено, берём его, иначе берём правое значение.
-/
def mergeLeft {n : Nat} (T₁ T₂ : PartialFunction n) : PartialFunction n :=
  fun i => match T₁ i with
    | some b => some b
    | none => T₂ i

/-- На забытых позициях действительно получаем `none`. -/
lemma forget_mem {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n))) {i : Fin (Partial.tableLen n)}
    (hmem : i ∈ S) : forget T S i = none := by
  simp [forget, hmem]

/-- Вне множества `S` операция `forget` не меняет значения. -/
lemma forget_not_mem {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n))) {i : Fin (Partial.tableLen n)}
    (hmem : i ∉ S) : forget T S i = T i := by
  simp [forget, hmem]

/-- Лемма о переопределении заданной позиции. -/
lemma setDefined_eq {n : Nat} (T : PartialFunction n)
    (i : Fin (Partial.tableLen n)) (b : Bool) :
    setDefined T i b i = some b := by
  simp [setDefined]

/-- На других позициях `setDefined` сохраняет исходное значение. -/
lemma setDefined_ne {n : Nat} (T : PartialFunction n)
    {i j : Fin (Partial.tableLen n)} (b : Bool) (h : j ≠ i) :
    setDefined T i b j = T j := by
  simp [setDefined, h]

/-!
  ### Множество определённых позиций

  Для counting-аргументов и рестрикций удобно явно выделять множество индексов,
  где таблица определена.  Ниже фиксируем базовые операции и леммы.
-/

/-- Множество позиций, где таблица определена (`isSome`). -/
def definedPositions {n : Nat} (T : PartialFunction n) :
    Finset (Fin (Partial.tableLen n)) :=
  (Finset.univ : Finset (Fin (Partial.tableLen n))).filter (fun i => (T i).isSome)

/-- Число определённых позиций. -/
def definedCount {n : Nat} (T : PartialFunction n) : Nat :=
  (definedPositions T).card

/-- Характеризация принадлежности `definedPositions`. -/
lemma mem_definedPositions {n : Nat} (T : PartialFunction n)
    {i : Fin (Partial.tableLen n)} :
    i ∈ definedPositions T ↔ (T i).isSome := by
  classical
  simp [definedPositions]

/-- Если `T i` не определено, то `i` не входит в `definedPositions`. -/
lemma not_mem_definedPositions {n : Nat} (T : PartialFunction n)
    {i : Fin (Partial.tableLen n)} (h : T i = none) :
    i ∉ definedPositions T := by
  classical
  have : (T i).isSome = false := by simp [h]
  simp [mem_definedPositions, this]

/-- После `forget` позиции из `S` точно становятся неопределёнными. -/
lemma definedPositions_forget_subset {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n))) :
    definedPositions (forget T S) ⊆ definedPositions T := by
  classical
  intro i hi
  have hi' : (forget T S i).isSome := (mem_definedPositions _).1 hi
  -- В случае `i ∈ S` значение становится `none`, противоречие.
  by_cases hmem : i ∈ S
  · have : forget T S i = none := by simp [forget, hmem]
    simp [this] at hi'
  · -- Вне `S` значение не меняется.
    have hEq : forget T S i = T i := by simp [forget, hmem]
    have : (T i).isSome := by simpa [hEq] using hi'
    exact (mem_definedPositions _).2 this

/-- После `setDefined` позиция `i` становится определённой. -/
lemma mem_definedPositions_setDefined {n : Nat} (T : PartialFunction n)
    (i : Fin (Partial.tableLen n)) (b : Bool) :
    i ∈ definedPositions (setDefined T i b) := by
  classical
  apply (mem_definedPositions _).2
  simp [setDefined]

/-- На других позициях `setDefined` не меняет статус определённости. -/
lemma definedPositions_setDefined_ne {n : Nat} (T : PartialFunction n)
    {i j : Fin (Partial.tableLen n)} (b : Bool) (h : j ≠ i) :
    j ∈ definedPositions (setDefined T i b) ↔ j ∈ definedPositions T := by
  classical
  simp [definedPositions, setDefined, h]

/-- `mergeLeft` определён там, где определён хотя бы один из аргументов. -/
lemma definedPositions_mergeLeft_subset {n : Nat} (T₁ T₂ : PartialFunction n) :
    definedPositions (mergeLeft T₁ T₂) ⊆
      definedPositions T₁ ∪ definedPositions T₂ := by
  classical
  intro i hi
  have hi' : (mergeLeft T₁ T₂ i).isSome := (mem_definedPositions _).1 hi
  cases hT₁ : T₁ i with
  | some b =>
      -- Тогда `mergeLeft` берёт значение из `T₁`.
      have : i ∈ definedPositions T₁ := by
        apply (mem_definedPositions _).2
        simp [hT₁]
      exact (Finset.mem_union.mpr (Or.inl this))
  | none =>
      -- Тогда `mergeLeft` берёт значение из `T₂`.
      have hEq : mergeLeft T₁ T₂ i = T₂ i := by simp [mergeLeft, hT₁]
      have : (T₂ i).isSome := by simpa [hEq] using hi'
      have : i ∈ definedPositions T₂ := (mem_definedPositions _).2 this
      exact (Finset.mem_union.mpr (Or.inr this))

/-!
  ### Неопределённые позиции

  Для counting‑аргументов удобно выделять «комплемент» множества определённых
  позиций и работать с ним напрямую.
-/

/-- Множество неопределённых позиций (`none`). -/
def undefinedPositions {n : Nat} (T : PartialFunction n) :
    Finset (Fin (Partial.tableLen n)) :=
  (Finset.univ : Finset (Fin (Partial.tableLen n))).filter (fun i => (T i).isNone)

/-- Число неопределённых позиций. -/
def undefinedCount {n : Nat} (T : PartialFunction n) : Nat :=
  (undefinedPositions T).card

/-- Характеризация принадлежности `undefinedPositions`. -/
lemma mem_undefinedPositions {n : Nat} (T : PartialFunction n)
    {i : Fin (Partial.tableLen n)} :
    i ∈ undefinedPositions T ↔ (T i).isNone := by
  classical
  simp [undefinedPositions]

/-- `definedPositions` и `undefinedPositions` дизъюнктны. -/
lemma defined_undefined_disjoint {n : Nat} (T : PartialFunction n) :
    Disjoint (definedPositions T) (undefinedPositions T) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hdef hundef
  cases hT : T i with
  | none =>
      have : (T i).isSome = false := by simp [hT]
      have hdef' : (T i).isSome := (mem_definedPositions T).1 hdef
      simp [this] at hdef'
  | some b =>
      have : (T i).isNone = false := by simp [hT]
      have hundef' : (T i).isNone := (mem_undefinedPositions T).1 hundef
      simp [this] at hundef'

/-- Объединение определённых и неопределённых позиций даёт все индексы. -/
lemma defined_union_undefined {n : Nat} (T : PartialFunction n) :
    definedPositions T ∪ undefinedPositions T =
      (Finset.univ : Finset (Fin (Partial.tableLen n))) := by
  classical
  ext i
  cases hT : T i with
  | some b =>
      have : i ∈ definedPositions T := by
        apply (mem_definedPositions T).2
        simp [hT]
      have : i ∈ definedPositions T ∪ undefinedPositions T :=
        Finset.mem_union.mpr (Or.inl this)
      simp [this]
  | none =>
      have : i ∈ undefinedPositions T := by
        apply (mem_undefinedPositions T).2
        simp [hT]
      have : i ∈ definedPositions T ∪ undefinedPositions T :=
        Finset.mem_union.mpr (Or.inr this)
      simp [this]

/-- Сумма количества определённых и неопределённых позиций равна `2^n`. -/
lemma definedCount_add_undefinedCount {n : Nat} (T : PartialFunction n) :
    definedCount T + undefinedCount T = Partial.tableLen n := by
  classical
  have hdisj := defined_undefined_disjoint (T := T)
  have hunion := defined_union_undefined (T := T)
  have hcard_union :
      (definedPositions T ∪ undefinedPositions T).card =
        definedCount T + undefinedCount T := by
    simpa [definedCount, undefinedCount] using
      (Finset.card_union_of_disjoint hdisj)
  calc
    definedCount T + undefinedCount T
        = (definedPositions T ∪ undefinedPositions T).card := by
            symm
            exact hcard_union
    _ = (Finset.univ : Finset (Fin (Partial.tableLen n))).card := by
          simp [hunion]
    _ = Partial.tableLen n := by
          simp

/-- Неопределённых позиций не больше, чем `2^n`. -/
lemma undefinedCount_le_tableLen {n : Nat} (T : PartialFunction n) :
    undefinedCount T ≤ Partial.tableLen n := by
  have h := definedCount_add_undefinedCount (T := T)
  have hle : undefinedCount T ≤ definedCount T + undefinedCount T := by
    exact Nat.le_add_left _ _
  simpa [h] using hle

/-- Неопределённые позиции — это дополнение к определённым. -/
lemma undefinedPositions_eq_compl {n : Nat} (T : PartialFunction n) :
    undefinedPositions T = (definedPositions T)ᶜ := by
  classical
  ext i
  cases hT : T i with
  | some b =>
      have hdef : i ∈ definedPositions T := by
        apply (mem_definedPositions T).2
        simp [hT]
      have hundef : i ∉ undefinedPositions T := by
        intro hmem
        have : (T i).isNone := (mem_undefinedPositions T).1 hmem
        simp [hT] at this
      simp [hdef, hundef]
  | none =>
      have hundef : i ∈ undefinedPositions T := by
        apply (mem_undefinedPositions T).2
        simp [hT]
      have hdef : i ∉ definedPositions T := by
        intro hmem
        have : (T i).isSome := (mem_definedPositions T).1 hmem
        simp [hT] at this
      simp [hdef, hundef]

/-!
  ### Таблицы с фиксированной областью определения

  Для anti-checker удобно фиксировать множество позиций, где таблица определена,
  и считать число возможных таблиц с ровно этим множеством определённых индексов.
-/

/-- Предикат: таблица определена ровно на множестве `S`. -/
def definedExactly {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n))) : Prop :=
  definedPositions T = S

/-- Если таблица определена ровно на `S`, то вне `S` она `none`. -/
lemma definedExactly_outside_none {n : Nat} {T : PartialFunction n}
    {S : Finset (Fin (Partial.tableLen n))} (h : definedExactly T S)
    {i : Fin (Partial.tableLen n)} (hmem : i ∉ S) :
    T i = none := by
  classical
  cases hT : T i with
  | none =>
      rfl
  | some b =>
      have : i ∈ definedPositions T := by
        apply (mem_definedPositions T).2
        simp [hT]
      have hS : definedPositions T = S := by
        simpa [definedExactly] using h
      have : i ∈ S := by simpa [hS] using this
      exact (hmem this).elim

/-- Если `i ∈ S`, то `T i` определено, когда `definedExactly T S`. -/
lemma definedExactly_inside_some {n : Nat} {T : PartialFunction n}
    {S : Finset (Fin (Partial.tableLen n))} (h : definedExactly T S)
    {i : Fin (Partial.tableLen n)} (hmem : i ∈ S) :
    (T i).isSome := by
  classical
  have hS : definedPositions T = S := by
    simpa [definedExactly] using h
  have : i ∈ definedPositions T := by simpa [hS] using hmem
  exact (mem_definedPositions T).1 this

/-- Две таблицы с одинаковыми значениями на `S` и `definedExactly` равны. -/
lemma tables_eq_of_definedExactly {n : Nat}
    {T₁ T₂ : PartialFunction n} {S : Finset (Fin (Partial.tableLen n))}
    (h₁ : definedExactly T₁ S) (h₂ : definedExactly T₂ S)
    (hvals : ∀ i ∈ S, T₁ i = T₂ i) : T₁ = T₂ := by
  funext i
  by_cases hmem : i ∈ S
  · exact hvals i hmem
  · have h₁' : T₁ i = none := definedExactly_outside_none (h := h₁) hmem
    have h₂' : T₂ i = none := definedExactly_outside_none (h := h₂) hmem
    simp [h₁', h₂']

/-- Таблицы, определённые ровно на `S`, образуют конечное множество. -/
noncomputable def tablesWithDefinedSet {n : Nat}
    (S : Finset (Fin (Partial.tableLen n))) : Finset (PartialFunction n) :=
  by
    classical
    exact (Finset.univ.filter (fun T => definedExactly T S))

/--
Сужение таблицы на множество `S`: возвращаем функцию `S → Bool`,
которая извлекает значения (для таблиц, определённых на `S`).
-/
def restrictToSet {n : Nat} (S : Finset (Fin (Partial.tableLen n)))
    (T : PartialFunction n) : S → Bool :=
  fun i => (T i.1).getD false

/-- Вспомогательная лемма: если `definedExactly T S`, то `restrictToSet` корректен. -/
lemma restrictToSet_eq_of_definedExactly {n : Nat}
    {S : Finset (Fin (Partial.tableLen n))} {T : PartialFunction n}
    (h : definedExactly T S) (i : S) :
    T i.1 = some (restrictToSet S T i) := by
  classical
  have hsome : (T i.1).isSome := by
    apply definedExactly_inside_some (T := T) (S := S) (h := h)
    exact i.2
  cases hT : T i.1 with
  | none =>
      simp [hT] at hsome
  | some b =>
      simp [restrictToSet, hT]

/--
Таблицы с фиксированным множеством определённых позиций однозначно задаются
своими значениями на `S`. Это даёт инъекцию в пространство функций `S → Bool`.
-/
lemma injective_restrictToSet {n : Nat}
    {S : Finset (Fin (Partial.tableLen n))} :
    Function.Injective (fun T : {T // definedExactly T S} =>
      restrictToSet S T.1) := by
  intro T₁ T₂ hEq
  apply Subtype.ext
  -- Используем `tables_eq_of_definedExactly`.
  apply tables_eq_of_definedExactly (h₁ := T₁.2) (h₂ := T₂.2)
  intro i hi
  -- На `S` значения совпадают через `restrictToSet`.
  have h₁ := restrictToSet_eq_of_definedExactly (T := T₁.1) (S := S) T₁.2 ⟨i, hi⟩
  have h₂ := restrictToSet_eq_of_definedExactly (T := T₂.1) (S := S) T₂.2 ⟨i, hi⟩
  -- Из равенства функций `restrictToSet` следует равенство значений.
  have hfun := congrArg (fun f => f ⟨i, hi⟩) hEq
  calc
    T₁.1 i = some (restrictToSet S T₁.1 ⟨i, hi⟩) := h₁
    _ = some (restrictToSet S T₂.1 ⟨i, hi⟩) := by
          simp [hfun]
    _ = T₂.1 i := h₂.symm

/-!
  Из инъекции получаем более точную оценку:
  `|tablesWithDefinedSet S| ≤ 2^{|S|}`.
-/

lemma card_tablesWithDefinedSet_le_pow {n : Nat}
    (S : Finset (Fin (Partial.tableLen n))) :
    (tablesWithDefinedSet (n := n) S).card ≤ 2 ^ S.card := by
  classical
  -- Переходим к подмножеству `Subtype` с условием `definedExactly`.
  have hcard :
      (tablesWithDefinedSet (n := n) S).card =
        Fintype.card {T : PartialFunction n // definedExactly T S} := by
    have hcard' :
        Fintype.card {T : PartialFunction n // definedExactly T S} =
          (tablesWithDefinedSet (n := n) S).card := by
      simpa [tablesWithDefinedSet] using
        (Fintype.card_subtype (α := PartialFunction n) (p := fun T => definedExactly T S))
    exact hcard'.symm
  -- Инъекция в `S → Bool` даёт оценку кардинала.
  have hinj : Function.Injective (fun T : {T // definedExactly T S} =>
      restrictToSet S T.1) :=
    injective_restrictToSet (S := S)
  have hle' : Fintype.card {T : PartialFunction n // definedExactly T S} ≤
      Fintype.card (S → Bool) :=
    Fintype.card_le_of_injective _ hinj
  have hle : (tablesWithDefinedSet (n := n) S).card ≤ Fintype.card (S → Bool) := by
    -- Стандартная оценка по инъекции.
    simpa [hcard] using hle'
  -- Кардинал функций `S → Bool` равен `2^{|S|}`.
  have hcard_fun : Fintype.card (S → Bool) = 2 ^ S.card := by
    simp
  -- Собираем вместе.
  simpa [hcard, hcard_fun] using hle

/-!
  ### Частичные таблицы, согласованные с фиксированной тотальной функцией

  Следующий блок даёт биекцию между масками и частичными таблицами,
  согласованными с заданной тотальной функцией `f`.  Это даёт точную
  комбинаторную оценку `2^{2^n}` для числа таких таблиц.
-/

/-- Тотальная функция в табличной форме. -/
abbrev TotalFunction (n : Nat) := Fin (Partial.tableLen n) → Bool

/-- Согласованность partial‑таблицы `T` с тотальной функцией `f`. -/
def consistentWithTotal {n : Nat} (T : PartialFunction n) (f : TotalFunction n) : Prop :=
  ∀ i, match T i with
    | some b => b = f i
    | none => True

noncomputable instance {n : Nat} (f : TotalFunction n) :
    Fintype {T : PartialFunction n // consistentWithTotal T f} := by
  classical
  infer_instance

/-- Маска определённости для partial‑таблицы. -/
def maskOfPartial {n : Nat} (T : PartialFunction n) : Core.BitVec (Partial.tableLen n) :=
  fun i => (T i).isSome

/-- Построение partial‑таблицы по маске и тотальной функции. -/
def partialFromMask {n : Nat} (f : TotalFunction n)
    (mask : Core.BitVec (Partial.tableLen n)) : PartialFunction n :=
  fun i => if mask i then some (f i) else none

/-- Таблица, построенная по маске, согласована с `f`. -/
lemma consistentWithTotal_fromMask {n : Nat}
    (f : TotalFunction n) (mask : Core.BitVec (Partial.tableLen n)) :
    consistentWithTotal (partialFromMask f mask) f := by
  intro i
  by_cases h : mask i
  · simp [partialFromMask, h]
  · simp [partialFromMask, h]

/-- Маска, извлечённая из `partialFromMask`, совпадает с исходной маской. -/
lemma maskOfPartial_fromMask {n : Nat}
    (f : TotalFunction n) (mask : Core.BitVec (Partial.tableLen n)) :
    maskOfPartial (partialFromMask f mask) = mask := by
  funext i
  by_cases h : mask i <;> simp [maskOfPartial, partialFromMask, h]

/-- Если `T` согласована с `f`, то восстановление по маске возвращает `T`. -/
lemma partialFromMask_maskOfPartial {n : Nat}
    (T : PartialFunction n) (f : TotalFunction n)
    (hcons : consistentWithTotal T f) :
    partialFromMask f (maskOfPartial T) = T := by
  funext i
  cases hT : T i with
  | none =>
      -- В этом случае маска равна `false`.
      have : maskOfPartial T i = false := by simp [maskOfPartial, hT]
      simp [partialFromMask, this]
  | some b =>
      -- В этом случае маска равна `true`, и значение совпадает с `f i`.
      have : maskOfPartial T i = true := by simp [maskOfPartial, hT]
      have hEq : b = f i := by
        have := hcons i
        simp [hT] at this
        exact this
      simp [partialFromMask, this, hEq]

/-- Эквивалентность между масками и согласованными partial‑таблицами. -/
noncomputable def consistentPartialEquiv {n : Nat} (f : TotalFunction n) :
    (Core.BitVec (Partial.tableLen n)) ≃ {T : PartialFunction n // consistentWithTotal T f} :=
  { toFun := fun mask => ⟨partialFromMask f mask, consistentWithTotal_fromMask f mask⟩
    invFun := fun T => maskOfPartial T.1
    left_inv := by
      intro mask
      exact maskOfPartial_fromMask f mask
    right_inv := by
      intro T
      apply Subtype.ext
      exact partialFromMask_maskOfPartial (T := T.1) (f := f) T.2 }

/-- Число partial‑таблиц, согласованных с фиксированной `f`, равно `2^{2^n}`. -/
theorem card_consistentPartial_withTotal {n : Nat} (f : TotalFunction n) :
    Fintype.card {T : PartialFunction n // consistentWithTotal T f} =
      2 ^ Partial.tableLen n := by
  classical
  have hEquiv := Fintype.card_congr (consistentPartialEquiv (f := f))
  -- Кардинал масок равен `2^{|Fin (2^n)|}`.
  have hmask :
      Fintype.card (Core.BitVec (Partial.tableLen n)) = 2 ^ Partial.tableLen n := by
    simp
  -- Переписываем кардиналы через эквивалентность и оценку для масок.
  simpa [hmask] using hEquiv.symm

/-!
  ### Согласованные тотальные функции

  Эти определения и леммы дают количественную оценку числа тотальных функций,
  согласованных с заданной частичной таблицей. Это ключевой шаг для
  counting‑anti-checker.
-/

/-- Тотальная функция согласована с частичной таблицей, если совпадает на `some`. -/
def consistentTotal {n : Nat} (T : PartialFunction n) (f : TotalFunction n) : Prop :=
  ∀ i,
    match T i with
    | some b => f i = b
    | none => True

noncomputable instance {n : Nat} (T : PartialFunction n) :
    Fintype {f : TotalFunction n // consistentTotal T f} := by
  classical
  infer_instance

/-- Индексы неопределённых позиций как подтип. -/
def undefinedIndex {n : Nat} (T : PartialFunction n) :=
  {i : Fin (Partial.tableLen n) // i ∈ undefinedPositions T}

noncomputable instance {n : Nat} (T : PartialFunction n) : Fintype (undefinedIndex T) := by
  classical
  refine Fintype.subtype (undefinedPositions T) ?_
  intro i
  rfl

noncomputable instance {n : Nat} (T : PartialFunction n) : DecidableEq (undefinedIndex T) := by
  classical
  infer_instance

/-- Ограничение тотальной функции на неопределённые позиции. -/
def restrictUndefined {n : Nat} (T : PartialFunction n) (f : TotalFunction n) :
    undefinedIndex T → Bool :=
  fun i => f i.1

/--
Расширение функции на неопределённых позициях до тотальной функции:
на определённых позициях берём значение из `T`.
-/
def extendFromUndefined {n : Nat} (T : PartialFunction n)
    (g : undefinedIndex T → Bool) : TotalFunction n :=
  fun i =>
    if h : i ∈ undefinedPositions T then
      g ⟨i, h⟩
    else
      (T i).getD false

/-- Расширение действительно согласовано с `T`. -/
lemma extendFromUndefined_consistent {n : Nat} (T : PartialFunction n)
    (g : undefinedIndex T → Bool) : consistentTotal T (extendFromUndefined T g) := by
  intro i
  cases hT : T i with
  | none =>
      -- В этом случае условие согласованности тривиально.
      simp
  | some b =>
      -- Здесь `i` не принадлежит `undefinedPositions`.
      have hmem : i ∉ undefinedPositions T := by
        intro hmem
        have : (T i).isNone := (mem_undefinedPositions T).1 hmem
        simp [hT] at this
      -- Значение `extendFromUndefined` берётся из `T`.
      simp [extendFromUndefined, hT, hmem]

/-- Ограничение после расширения возвращает исходную функцию. -/
lemma restrict_extendFromUndefined {n : Nat} (T : PartialFunction n)
    (g : undefinedIndex T → Bool) :
    restrictUndefined T (extendFromUndefined T g) = g := by
  funext i
  -- По определению `undefinedIndex` имеем `i.1 ∈ undefinedPositions T`.
  have hmem : i.1 ∈ undefinedPositions T := i.2
  simp [restrictUndefined, extendFromUndefined, hmem]

/-- Расширение после ограничения совпадает с исходной тотальной функцией. -/
lemma extendFromUndefined_restrict {n : Nat} (T : PartialFunction n)
    (f : TotalFunction n) (hcons : consistentTotal T f) :
    extendFromUndefined T (restrictUndefined T f) = f := by
  funext i
  by_cases hmem : i ∈ undefinedPositions T
  · -- На неопределённых позициях возвращаем `f`.
    simp [extendFromUndefined, restrictUndefined, hmem]
  · -- На определённых позициях используем значение из `T`.
    cases hT : T i with
    | none =>
        -- Противоречие с `i ∉ undefinedPositions`.
        have : i ∈ undefinedPositions T := by
          apply (mem_undefinedPositions T).2
          simp [hT]
        exact (hmem this).elim
    | some b =>
        have hEq : f i = b := by
          have := hcons i
          simp [hT] at this
          exact this
        simp [extendFromUndefined, hmem, hT, hEq]

/-- Эквивалентность между согласованными тотальными функциями и функциями на `undefinedIndex`. -/
noncomputable def consistentTotalEquiv {n : Nat} (T : PartialFunction n) :
    {f : TotalFunction n // consistentTotal T f} ≃ (undefinedIndex T → Bool) :=
  { toFun := fun f => restrictUndefined T f.1
    invFun := fun g => ⟨extendFromUndefined T g, extendFromUndefined_consistent T g⟩
    left_inv := by
      intro f
      apply Subtype.ext
      exact extendFromUndefined_restrict (T := T) (f := f.1) f.2
    right_inv := by
      intro g
      exact restrict_extendFromUndefined (T := T) g }

/-- Кардинал множества неопределённых индексов равен `undefinedCount`. -/
lemma card_undefinedIndex_eq {n : Nat} (T : PartialFunction n) :
    Fintype.card (undefinedIndex T) = undefinedCount T := by
  classical
  -- Прямое применение `Fintype.card_subtype`.
  simpa [undefinedIndex, undefinedCount, undefinedPositions] using
    (Fintype.card_subtype (α := Fin (Partial.tableLen n))
      (p := fun i => i ∈ undefinedPositions T))

/-- Число тотальных функций, согласованных с `T`, равно `2^{undefinedCount T}`. -/
theorem card_consistentTotal {n : Nat} (T : PartialFunction n) :
    Fintype.card {f : TotalFunction n // consistentTotal T f} =
      2 ^ (undefinedCount T) := by
  classical
  -- Переводим в функции на `undefinedIndex`.
  have hEquiv := Fintype.card_congr (consistentTotalEquiv (T := T))
  -- Кардинал функций `undefinedIndex → Bool`.
  have hfun :
      Fintype.card (undefinedIndex T → Bool) =
        2 ^ Fintype.card (undefinedIndex T) := by
    simp
  -- Собираем равенства.
  calc
    Fintype.card {f : TotalFunction n // consistentTotal T f}
        = Fintype.card (undefinedIndex T → Bool) := hEquiv
    _ = 2 ^ Fintype.card (undefinedIndex T) := hfun
    _ = 2 ^ undefinedCount T := by
          -- Завершаем через `undefinedCount`.
          simp [card_undefinedIndex_eq (T := T)]

/-- Перечисление всех таблиц с фиксированным множеством определённых позиций. -/
noncomputable def tablesWithDefinedSetList {n : Nat}
    (S : Finset (Fin (Partial.tableLen n))) : List (PartialFunction n) :=
  (tablesWithDefinedSet (n := n) S).toList

/-- Каждая таблица из `tablesWithDefinedSet` действительно определена на `S`. -/
lemma mem_tablesWithDefinedSet {n : Nat}
    {S : Finset (Fin (Partial.tableLen n))} {T : PartialFunction n} :
    T ∈ tablesWithDefinedSet (n := n) S ↔ definedExactly T S := by
  classical
  simp [tablesWithDefinedSet, definedExactly]

/-- Простейшая верхняя оценка: число таких таблиц не больше `2^{|S|}`. -/
lemma card_tablesWithDefinedSet_le {n : Nat}
    (S : Finset (Fin (Partial.tableLen n))) :
    (tablesWithDefinedSet (n := n) S).card ≤ 3 ^ Partial.tableLen n := by
  classical
  -- Грубая оценка: подмножество всех partial‑таблиц.
  have hle :
      (tablesWithDefinedSet (n := n) S).card ≤ Fintype.card (PartialFunction n) := by
    simpa using (Finset.card_le_univ (s := tablesWithDefinedSet (n := n) S))
  simpa [card_partialTables n] using hle

/-!
  ### Оценки на `definedCount`

  Эти леммы дают «чистые» арифметические следствия из уже доказанных
  утверждений о `definedPositions`.  Они нужны для counting‑аргументов
  в anti-checker: важно контролировать, сколько позиций остаётся
  определённым после операций над таблицами.
-/

/-- После `forget` число определённых позиций не возрастает. -/
lemma definedCount_forget_le {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n))) :
    definedCount (forget T S) ≤ definedCount T := by
  classical
  -- Следует из вложенности множеств определённых позиций.
  have hsubset := definedPositions_forget_subset (T := T) (S := S)
  exact Finset.card_le_card hsubset

/-- Если `S` не пересекается с определёнными позициями, `forget` не меняет счётчик. -/
lemma definedCount_forget_eq_of_disjoint {n : Nat} (T : PartialFunction n)
    (S : Finset (Fin (Partial.tableLen n)))
    (hdisj : Disjoint S (definedPositions T)) :
    definedCount (forget T S) = definedCount T := by
  classical
  apply le_antisymm
  · exact definedCount_forget_le (T := T) (S := S)
  · -- Показываем, что каждое определённое значение остаётся определённым.
    have hsubset :
        definedPositions T ⊆ definedPositions (forget T S) := by
      intro i hi
      have hmemS : i ∉ S := by
        have hdisj' := (Finset.disjoint_left.1 hdisj)
        exact fun hmem => (hdisj' hmem hi)
      -- Вне `S` значение не меняется.
      have hEq : forget T S i = T i := by simp [forget, hmemS]
      have : (forget T S i).isSome := by simpa [hEq] using (mem_definedPositions _).1 hi
      exact (mem_definedPositions _).2 this
    exact Finset.card_le_card hsubset

/-- После `setDefined` число определённых позиций увеличивается не более чем на 1. -/
lemma definedCount_setDefined_le_succ {n : Nat} (T : PartialFunction n)
    (i : Fin (Partial.tableLen n)) (b : Bool) :
    definedCount (setDefined T i b) ≤ definedCount T + 1 := by
  classical
  by_cases hmem : i ∈ definedPositions T
  · -- Если позиция уже была определена, число определённых не увеличивается.
    have hEq : definedPositions (setDefined T i b) = definedPositions T := by
      ext j
      by_cases hji : j = i
      · -- `i` остаётся определённой и уже была определённой.
        have : i ∈ definedPositions (setDefined T i b) := by
          exact mem_definedPositions_setDefined T i b
        simpa [hmem, hji] using this
      · -- На других позициях статус определённости не меняется.
        simp [definedPositions_setDefined_ne (T := T) (b := b) hji]
    -- Следовательно, `definedCount` не меняется, а значит ≤ `+1`.
    have hcount : definedCount (setDefined T i b) = definedCount T := by
      simp [definedCount, hEq]
    -- Переписываем через `hcount` и применяем тривиальную оценку.
    exact hcount.le.trans (Nat.le_succ _)
  · -- Если позиция была неопределённой, добавляем максимум одну позицию.
    have hsubset :
        definedPositions (setDefined T i b) ⊆
          insert i (definedPositions T) := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact Finset.mem_insert_self _ _
      · -- На других позициях определённость совпадает с T.
        have hiff := definedPositions_setDefined_ne (T := T) (b := b) hji
        have : j ∈ definedPositions T := by
          exact (hiff.mp hj)
        exact Finset.mem_insert_of_mem this
    have hcard :=
      Finset.card_le_card hsubset
    -- Оцениваем кардинал `insert i` через `+1`.
    have hcard_insert :
        (insert i (definedPositions T)).card ≤ definedCount T + 1 := by
      by_cases hmem' : i ∈ definedPositions T
      · -- В этом случае `insert` не меняет множество.
        simp [definedCount, hmem']
      · -- Иначе кардинал увеличивается на 1.
        simp [definedCount, hmem', Nat.add_comm]
    exact hcard.trans hcard_insert

/-- Число определённых позиций в исходной таблице ограничено числом после `setDefined`. -/
lemma definedCount_le_setDefined_succ {n : Nat} (T : PartialFunction n)
    (i : Fin (Partial.tableLen n)) (b : Bool) :
    definedCount T ≤ definedCount (setDefined T i b) + 1 := by
  classical
  -- Используем симметричный аргумент: `definedPositions T ⊆ insert i definedPositions (setDefined T i b)`.
  have hsubset :
      definedPositions T ⊆ insert i (definedPositions (setDefined T i b)) := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      exact Finset.mem_insert_self _ _
    · have hiff := (definedPositions_setDefined_ne (T := T) (b := b) hji).symm
      have : j ∈ definedPositions (setDefined T i b) := hiff.mp hj
      exact Finset.mem_insert_of_mem this
  have hcard := Finset.card_le_card hsubset
  -- Оценка кардинала `insert`.
  have hcard_insert :
      (insert i (definedPositions (setDefined T i b))).card ≤
        definedCount (setDefined T i b) + 1 := by
    by_cases hmem : i ∈ definedPositions (setDefined T i b)
    · simp [definedCount, hmem]
    · simp [definedCount, hmem, Nat.add_comm]
  exact hcard.trans hcard_insert

/-- `mergeLeft` определён не более чем на сумме определённых позиций. -/
lemma definedCount_mergeLeft_le {n : Nat} (T₁ T₂ : PartialFunction n) :
    definedCount (mergeLeft T₁ T₂) ≤ definedCount T₁ + definedCount T₂ := by
  classical
  -- Пользуемся `definedPositions_mergeLeft_subset` и оценкой для объединения.
  have hsubset := definedPositions_mergeLeft_subset (T₁ := T₁) (T₂ := T₂)
  have hcard_le := Finset.card_le_card hsubset
  -- Оцениваем кардинал объединения сверху суммой кардиналов.
  have hcard_union :
      (definedPositions T₁ ∪ definedPositions T₂).card ≤
        definedCount T₁ + definedCount T₂ := by
    simpa [definedCount] using
      (Finset.card_union_le (definedPositions T₁) (definedPositions T₂))
  exact hcard_le.trans hcard_union

/--
Применение табличной рестрикции к частичной функции.

Мы рассматриваем маску и значения как две независимые половины входа и
перезаписываем их согласно `ρ`. При этом результат остаётся функцией
`Fin (2^n) → Option Bool`.
-/
def applyRestrictionToTable {n : Nat}
    (T : PartialFunction n) (ρ : Restriction (Partial.inputLen n)) : PartialFunction n :=
  fun i =>
    let maskBit :=
      match ρ.mask (Partial.maskIndex i) with
      | some b => b
      | none => (T i).isSome
    let valBit :=
      match ρ.mask (Partial.valIndex i) with
      | some b => b
      | none => (T i).getD false
    if maskBit then some valBit else none

/--
Декодирование после рестрикции входа эквивалентно рестрикции частичной таблицы.

Это основная техническая связка между представлением `mask ++ values` и
семантикой `PartialFunction`.
-/
lemma decodePartial_applyRestrictionToInput {n : Nat}
    (x : Core.BitVec (Partial.inputLen n)) (ρ : Restriction (Partial.inputLen n)) :
    decodePartial (applyRestrictionToInput x ρ) =
      applyRestrictionToTable (decodePartial x) ρ := by
  funext i
  -- Разбираем значения маски/значения под действием рестрикции.
  cases hmask : ρ.mask (Partial.maskIndex i) <;>
    cases hval : ρ.mask (Partial.valIndex i) <;>
    (by_cases hx : x (Partial.maskIndex i) <;>
      simp [decodePartial, applyRestrictionToInput, applyRestrictionToTable,
        Partial.maskPart, Partial.valPart, hmask, hval,
        encodePartial_decodePartial_maskIndex, encodePartial_decodePartial_valIndex, hx])

/-- Декодирование после кодирования возвращает исходную частичную функцию. -/
lemma decodePartial_encodePartial {n : Nat} (T : PartialFunction n) :
    decodePartial (encodePartial T) = T := by
  funext i
  have hmask : Partial.maskPart (encodePartial T) i = (T i).isSome := by
    simp [Partial.maskPart, encodePartial, Partial.maskIndex]
  have hval : Partial.valPart (encodePartial T) i = (T i).getD false := by
    simp [Partial.valPart, encodePartial, Partial.valIndex]
  cases hTi : T i <;> simp [decodePartial, hmask, hval, hTi]

/--
Типовая замкнутость: после рестрикции мы остаёмся в том же типе
`PartialTruthTable n`.

Это базовая лемма, необходимая для устранения «encoding wall».
-/
theorem restriction_preserves_type {n : Nat}
    (T : PartialTruthTable n) (ρ : Restriction (Partial.inputLen n)) :
    ∃ (T' : PartialTruthTable n), T' = applyRestrictionToTable T ρ := by
  exact ⟨_, rfl⟩

end Models
end Pnp3
