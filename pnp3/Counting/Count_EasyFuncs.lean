import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Core.BooleanBasics
import Core.SAL_Core

/-!
  pnp3/Counting/Count_EasyFuncs.lean

  В классических оценках сложности схем часто требуется грубая верхняя
  граница на число булевых функций, которые могут быть реализованы малыми
  схемами.  Даже без сложной комбинаторики достаточно помнить, что всего
  булевых функций на `n` переменных ровно `2^{2^n}`: каждая функция задаётся
  таблицей истинности длины `2^n`, и каждая такая таблица — произвольная
  последовательность из нулей и единиц.  Следовательно, любое подсемейство
  (в том числе множество «простых» функций) не может содержать больше
  элементов.

  Ниже мы формализуем именно эту тривиальную, но полезную границу.  Она
  заменяет прежнюю аксиому `count_small_circuits_bound`, делая часть B
  полностью конструктивной даже до подключения настоящих оценок роста
  числа схем.  Впоследствии, когда появятся более тонкие асимптотические
  формулы, их можно будет встроить поверх этой базовой заготовки.
-/

namespace Pnp3
namespace Counting

open scoped BigOperators

/--
  Полное число булевых функций на `n` переменных.  Оно равно `2^{2^n}` и
  служит универсальной верхней оценкой для любого подсемейства — в том
  числе и для функций, реализуемых малыми схемами.
-/
@[simp] def allBooleanFunctionsBound (n : Nat) : Nat := 2 ^ Nat.pow 2 n

lemma card_bitvec (n : Nat) :
    Fintype.card (Core.BitVec n) = 2 ^ n := by
  classical
  -- `Core.BitVec n` — это `Fin n → Bool`, поэтому число всех битовых векторов — `2^n`.
  calc
    Fintype.card (Core.BitVec n)
        = Fintype.card (Fin n → Bool) := rfl
    _ = (Fintype.card Bool) ^ Fintype.card (Fin n) :=
          Fintype.card_fun (α := Fin n) (β := Bool)
    _ = 2 ^ n := by
          simp [Fintype.card_fin]

lemma card_boolean_functions (n : Nat) :
    Fintype.card (Core.BitVec n → Bool) = allBooleanFunctionsBound n := by
  classical
  -- Число всех функций `BitVec n → Bool` равно `2^{|BitVec n|}`.
  have hcard := Fintype.card_fun (α := Core.BitVec n) (β := Bool)
  calc
    Fintype.card (Core.BitVec n → Bool)
        = (Fintype.card Bool) ^ Fintype.card (Core.BitVec n) := hcard
    _ = 2 ^ Fintype.card (Core.BitVec n) := by simp
    _ = allBooleanFunctionsBound n := by
          simp [allBooleanFunctionsBound]

/--
  Полное множество всех булевых функций на `n` переменных, представленных
  как конечное множество.  Это удобный источник семейства для построения
  «большого» сценария, приводящего к противоречию с ограниченной ёмкостью.
-/
@[simp] def allFunctionsFinset (n : Nat) :
    Finset (Core.BitVec n → Bool) := Finset.univ

@[simp] lemma card_allFunctionsFinset (n : Nat) :
    (allFunctionsFinset n).card = 2 ^ (2 ^ n) :=
  by
    classical
    calc
      (allFunctionsFinset n).card
          = Fintype.card (Core.BitVec n → Bool) := by
              simp [allFunctionsFinset]
      _ = allBooleanFunctionsBound n := card_boolean_functions n
      _ = 2 ^ (2 ^ n) := by simp [allBooleanFunctionsBound]

/--
  Полное семейство всех булевых функций на `n` переменных в формате `Family`
  (список).  Реализовано через список элементов `Finset.univ`, так что порядок
  не важен, а данные удобны для последующей работы с `familyFinset`.
-/
noncomputable def allFunctionsFamily (n : Nat) : Core.Family n :=
  (allFunctionsFinset n).toList

@[simp] lemma allFunctionsFamily_toFinset (n : Nat) :
    (allFunctionsFamily n).toFinset = allFunctionsFinset n :=
  by
    classical
    -- `toList` перечисляет элементы `univ` без повторов, поэтому восстановление
    -- через `toFinset` сразу возвращает исходный `Finset`.
    simp [allFunctionsFamily, allFunctionsFinset]

/--
  Любое конечное семейство булевых функций на `n` переменных не может быть
  больше полного множества `2^{2^n}`.  Это чисто комбинаторное утверждение,
  полученное из очевидного факта `|F| ≤ |универса|`.
-/
lemma card_family_le_allBooleanFunctions (n : Nat)
    (F : Finset (Core.BitVec n → Bool)) :
    F.card ≤ allBooleanFunctionsBound n := by
  classical
  -- Сравниваем с универсальным Finset, чья мощность равна `Fintype.card`.
  have h := Finset.card_le_univ (s := F)
  -- Переписываем правую часть через явную формулу `2^{2^n}`.
  have hb := card_boolean_functions n
  exact (hb ▸ h)

/--  
  **External quantitative bound (placeholder).**

  Мы используем эту лемму как интерфейс для *строгой* оценки ёмкости,
  необходимой в античекере.  Интуитивное содержание: если словарь и бюджет
  достаточно малы (≤ `2^n`), а ошибка не превосходит `1/(n+2)`, то ёмкость
  `capacityBound` строго меньше общего числа булевых функций `2^{2^n}`.

  В текущем коде это оформлено как аксиома, потому что полноценное
  биномиально-энтропийное доказательство требует отдельного слоя
  аналитической арифметики.  Лемма изолирует именно тот недостающий
  строгий шаг, о котором говорится в докстринге `AntiChecker.lean`.

  Как только будет добавлен комбинаторный/энтропийный пакет для оценки
  `hammingBallBound`, эту аксиому следует заменить доказательством.  
-/
axiom capacityBound_lt_allBooleanFunctions
    (n D k : Nat) (ε : Rat)
    (hε0 : (0 : Rat) ≤ ε) (hε1 : ε ≤ (1 : Rat) / 2)
    (hD : D ≤ 2 ^ n) (hk : k ≤ 2 ^ n)
    (hε : ε ≤ (1 : Rat) / (n + 2)) :
    Counting.capacityBound D k (Nat.pow 2 n) ε hε0 hε1
      < allBooleanFunctionsBound n

/--
  Тривиальная верхняя оценка на число «простых» функций: их не может быть
  больше всех возможных булевых функций.  Этого достаточно, чтобы в частях
  B и C использовать конкретную константу вместо ранее постулированной
  аксиомы.
-/
theorem count_small_circuits_bound (n _s : Nat) :
    ∃ Bound : Nat,
      Bound = allBooleanFunctionsBound n ∧
        ∀ F : Finset (Core.BitVec n → Bool), F.card ≤ Bound := by
  refine ⟨allBooleanFunctionsBound n, rfl, ?_⟩
  intro F
  exact card_family_le_allBooleanFunctions n F

end Counting
end Pnp3
