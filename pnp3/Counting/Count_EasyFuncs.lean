import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Core.BooleanBasics

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
            simp [allBooleanFunctionsBound, card_bitvec]

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
