import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Facts.LocalityLift.Interface.Parameters

/-!
# Извлечение тест-набора из множества живых координат

В полноценном доказательстве locality lift тест-набор `T` строится из
«живых» координат, возвращаемых shrinkage-свидетелем.  Этот файл
подготовляет соответствующие конструкции: мы переводим конечное
подмножество `alive ⊆ Fin N` в набор битовых векторов длины `N`, где
каждый вектор кодирует одиночную живую координату.  Такое описание не
противоречит классическому доказательству и сохраняет необходимую
полилогарифмическую границу на мощности `T`.

Пока фактический shrinkage-аргумент не реализован, данные конструкции
служат промежуточным шагом: когда появится реальный сертификат,
объявленные ниже функции станут мостом от его параметров к
«чертежу» локального решателя.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
`supportVector i` — битовый вектор длины `N`, принимающий значение `true`
ровно на позиции `i` и `false` на всех остальных.  Такие векторы удобны,
чтобы кодировать отдельные живые координаты из shrinkage-свидетеля.
-/
def supportVector {N : Nat} (i : Fin N) : BitVec N :=
  fun j => decide (j = i)

@[simp] lemma supportVector_self {N : Nat} (i : Fin N) :
    supportVector i i = true := by
  classical
  simp [supportVector]

@[simp] lemma supportVector_ne {N : Nat} {i j : Fin N} (h : j ≠ i) :
    supportVector i j = false := by
  classical
  by_cases hij : j = i
  · exact (h hij).elim
  · simp [supportVector, hij]

/--
Инъективное отображение, отправляющее номер живой координаты в
соответствующий битовый вектор.  Это позволяет без труда строить
`Finset` живых векторов из `Finset` живых индексов.
-/
def supportEmbedding (N : Nat) : (Fin N) ↪ (BitVec N) where
  toFun := supportVector
  inj' := by
    classical
    intro i j h
    have hij := congrArg (fun f => f i) h
    have : decide (i = j) = true := by
      simpa [supportVector] using hij
    exact of_decide_eq_true this

/--
Преобразуем конечное множество живых координат в тест-набор битовых
векторов.  Каждый вектор соответствует одной координате, поэтому мощность
полученного множества совпадает с `alive.card`.
-/
def testSetOfAlive {N : Nat} (alive : Finset (Fin N)) : Finset (BitVec N) :=
  alive.map (supportEmbedding N)

@[simp] lemma mem_testSetOfAlive {N : Nat} (alive : Finset (Fin N))
    {v : BitVec N} :
    v ∈ testSetOfAlive alive ↔ ∃ i ∈ alive, supportVector i = v := by
  classical
  constructor
  · intro hv
    rcases mem_map.mp hv with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_map.mpr ⟨i, hi, rfl⟩

@[simp] lemma card_testSetOfAlive {N : Nat} (alive : Finset (Fin N)) :
    (testSetOfAlive alive).card = alive.card := by
  classical
  change (alive.map (supportEmbedding N)).card = alive.card
  exact Finset.card_map (f := supportEmbedding N) (s := alive)

/-- Длина входа `N = 2^n` всегда положительна. -/
lemma inputLen_pos (p : GapMCSPParams) : 0 < inputLen p := by
  have : 0 < 2 ^ p.n := Nat.pow_pos (by decide : 0 < (2 : Nat))
  simpa [inputLen] using this

/-- Канонический набор живых координат: одна координата с индексом `0`. -/
def canonicalAlive (p : GapMCSPParams) : Finset (Fin (inputLen p)) :=
  {⟨0, inputLen_pos p⟩}

@[simp] lemma mem_canonicalAlive {p : GapMCSPParams}
    (i : Fin (inputLen p)) : i ∈ canonicalAlive p ↔ i = ⟨0, inputLen_pos p⟩ := by
  classical
  constructor
  · intro hi
    have : i ∈ ({⟨0, inputLen_pos p⟩} : Finset (Fin (inputLen p))) := hi
    simpa [canonicalAlive]
  · intro hi
    subst hi
    simp [canonicalAlive]

@[simp] lemma card_canonicalAlive (p : GapMCSPParams) :
    (canonicalAlive p).card = 1 := by
  classical
  simp [canonicalAlive]

end LocalityLift
end Facts
