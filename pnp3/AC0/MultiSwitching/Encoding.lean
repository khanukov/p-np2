import Mathlib.Data.Fintype.Card
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.Counting

/-!
  pnp3/AC0/MultiSwitching/Encoding.lean

  Минимальная «encoding/injection» оболочка для multi-switching.

  Идея классического доказательства:
  1) фиксируем предикат "bad" (например, `BadEvent` для CCDT);
  2) строим инъекцию из множества плохих рестрикций в конечное множество кодов;
  3) сравниваем кардиналы и заключаем существование хорошей рестрикции.

  Здесь мы оставляем схему максимально абстрактной:
  * `EncodingWitness` хранит только кодирующее отображение и его инъективность;
  * оценка кардиналов проводится через `Fintype.card_le_of_injective`;
  * итоговый шаг использует готовую лемму `exists_good_of_card_lt`.

  Такой интерфейс позволяет «подключить» реальный encoding
  (например, через запись CCDT-ветви и набора термов), не меняя downstream.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n k ℓ t : Nat}
variable {F : FormulaFamily n k}
variable {α : Type}

/-!
### Инъективный encoding для bad-ограничений

Мы фиксируем конечное множество `codes` (например, это могут быть битовые
строки фиксированной длины или структурированные «сертификаты»), и требуем
инъекцию из множества плохих рестрикций в это множество.
-/

structure EncodingWitness
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat)
    (codes : Finset α)
    [DecidablePred (BadEvent (A := A))] : Type where
  /-- Инъективное кодирование каждого плохого ограничения. -/
  encode :
    {ρ // ρ ∈ badRestrictions (n := n) s (BadEvent (A := A))}
      → {c // c ∈ codes}
  /-- Инъективность кодирования. -/
  inj : Function.Injective encode

/-!
### Кардинальная оценка по encoding

Если существует инъекция в `codes`, то число «плохих» ограничений
не превосходит `codes.card`.
-/

lemma badRestrictions_card_le_of_encoding
    {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat)
    (codes : Finset α)
    [DecidablePred (BadEvent (A := A))]
    (witness : EncodingWitness (A := A) (s := s) codes) :
    (badRestrictions (n := n) s (BadEvent (A := A))).card ≤ codes.card := by
  classical
  -- Обозначим соответствующие множества как `Set`, чтобы использовать
  -- `Fintype.ofFinset` и сравнивать их кардиналы через инъекцию.
  let badSet : Set (Restriction n) :=
    {ρ | ρ ∈ badRestrictions (n := n) s (BadEvent (A := A))}
  let codeSet : Set α := {c | c ∈ codes}
  have hcard :
      Fintype.card badSet ≤ Fintype.card codeSet := by
    -- `Fintype.card_le_of_injective` применим к подтипам.
    simpa [badSet, codeSet] using
      (Fintype.card_le_of_injective witness.encode witness.inj)
  have hbad :
      Fintype.card badSet =
        (badRestrictions (n := n) s (BadEvent (A := A))).card := by
    -- Привязываем кардинал подтипа к кардиналу `Finset`.
    simpa [badSet] using
      (Fintype.card_ofFinset
        (s := badRestrictions (n := n) s (BadEvent (A := A)))
        (p := badSet)
        (H := by intro x; rfl))
  have hcode :
      Fintype.card codeSet = codes.card := by
    simpa [codeSet] using
      (Fintype.card_ofFinset
        (s := codes) (p := codeSet) (H := by intro x; rfl))
  -- Итоговая оценка через переписывание.
  simpa [hbad, hcode] using hcard

/-!
### Экстракция хорошей рестрикции

Если `codes.card` строго меньше общего числа рестрикций в `R_s`,
то по инъективности encoding существует «хорошая» рестрикция.
-/

lemma exists_good_restriction_of_encoding
    {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat)
    (codes : Finset α)
    [DecidablePred (BadEvent (A := A))]
    (witness : EncodingWitness (A := A) (s := s) codes)
    (hcodes : codes.card < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadEvent (A := A) ρ := by
  classical
  -- Сначала оцениваем число плохих рестрикций через encoding.
  have hbad :
      (badRestrictions (n := n) s (BadEvent (A := A))).card ≤ codes.card := by
    exact badRestrictions_card_le_of_encoding (A := A) (s := s)
      (codes := codes) witness
  -- Затем используем общий комбинаторный шаг из `Counting.lean`.
  have hlt :
      (badRestrictions (n := n) s (BadEvent (A := A))).card
        < (R_s (n := n) s).card := by
    exact lt_of_le_of_lt hbad hcodes
  exact exists_good_of_card_lt (n := n) (s := s)
    (bad := BadEvent (A := A)) hlt

end MultiSwitching
end AC0
end Pnp3
