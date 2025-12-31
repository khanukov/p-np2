import Mathlib.Data.Fintype.Card
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.Counting
import AC0.MultiSwitching.CanonicalTrace
import AC0.MultiSwitching.CanonicalDT

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
### Вспомогательное множество кодов (Aux)

В proof-by-encoding обычно требуется конечное множество "сертификатов пути":
на каждом из `t` шагов мы храним

* направление ветвления (бит),
* позицию внутри терма/клаузы (≤ k),
* номер формулы из семейства (≤ m).

Ниже мы даём *абстрактную* реализацию такого кода как функцию
`Fin t → (Bool × Fin k × Fin m)` и сразу фиксируем его кардинал.
Это позволит позже связать инъекцию `Bad → R_{s-t} × Aux` с оценкой
`|Aux| ≤ (2*k*m)^t` без дополнительных вычислений.
-/

/--
Код пути длины `t`: для каждого шага храним

* пару `(индекс, значение)` (полный `BitFix n`),
* позицию выбранного литерала внутри клаузы (`Fin k`),
* номер формулы из семейства (`Fin m`).

Наличие `BitFix n` делает код достаточно информативным, чтобы
восстанавливать исходную рестрикцию через `reconstructRestriction`.
-/
abbrev Aux (n t k m : Nat) : Type :=
  Fin t → (BitFix n × Fin k × Fin m)

lemma card_Aux (n t k m : Nat) :
    Fintype.card (Aux n t k m) = (2 * n * k * m) ^ t := by
  classical
  -- `Fintype.card_fun` даёт степень кардинала кодом для одного шага.
  -- Кардинал одного шага = (2 * n) * k * m.
  simp [Aux, BitFix, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

lemma card_Aux_le (n t k m : Nat) :
    Fintype.card (Aux n t k m) ≤ (2 * n * k * m) ^ t := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (le_rfl : (2 * n * k * m) ^ t ≤ (2 * n * k * m) ^ t)

/-- Универсальное множество кодов `Aux` как `Finset.univ`. -/
def auxCodes (n t k m : Nat) [Fintype (Aux n t k m)] : Finset (Aux n t k m) :=
  Finset.univ

@[simp] lemma auxCodes_card (n t k m : Nat) [Fintype (Aux n t k m)] :
    (auxCodes n t k m).card = Fintype.card (Aux n t k m) := by
  simp [auxCodes]

/-!
### Инъективный encoding для bad-ограничений

Формально фиксируем encoding как инъекцию из множества «плохих» рестрикций
в конечное множество кодов. Эти определения нужны раньше, чем
специализации `product` и `Aux`.
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

lemma badRestrictions_card_le_of_encoding
    {F : FormulaFamily n k}
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat)
    (codes : Finset α)
    [DecidablePred (BadEvent (A := A))]
    (witness : EncodingWitness (A := A) (s := s) codes) :
    (badRestrictions (n := n) s (BadEvent (A := A))).card ≤ codes.card := by
  classical
  -- Сравниваем кардиналы подтипов через инъекцию `witness.encode`.
  have hcard :
      Fintype.card {ρ // ρ ∈ badRestrictions (n := n) s (BadEvent (A := A))}
        ≤ Fintype.card {c // c ∈ codes} := by
    exact Fintype.card_le_of_injective witness.encode witness.inj
  -- Перепишем кардиналы подтипов через `Finset.card`.
  have hbad :
      Fintype.card {ρ // ρ ∈ badRestrictions (n := n) s (BadEvent (A := A))} =
        (badRestrictions (n := n) s (BadEvent (A := A))).card := by
    classical
    simpa using
      (Fintype.card_coe
        (s := badRestrictions (n := n) s (BadEvent (A := A))))
  have hcodes :
      Fintype.card {c // c ∈ codes} = codes.card := by
    classical
    simpa using (Fintype.card_coe (s := codes))
  -- Собираем оценку, явно переписывая кардиналы.
  calc
    (badRestrictions (n := n) s (BadEvent (A := A))).card
        = Fintype.card {ρ // ρ ∈ badRestrictions (n := n) s (BadEvent (A := A))} := by
            simpa using hbad.symm
    _ ≤ Fintype.card {c // c ∈ codes} := by
          exact hcard
    _ = codes.card := by
          exact hcodes

lemma exists_good_restriction_of_encoding
    (A : CCDTAlgorithm n k ℓ t F) (s : Nat)
    (codes : Finset α)
    [DecidablePred (BadEvent (A := A))]
    (witness : EncodingWitness (A := A) (s := s) codes)
    (hcodes : codes.card < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadEvent (A := A) ρ := by
  classical
  have hbad :
      (badRestrictions (n := n) s (BadEvent (A := A))).card ≤ codes.card := by
    exact badRestrictions_card_le_of_encoding (A := A) (s := s) (codes := codes) witness
  have hlt :
      (badRestrictions (n := n) s (BadEvent (A := A))).card <
        (R_s (n := n) s).card := by
    exact lt_of_le_of_lt hbad hcodes
  exact exists_good_of_card_lt (n := n) (s := s)
    (bad := BadEvent (A := A)) hlt

/-!
### Оценка `bad` через product-коды

Если encoding идёт в произведение `R_{s-t} × codes`, то кардинал
плохих рестрикций не превосходит произведения кардиналов факторов.
-/

lemma badRestrictions_card_le_of_encoding_product
    {α : Type} [DecidableEq α]
    (A : CCDTAlgorithm n k ℓ t F) (s t' : Nat)
    (codes : Finset α)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product codes)) :
    (badRestrictions (n := n) s (BadEvent (A := A))).card
      ≤ (R_s (n := n) t').card * codes.card := by
  classical
  -- Используем общую лемму для encoding и разворачиваем кардинал продукта.
  have h := badRestrictions_card_le_of_encoding
    (A := A) (s := s) (codes := (R_s (n := n) t').product codes) witness
  -- `card_product` даёт ровно произведение кардиналов.
  simpa [Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-!
### Специализация для `Aux`

Часто encoding строится в продукт `R_{s-t} × Aux t k m`.  Тогда кардинал
плохих рестрикций ограничивается формулой `|R_{s-t}| * (2*k*m)^t`.
-/

lemma badRestrictions_card_le_of_aux_encoding
    (A : CCDTAlgorithm n k ℓ t F) (s t' k' m : Nat)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product (auxCodes n t k' m))) :
    (badRestrictions (n := n) s (BadEvent (A := A))).card
      ≤ (R_s (n := n) t').card * (2 * n * k' * m) ^ t := by
  classical
  have h :=
    badRestrictions_card_le_of_encoding_product
      (A := A) (s := s) (t' := t') (codes := auxCodes n t k' m) witness
  -- Разворачиваем кардинал `auxCodes` и используем формулу для `Aux`.
  simpa [auxCodes_card, card_Aux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-!
### Существование "хорошей" рестрикции из Aux-encoding

Если encoding построен в `R_{s-t} × Aux` и произведение кардиналов
строго меньше `|R_s|`, то существует хорошая рестрикция.
-/

lemma exists_good_restriction_of_aux_encoding
    (A : CCDTAlgorithm n k ℓ t F) (s t' k' m : Nat)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product (auxCodes n t k' m)))
    (hcodes :
      (R_s (n := n) t').card * (2 * n * k' * m) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadEvent (A := A) ρ := by
  classical
  -- Переписываем `codes.card` как произведение кардиналов.
  have hcodes' :
      ((R_s (n := n) t').product (auxCodes n t k' m)).card
        < (R_s (n := n) s).card := by
    -- `card_product` + формула для `Aux`.
    simpa [Finset.card_product, auxCodes_card, card_Aux,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcodes
  -- Применяем общий комбинаторный шаг из encoding.
  exact exists_good_restriction_of_encoding
    (A := A) (s := s)
    (codes := (R_s (n := n) t').product (auxCodes n t k' m))
    witness hcodes'

/-!
### Канонический encoding для CNF через CanonicalTrace (placeholder)

Полная реализация proof‑by‑encoding для CNF будет добавлена позже.
Пока оставляем этот блок как отдельную заглушку, чтобы не мешать сборке.
-/

section CanonicalTraceEncoding

open Core.CNF CanonicalTrace

variable {F0 : CNF n k}

axiom BadTraceEvent (t : Nat) (ρ : Restriction n) : Prop

axiom defaultCCDTAlgorithm (F0 : CNF n k) (t ℓ : Nat) :
  CCDTAlgorithm n k ℓ t [F0]

axiom canonicalTraceEncoding_witness
    (t s : Nat) :
    EncodingWitness (A := defaultCCDTAlgorithm (F0 := F0) (t := t) (ℓ := s))
      (s := s)
      (codes := (R_s (n := n) (s - t)).product (auxCodes n t k 1))

axiom exists_good_restriction_of_canonical_trace_encoding
    (t s : Nat) (hcodes :
      (R_s (n := n) (s - t)).card * (2 * n * k * 1) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadTraceEvent t ρ

end CanonicalTraceEncoding

end MultiSwitching
end AC0
end Pnp3
