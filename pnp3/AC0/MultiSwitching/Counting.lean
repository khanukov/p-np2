import Mathlib.Data.Fintype.Card
import AC0.MultiSwitching.Restrictions
import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.TraceBridge

/-!
  pnp3/AC0/MultiSwitching/Counting.lean

  Базовые комбинаторные леммы для модели `R_s` (равномерное распределение
  по рестрикциям с фиксированным числом свободных координат).

  Эти результаты нужны для шага "вероятность → существование": если множество
  "плохих" рестрикций имеет строго меньший кардинал, чем всё `R_s`, то
  существует "хорошая" рестрикция. Леммы здесь не зависят от конкретного
  определения "плохих" рестрикций и потому пригодны для будущей реализации
  multi‑switching (encoding/injection).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w : Nat}

noncomputable section

local instance instDecidableBadCNF (F : CNF n w) (t : Nat) :
    DecidablePred (BadCNF (F := F) t) := by
  classical
  exact Classical.decPred _

local instance instDecidableBadFamily (F : FormulaFamily n w) (t : Nat) :
    DecidablePred (BadFamily (F := F) t) := by
  classical
  exact Classical.decPred _

local instance instDecidableBadFamilyDet (F : FormulaFamily n w) (t : Nat) :
    DecidablePred (BadFamily_deterministic (F := F) t) := by
  classical
  exact Classical.decPred _

/-!
### Кардинал `badRestrictions` через явный предикат

Связываем `badRestrictions` с подтипом по явному предикату
`freeIndicesList.length = s ∧ bad`, чтобы проще использовать `Fintype.card`.
-/

lemma badRestrictions_card_eq_fintype
    {n s : Nat} {bad : Restriction n → Prop} [DecidablePred bad] :
    (badRestrictions (n := n) s bad).card =
      Fintype.card {ρ // ρ.freeIndicesList.length = s ∧ bad ρ} := by
  classical
  -- Эквивалентность между `↥badRestrictions` и подтипом по явному предикату.
  let e :
      (↑(badRestrictions (n := n) s bad)) ≃
        {ρ // ρ.freeIndicesList.length = s ∧ bad ρ} :=
    { toFun := fun ρ =>
        have hmem : ρ.1 ∈ R_s (n := n) s :=
          (mem_badRestrictions (n := n) (s := s) (bad := bad)).1 ρ.2 |>.1
        have hbad : bad ρ.1 :=
          (mem_badRestrictions (n := n) (s := s) (bad := bad)).1 ρ.2 |>.2
        have hlen : ρ.1.freeIndicesList.length = s := by
          have hcount : ρ.1.freeCount = s := (mem_R_s (n := n) (s := s)).1 hmem
          simpa [Restriction.freeCount] using hcount
        ⟨ρ.1, hlen, hbad⟩
      invFun := fun ρ =>
        have hmem : ρ.1 ∈ R_s (n := n) s := by
          have hcount : ρ.1.freeCount = s := by
            simpa [Restriction.freeCount] using ρ.2.1
          exact (mem_R_s (n := n) (s := s)).2 hcount
        have hmem' : ρ.1 ∈ badRestrictions (n := n) s bad := by
          exact (mem_badRestrictions (n := n) (s := s) (bad := bad)).2 ⟨hmem, ρ.2.2⟩
        ⟨ρ.1, hmem'⟩
      left_inv := by
        intro ρ
        ext
        rfl
      right_inv := by
        intro ρ
        ext
        rfl }
  -- Переводим `Fintype.card` эквивалентных типов в кардинал финсета.
  have hcard := Fintype.card_congr e
  calc
    (badRestrictions (n := n) s bad).card
        = Fintype.card (↑(badRestrictions (n := n) s bad)) := by
            symm
            exact (Fintype.card_coe (s := badRestrictions (n := n) s bad))
    _ = Fintype.card {ρ // ρ.freeIndicesList.length = s ∧ bad ρ} := hcard

lemma fintype_card_badRestrictions_eq
    {n s : Nat} {bad : Restriction n → Prop} [DecidablePred bad] :
    Fintype.card {ρ // ρ ∈ badRestrictions (n := n) s bad} =
      Fintype.card {ρ // ρ.freeIndicesList.length = s ∧ bad ρ} := by
  classical
  calc
    Fintype.card {ρ // ρ ∈ badRestrictions (n := n) s bad}
        = (badRestrictions (n := n) s bad).card := by
            simpa using
              (Fintype.card_coe (s := badRestrictions (n := n) s bad))
    _ = Fintype.card {ρ // ρ.freeIndicesList.length = s ∧ bad ρ} := by
            simpa using
              (badRestrictions_card_eq_fintype (n := n) (s := s) (bad := bad))

/-!
## Специализация: CNF depth‑2, оценка через encoding/injection

Это следующий «железный» шаг после построения `encodeBadCNF`:
мы получаем верхнюю границу на количество плохих рестрикций
через инъекцию в `R_{s-t} × AuxSimple` (алфавит `2*n`).
-/

lemma badRestrictions_card_le_cnf_aux
    {n w s t : Nat} (F : CNF n w) :
    (badRestrictions (n := n) s (BadCNF (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card * (2 * n) ^ t := by
  classical
  -- Построим инъекцию из bad‑рестрикций в `R_{s-t} × AuxSimple`.
  let codes := (R_s (n := n) (s - t)).product (auxSimpleCodes n t)
  have henc :
      Function.Injective (encodeBadCNF (F := F) (s := s) (t := t)) :=
    encodeBadCNF_injective (F := F) (s := s) (t := t)
  have hcard :
      (badRestrictions (n := n) s (BadCNF (F := F) t)).card
        ≤ codes.card := by
    -- Приводим `badRestrictions` к подтипу, на который действует `encodeBadCNF`.
    have hsub :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadCNF (F := F) t)}
          ≤ Fintype.card {c // c ∈ codes} := by
      let toBadCNF :
          {ρ // ρ ∈ badRestrictions (n := n) s (BadCNF (F := F) t)}
            → BadInRsCNF (F := F) s t :=
        fun ρbad =>
          let hmem :=
            (mem_badRestrictions (n := n) (s := s) (bad := BadCNF (F := F) t)).1
              ρbad.property
          ⟨ρbad.1, hmem.1, hmem.2⟩
      have hsub_inj : Function.Injective toBadCNF := by
        intro x y hxy
        apply Subtype.ext
        simpa using congrArg Subtype.val hxy
      exact Fintype.card_le_of_injective
        (fun ρbad => encodeBadCNF (F := F) (s := s) (t := t) (toBadCNF ρbad))
        (fun x y hxy => hsub_inj (henc hxy))
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadCNF (F := F) t)} =
          (badRestrictions (n := n) s (BadCNF (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s (BadCNF (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simp [Fintype.card_coe]
    calc
      (badRestrictions (n := n) s (BadCNF (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s (BadCNF (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hsub
      _ = codes.card := hcodes
  -- Разворачиваем кардинал продукта `codes`.
  have hcodes_card :
      codes.card = (R_s (n := n) (s - t)).card * (auxSimpleCodes n t).card := by
    simp [codes, Finset.card_product, Nat.mul_comm]
  -- Подставляем кардинал `AuxSimple`.
  have haux :
      (auxSimpleCodes n t).card = (2 * n) ^ t := by
    simp [Nat.mul_comm]
  calc
    (badRestrictions (n := n) s (BadCNF (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (auxSimpleCodes n t).card := hcodes_card
    _ = (R_s (n := n) (s - t)).card * (2 * n) ^ t := by
          simp [haux, Nat.mul_comm]

/-!
### Семейство CNF: оценка bad‑рестрикций через encoding
-/

lemma badRestrictions_card_le_cnf_family_aux
    {n w s t : Nat} (F : FormulaFamily n w) :
    (badRestrictions (n := n) s (BadFamily (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t := by
  classical
  let codes := (R_s (n := n) (s - t)).product (auxFamilySimpleCodes (F := F) t)
  have henc :
      Function.Injective
        (encodeBadFamilyCNF (F := F) (s := s) (t := t)) :=
    encodeBadFamilyCNF_injective (F := F) (s := s) (t := t)
  have hcard :
      (badRestrictions (n := n) s (BadFamily (F := F) t)).card
        ≤ codes.card := by
    have hsub :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily (F := F) t)}
          ≤ Fintype.card {c // c ∈ codes} := by
      let toBadFamily :
          {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily (F := F) t)}
            → BadFamilyInRsCNF (F := F) s t :=
        fun ρbad =>
          let hmem :=
            (mem_badRestrictions (n := n) (s := s) (bad := BadFamily (F := F) t)).1
              ρbad.property
          ⟨ρbad.1, hmem.1, hmem.2⟩
      have hsub_inj : Function.Injective toBadFamily := by
        intro x y hxy
        apply Subtype.ext
        simpa using congrArg Subtype.val hxy
      exact Fintype.card_le_of_injective
        (fun ρbad => encodeBadFamilyCNF (F := F) (s := s) (t := t) (toBadFamily ρbad))
        (fun x y hxy => hsub_inj (henc hxy))
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily (F := F) t)} =
          (badRestrictions (n := n) s (BadFamily (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s (BadFamily (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simp [Fintype.card_coe]
    calc
      (badRestrictions (n := n) s (BadFamily (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hsub
      _ = codes.card := hcodes
  have hcodes_card :
      codes.card =
        (R_s (n := n) (s - t)).card * (auxFamilySimpleCodes (F := F) t).card := by
    simp [codes, Finset.card_product, Nat.mul_comm]
  have haux :
      (auxFamilySimpleCodes (F := F) t).card =
        (F.length + 1) * (2 * n) ^ t := by
    simp [auxFamilySimpleCodes_card, Nat.mul_comm]
  calc
    (badRestrictions (n := n) s (BadFamily (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (auxFamilySimpleCodes (F := F) t).card :=
        hcodes_card
    _ = (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_assoc]

/-!
### Семейство CNF (детерминированный BadFamily): оценка через Aux

Здесь мы используем «полный» алфавит `Aux`, где каждый шаг хранит
`BitFix` (переменная + значение), позицию литерала и индекс формулы.
Эта версия нужна для Stage‑1: инъекция должна быть восстановимой.
-/

lemma badRestrictions_card_le_cnf_family_det_aux
    {n w s t : Nat} (F : FormulaFamily n w) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t := by
  classical
  let codes :=
    (R_s (n := n) (s - t)).product
      (auxCodes n t (w + 1) (F.length + 1))
  have henc :
      Function.Injective
        (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t)) :=
    encodeBadFamilyDetCNF_aux_injective (F := F) (s := s) (t := t)
  have hcard :
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := by
    have hsub :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s
              (BadFamily_deterministic (F := F) t)}
          ≤ Fintype.card {c // c ∈ codes} := by
      let toBadFamily :
          {ρ // ρ ∈ badRestrictions (n := n) s
            (BadFamily_deterministic (F := F) t)}
            → BadFamilyDetInRsCNF (F := F) s t :=
        fun ρbad =>
          let hmem :=
            (mem_badRestrictions (n := n) (s := s)
              (bad := BadFamily_deterministic (F := F) t)).1
              ρbad.property
          ⟨ρbad.1, hmem.1, hmem.2⟩
      have hsub_inj : Function.Injective toBadFamily := by
        intro x y hxy
        apply Subtype.ext
        simpa using congrArg Subtype.val hxy
      exact Fintype.card_le_of_injective
        (fun ρbad =>
          encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t)
            (toBadFamily ρbad))
        (fun x y hxy => hsub_inj (henc hxy))
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s
              (BadFamily_deterministic (F := F) t)}
          = (badRestrictions (n := n) s
              (BadFamily_deterministic (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s
            (BadFamily_deterministic (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simpa using (Fintype.card_coe (s := codes))
    calc
      (badRestrictions (n := n) s
          (BadFamily_deterministic (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s
                (BadFamily_deterministic (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hsub
      _ = codes.card := hcodes
  have hcodes_card :
      codes.card =
        (R_s (n := n) (s - t)).card
          * (auxCodes n t (w + 1) (F.length + 1)).card := by
    simp [codes, Finset.card_product, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]
  have haux :
      (auxCodes n t (w + 1) (F.length + 1)).card
        = (2 * n * (w + 1) * (F.length + 1)) ^ t := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using (card_Aux (n := n) (t := t) (k := w + 1) (m := F.length + 1))
  calc
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card
          * (auxCodes n t (w + 1) (F.length + 1)).card := hcodes_card
    _ = (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-!
### Canonical CCDT (BadEvent): counting bound через Aux-encoding

Эта лемма закрывает Stage‑2 на уровне `BadEvent` для канонического CCDT:
мы используем готовый `EncodingWitness` из `Encoding.lean` и общую
комбинаторную оценку `badRestrictions_card_le_of_aux_encoding`.

Результат имеет тот же формат, что и для детерминированного `BadFamily`,
но теперь предикат «плохое событие» записан через стандартный интерфейс
`BadEvent (A := canonicalCCDTAlgorithmCNF ...)`.
-/

lemma badRestrictions_card_le_canonicalCCDT_aux
    {n w s t : Nat} (F : FormulaFamily n w) :
    (badRestrictions (n := n) s
        (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).card
      ≤ (R_s (n := n) (s - t)).card
        * (2 * n * (w + 1) * (F.length + 1)) ^ t := by
  classical
  -- Используем готовое кодирование для BadEvent канонического CCDT.
  have witness :=
    encodingWitness_canonicalCCDT_CNF (F := F) (t := t) (s := s)
  -- Применяем общий bound для Aux‑encoding.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (badRestrictions_card_le_of_aux_encoding
      (A := canonicalCCDTAlgorithmCNF (F := F) t)
      (s := s) (t' := s - t) (k' := w + 1) (m := F.length + 1)
      (witness := witness))

/-!
### Canonical CCDT (BadEvent): existence‑шаг из Aux‑границы

Если задана строгая оценка кардиналов для полного Aux‑кода, получаем
существование хорошей рестрикции для канонического CCDT, то есть
`¬ BadEvent (A := canonicalCCDTAlgorithmCNF ...)`.
-/

lemma exists_good_restriction_canonicalCCDT_of_bound_aux
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s,
      ¬ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ := by
  classical
  -- Ограничиваем число плохих рестрикций через Aux‑код.
  have hbad :
      (badRestrictions (n := n) s
        (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).card
        < (R_s (n := n) s).card := by
    have hle := badRestrictions_card_le_canonicalCCDT_aux (F := F) (s := s) (t := t)
    exact lt_of_le_of_lt hle hbound
  -- Применяем общий критерий существования good‑рестрикции.
  exact exists_good_of_card_lt
    (n := n) (s := s)
    (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t)) hbad

/-!
### Дет. BadFamily: existence‑шаг из Aux‑границы

Если задана строгая оценка кардиналов для полного Aux‑кода,
получаем существование хорошей рестрикции (¬BadFamily_deterministic).
-/

lemma exists_good_restriction_cnf_family_of_bound_det_aux
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily_deterministic (F := F) t ρ := by
  classical
  -- Сначала ограничиваем число плохих рестрикций через Aux‑код.
  have hbad :
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        < (R_s (n := n) s).card := by
    have hle := badRestrictions_card_le_cnf_family_det_aux (F := F) (s := s) (t := t)
    exact lt_of_le_of_lt hle hbound
  -- Затем применяем общий критерий существования good‑рестрикции.
  exact exists_good_of_card_lt
    (n := n) (s := s) (bad := BadFamily_deterministic (F := F) t) hbad

/-!
## Детерминированный BadFamily (пока через «толстый» алфавит)

Этот шаг полезен, чтобы отделить детерминизацию от смены алфавита.
Позже `AuxSimple` будет заменён на `AuxTraceSmall`.
-/

lemma badRestrictions_card_le_cnf_family_aux_det
    {n w s t : Nat} (F : FormulaFamily n w) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t := by
  classical
  let codes := (R_s (n := n) (s - t)).product (auxFamilySimpleCodes (F := F) t)
  have henc :
      Function.Injective (encodeBadFamilyDetCNF (F := F) (s := s) (t := t)) :=
    encodeBadFamilyDetCNF_injective (F := F) (s := s) (t := t)
  have hcard :
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := by
    have hsub :
        {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)}
          ↪ {c // c ∈ codes} := by
      refine ⟨fun ρbad => ?_, ?_⟩
      · have hmem : ρbad.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s) (bad := BadFamily_deterministic (F := F) t)).1
            ρbad.2 |>.1
        have hbad : BadFamily_deterministic (F := F) t ρbad.1 := by
          exact (mem_badRestrictions (n := n) (s := s) (bad := BadFamily_deterministic (F := F) t)).1
            ρbad.2 |>.2
        exact encodeBadFamilyDetCNF (F := F) (s := s) (t := t) ⟨ρbad.1, hmem, hbad⟩
      · intro x y hxy
        -- Переносим равенство кодов в равенство исходных рестрикций.
        have hmemx : x.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.1
        have hbadx : BadFamily_deterministic (F := F) t x.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.2
        have hmemy : y.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.1
        have hbady : BadFamily_deterministic (F := F) t y.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.2
        have hxy' :
            encodeBadFamilyDetCNF (F := F) (s := s) (t := t) ⟨x.1, hmemx, hbadx⟩
              = encodeBadFamilyDetCNF (F := F) (s := s) (t := t) ⟨y.1, hmemy, hbady⟩ := by
            simpa using hxy
        have henc' := henc hxy'
        have : x.1 = y.1 := by
          simpa using congrArg Subtype.val henc'
        exact Subtype.ext this
    have hcard' :=
      Fintype.card_le_of_injective (f := hsub) hsub.injective
    -- Переводим кардиналы подтипов в `Finset.card`.
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} =
          (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simpa using (Fintype.card_coe (s := codes))
    calc
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hcard'
      _ = codes.card := hcodes
  have hcodes_card :
      codes.card =
        (R_s (n := n) (s - t)).card * (auxFamilySimpleCodes (F := F) t).card := by
    simp [codes, Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have haux :
      (auxFamilySimpleCodes (F := F) t).card =
        (F.length + 1) * (2 * n) ^ t := by
    simp [auxFamilySimpleCodes_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  calc
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (auxFamilySimpleCodes (F := F) t).card := hcodes_card
    _ = (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-!
## Детерминированный BadFamily с расширенным кодом

Используем код `FamilyTraceCodeVar`, в котором хранится и полный список
присвоений, и позиции литералов. База увеличивается до
`(2*n)^t * (2*(w+1))^t`, но инъективность становится прямой.
-/

lemma badRestrictions_card_le_cnf_family_aux_det_var
    {n w s t : Nat} (F : FormulaFamily n w) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card * (F.length + 1)
          * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
  classical
  let codes := (R_s (n := n) (s - t)).product (familyTraceCodeVarCodes (F := F) t)
  have henc :
      Function.Injective (encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t)) :=
    encodeBadFamilyDetCNF_var_injective (F := F) (s := s) (t := t)
  have hcard :
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := by
    have hsub :
        {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)}
          ↪ {c // c ∈ codes} := by
      refine ⟨fun ρbad => ?_, ?_⟩
      · have hmem : ρbad.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 ρbad.2 |>.1
        have hbad : BadFamily_deterministic (F := F) t ρbad.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 ρbad.2 |>.2
        exact encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) ⟨ρbad.1, hmem, hbad⟩
      · intro x y hxy
        -- Переносим равенство кодов в равенство исходных рестрикций.
        have hmemx : x.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.1
        have hbadx : BadFamily_deterministic (F := F) t x.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.2
        have hmemy : y.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.1
        have hbady : BadFamily_deterministic (F := F) t y.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.2
        have hxy' :
            encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) ⟨x.1, hmemx, hbadx⟩
              = encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) ⟨y.1, hmemy, hbady⟩ := by
            simpa using hxy
        have henc' := henc hxy'
        have : x.1 = y.1 := by
          simpa using congrArg Subtype.val henc'
        exact Subtype.ext this
    have hcard' := Fintype.card_le_of_injective (f := hsub) hsub.injective
    -- Переводим кардиналы подтипов в `Finset.card`.
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} =
          (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simpa using (Fintype.card_coe (s := codes))
    calc
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hcard'
      _ = codes.card := hcodes
  have hcodes_card :
      codes.card =
        (R_s (n := n) (s - t)).card * (familyTraceCodeVarCodes (F := F) t).card := by
    simp [codes, Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have haux :
      (familyTraceCodeVarCodes (F := F) t).card =
        (F.length + 1) * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
    calc
      (familyTraceCodeVarCodes (F := F) t).card
          = Fintype.card (FamilyTraceCodeVar (F := F) t) := by
            simpa using (familyTraceCodeVarCodes_card (F := F) t)
      _ = (F.length + 1) * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
            simpa using (card_FamilyTraceCodeVar (F := F) t)
  calc
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (familyTraceCodeVarCodes (F := F) t).card := hcodes_card
    _ = (R_s (n := n) (s - t)).card * (F.length + 1)
          * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma card_bad_lt_card_all_of_cnf_family_bound_small
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadFamily (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt
    (badRestrictions_card_le_cnf_family_aux (F := F) (s := s) (t := t)) hbound

lemma exists_good_restriction_cnf_family_of_bound_small
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily (F := F) t ρ := by
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadFamily (F := F) t)
    (instDecidableBadFamily (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_family_bound_small (F := F) (s := s) (t := t) hbound)

lemma card_bad_lt_card_all_of_cnf_family_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadFamily (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt
    (badRestrictions_card_le_cnf_family_aux (F := F) (s := s) (t := t)) hbound

/-!
### Детерминированный вариант: bound с расширенным кодом

Здесь мы используем `FamilyTraceCodeVar`, поэтому база увеличивается
на фактор `(2*n)^t * (2*(w+1))^t`. Это сохраняет инъективность и
даёт прямую оценку для `BadFamily_deterministic`.
-/

lemma card_bad_lt_card_all_of_cnf_family_bound_det_var
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1)
          * (2 * n) ^ t * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt
    (badRestrictions_card_le_cnf_family_aux_det_var (F := F) (s := s) (t := t)) hbound

lemma exists_good_restriction_cnf_family_of_bound_det_var
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1)
          * (2 * n) ^ t * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily_deterministic (F := F) t ρ := by
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadFamily_deterministic (F := F) t)
    (instDecidableBadFamilyDet (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_family_bound_det_var (F := F) (s := s) (t := t) hbound)

/-!
### Детерминированный BadFamily: малый алфавит (BParam)

Этот блок оставляет явной гипотезу об инъективности малого encoding.
После доказательства `encodeBadFamilyDetCNF_small_injective` он даёт
полную цепочку до `exists_good_restriction`.
-/

lemma badRestrictions_card_le_cnf_family_aux_det_small
    {n w s t : Nat} (F : FormulaFamily n w)
    (henc :
      Function.Injective (encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t))) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      ≤ (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t := by
  classical
  let codes := (R_s (n := n) (s - t)).product (auxTraceFamilySmallCodes (F := F) t)
  have hcard :
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := by
    have hsub :
        {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)}
          ↪ {c // c ∈ codes} := by
      refine ⟨fun ρbad => ?_, ?_⟩
      · have hmem : ρbad.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 ρbad.2 |>.1
        have hbad : BadFamily_deterministic (F := F) t ρbad.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 ρbad.2 |>.2
        exact encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t) ⟨ρbad.1, hmem, hbad⟩
      · intro x y hxy
        -- Переносим равенство кодов в равенство исходных рестрикций.
        have hmemx : x.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.1
        have hbadx : BadFamily_deterministic (F := F) t x.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 x.2 |>.2
        have hmemy : y.1 ∈ R_s (n := n) s := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.1
        have hbady : BadFamily_deterministic (F := F) t y.1 := by
          exact (mem_badRestrictions (n := n) (s := s)
            (bad := BadFamily_deterministic (F := F) t)).1 y.2 |>.2
        have hxy' :
            encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t) ⟨x.1, hmemx, hbadx⟩
              = encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t) ⟨y.1, hmemy, hbady⟩ := by
            simpa using hxy
        have henc' := henc hxy'
        have : x.1 = y.1 := by
          simpa using congrArg Subtype.val henc'
        exact Subtype.ext this
    have hcard' :=
      Fintype.card_le_of_injective (f := hsub) hsub.injective
    -- Переводим кардиналы подтипов в `Finset.card`.
    have hbad :
        Fintype.card
            {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} =
          (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card := by
      simpa using
        (Fintype.card_coe
          (s := badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)))
    have hcodes :
        Fintype.card {c // c ∈ codes} = codes.card := by
      simpa using (Fintype.card_coe (s := codes))
    calc
      (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
          = Fintype.card
              {ρ // ρ ∈ badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)} := by
              simpa using hbad.symm
      _ ≤ Fintype.card {c // c ∈ codes} := hcard'
      _ = codes.card := hcodes
  have hcodes_card :
      codes.card =
        (R_s (n := n) (s - t)).card * (auxTraceFamilySmallCodes (F := F) t).card := by
    simp [codes, Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have haux :
      (auxTraceFamilySmallCodes (F := F) t).card =
        (F.length + 1) * (2 * (w + 1)) ^ t := by
    calc
      (auxTraceFamilySmallCodes (F := F) t).card
          = Fintype.card (AuxTraceFamilySmall (F := F) t) := by
            simpa using (auxTraceFamilySmallCodes_card (F := F) t)
      _ = (F.length + 1) * (2 * (w + 1)) ^ t := by
            simpa using (card_AuxTraceFamilySmall (F := F) t)
  calc
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (auxTraceFamilySmallCodes (F := F) t).card := hcodes_card
    _ = (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma card_bad_lt_card_all_of_cnf_family_bound_det_small
    {n w s t : Nat} (F : FormulaFamily n w)
    (henc :
      Function.Injective (encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t)))
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt
    (badRestrictions_card_le_cnf_family_aux_det_small (F := F) (s := s) (t := t) henc) hbound

lemma exists_good_restriction_cnf_family_of_bound_det_small
    {n w s t : Nat} (F : FormulaFamily n w)
    (henc :
      Function.Injective (encodeBadFamilyDetCNF_small (F := F) (s := s) (t := t)))
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily_deterministic (F := F) t ρ := by
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadFamily_deterministic (F := F) t)
    (instDecidableBadFamilyDet (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_family_bound_det_small
      (F := F) (s := s) (t := t) henc hbound)

lemma exists_good_restriction_cnf_family_of_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      -- Важно: здесь используется алфавит `2*n` из `AuxSimple`, а не `2*(w+1)`.
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily (F := F) t ρ := by
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadFamily (F := F) t)
    (instDecidableBadFamily (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_family_bound (F := F) (s := s) (t := t) hbound)

/-!
### Шаг 3.2: строгая оценка (через числовую гипотезу)

В финальной версии параметров нужно доказать, что
`|R_{s-t}| * (2n)^t < |R_s|`.  Здесь мы формализуем **универсальную**
лемму: если числовая оценка дана, то плохие рестрикции строго меньше
всего `R_s`, и значит существует хорошая рестрикция.

Это место — «точка подключения» для выбора параметров.
-/

lemma card_bad_lt_card_all_of_cnf_bound
    {n w s t : Nat} (F : CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadCNF (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt (badRestrictions_card_le_cnf_aux (F := F) (s := s) (t := t)) hbound

lemma exists_good_restriction_cnf_of_bound
    {n w s t : Nat} (F : CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadCNF (F := F) t ρ := by
  -- Комбинируем strict‑оценку с общим комбинаторным шагом.
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadCNF (F := F) t)
    (instDecidableBadCNF (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_bound (F := F) (s := s) (t := t) hbound)

end

end MultiSwitching
end AC0
end Pnp3
