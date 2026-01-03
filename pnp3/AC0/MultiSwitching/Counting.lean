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
      simpa using (Fintype.card_coe (s := codes))
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
    simp [codes, Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  -- Подставляем кардинал `AuxSimple`.
  have haux :
      (auxSimpleCodes n t).card = (2 * n) ^ t := by
    simpa [Nat.mul_comm] using (card_AuxSimple (n := n) (t := t))
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
      simpa using (Fintype.card_coe (s := codes))
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
    simp [codes, Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have haux :
      (auxFamilySimpleCodes (F := F) t).card =
        (F.length + 1) * (2 * n) ^ t := by
    simp [auxFamilySimpleCodes_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  calc
    (badRestrictions (n := n) s (BadFamily (F := F) t)).card
        ≤ codes.card := hcard
    _ = (R_s (n := n) (s - t)).card * (auxFamilySimpleCodes (F := F) t).card :=
        hcodes_card
    _ = (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t := by
          simp [haux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

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
        exact Subtype.ext (henc (by simpa using hxy))
    have hcard' := Fintype.card_le_of_injective (f := hsub)
    simpa using hcard'
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

lemma card_bad_lt_card_all_of_cnf_family_bound_det
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    (badRestrictions (n := n) s (BadFamily_deterministic (F := F) t)).card
      < (R_s (n := n) s).card := by
  classical
  exact lt_of_le_of_lt
    (badRestrictions_card_le_cnf_family_aux_det (F := F) (s := s) (t := t)) hbound

lemma exists_good_restriction_cnf_family_of_bound_det
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadFamily_deterministic (F := F) t ρ := by
  classical
  exact @exists_good_of_card_lt (n := n) (s := s)
    (bad := BadFamily_deterministic (F := F) t)
    (instDecidableBadFamilyDet (F := F) (t := t))
    (card_bad_lt_card_all_of_cnf_family_bound_det (F := F) (s := s) (t := t) hbound)

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
