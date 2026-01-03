import Core.BooleanBasics
import AC0.MultiSwitching.Restrictions

/-!
  pnp3/AC0/MultiSwitching/CanonicalTrace.lean

  Леммы про канонические трассы для CNF, которые нужны в proof-by-encoding.
  В частности, фиксируем, что длина трассы ровно на столько уменьшает число
  свободных координат рестрикции.
-/

namespace Pnp3
namespace Core
namespace CNF
namespace CanonicalTrace

open Core

variable {n w : Nat} {F : CNF n w}

/-- Число свободных координат после канонической трассы длины `t`. -/
lemma freeCount_finalRestriction
    {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    (finalRestriction trace).freeCount = ρ.freeCount - t := by
  -- Индукция по длине трассы, чтобы явно синхронизировать `t`
  -- и шаги канонического перехода.
  induction t generalizing ρ with
  | zero =>
      cases trace with
      | nil =>
          simp [finalRestriction]
  | succ t ih =>
      cases trace with
      | cons selection choice tail =>
          -- Хвост имеет длину `t`, применяем IH к нему.
          have ih' :
              (finalRestriction tail).freeCount
                = (ClausePendingWitness.Selection.nextRestriction (choice := choice)).freeCount - t := by
            simpa using (ih (ρ := ClausePendingWitness.Selection.nextRestriction (choice := choice)) (trace := tail))
          calc
            (finalRestriction (CanonicalTrace.cons selection choice tail)).freeCount
                = (finalRestriction tail).freeCount := by
                    simp [finalRestriction]
            _ = (ClausePendingWitness.Selection.nextRestriction (choice := choice)).freeCount - t := by
                  exact ih'
            _ = (ρ.freeCount - 1) - t := by
                  -- Переносим равенство `freeCount` через вычитание `t`.
                  have hstep :=
                    ClausePendingWitness.Selection.freeCount_nextRestriction (choice := choice)
                  exact congrArg (fun x => x - t) hstep
            _ = ρ.freeCount - (Nat.succ t) := by
                  -- `a - 1 - t = a - (1 + t) = a - (t + 1)`.
                  simpa [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-!
## Длина трассы не превосходит `freeCount`

Для канонической трассы длина не может превышать количество свободных
координат: каждый шаг фиксирует хотя бы одну свободную позицию.
-/

lemma length_le_freeCount
    {ρ : Restriction n} {t : Nat}
    (trace : CanonicalTrace (F := F) ρ t) :
    t ≤ ρ.freeCount := by
  induction t generalizing ρ with
  | zero =>
      simp
  | succ t ih =>
      cases trace with
      | cons selection choice tail =>
          -- Обозначим следующую рестрикцию.
          let ρ' :=
            ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := selection.witness) choice
          have hmem :
              choice.literal.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.Selection.literal_idx_mem_freeIndicesList
              (choice := choice)
          have hpos : 0 < ρ.freeCount :=
            Restriction.freeCount_pos_of_mem_freeIndicesList hmem
          have hih : t ≤ ρ'.freeCount := by
            simpa [ρ'] using (ih (ρ := ρ') (trace := tail))
          have hstep :
              ρ'.freeCount = ρ.freeCount - 1 := by
            simpa [ρ'] using
              ClausePendingWitness.Selection.freeCount_nextRestriction (choice := choice)
          have hle : t ≤ ρ.freeCount - 1 := by
            simpa [hstep] using hih
          have hle' : t + 1 ≤ ρ.freeCount := by
            have hle1 : t + 1 ≤ (ρ.freeCount - 1) + 1 :=
              Nat.add_le_add_right hle 1
            have hcancel : (ρ.freeCount - 1) + 1 = ρ.freeCount :=
              Nat.sub_add_cancel (Nat.succ_le_iff.mp hpos)
            simpa [Nat.succ_eq_add_one, hcancel] using hle1
          simpa [Nat.succ_eq_add_one] using hle'

/-- Каноническая трасса длины `t` переводит `R_s` в `R_{s-t}`. -/
lemma finalRestriction_mem_R_s
    {ρ : Restriction n} {s t : Nat}
    (hρ : ρ ∈ Pnp3.AC0.MultiSwitching.R_s (n := n) s)
    (trace : CanonicalTrace (F := F) ρ t) :
    finalRestriction trace ∈ Pnp3.AC0.MultiSwitching.R_s (n := n) (s - t) := by
  -- Используем характеристику `R_s` через `freeCount`.
  have hcount : ρ.freeCount = s :=
    (Pnp3.AC0.MultiSwitching.mem_R_s (n := n) (s := s)).1 hρ
  -- Переводим равенство в форму с `freeIndicesList.length`,
  -- чтобы избежать конфликтов `simp` при переписывании.
  have hcount' : ρ.freeIndicesList.length = s := by
    simpa [Restriction.freeCount] using hcount
  have hfinal_len :
      (finalRestriction trace).freeIndicesList.length
        = ρ.freeIndicesList.length - t := by
    simpa [Restriction.freeCount] using
      freeCount_finalRestriction (trace := trace)
  have hfinal : (finalRestriction trace).freeCount = s - t := by
    -- Возвращаемся к `freeCount`, уже имея замену `ρ.freeIndicesList.length = s`.
    simpa [Restriction.freeCount, hcount'] using hfinal_len
  exact (Pnp3.AC0.MultiSwitching.mem_R_s (n := n) (s := s - t)).2 hfinal

end CanonicalTrace
end CNF
end Core
end Pnp3
