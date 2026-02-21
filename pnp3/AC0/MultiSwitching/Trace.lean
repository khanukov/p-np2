import Core.BooleanBasics
import AC0.MultiSwitching.CanonicalTrace
import AC0.MultiSwitching.Definitions

/-!
  pnp3/AC0/MultiSwitching/Trace.lean

  Каноническая «трасса» для depth-2 (CNF) в удобной форме.

  Цель этого файла — дать **детерминированное** представление пути в
  каноническом DT, чтобы позже использовать его в encoding/injection.
  Мы сознательно фиксируем минимальный, но достаточный формат трассы:

  * индекс переменной (Fin n),
  * значение ветки (Bool),
  * индекс клаузы (Nat, с леммой о корректной границе),
  * позиция выбранного литерала (Nat).

  Важно: индексы записаны как `Nat`, но ниже есть леммы, подтверждающие,
  что они лежат в корректных диапазонах (например, `clauseIndex < #clauses`).
  Это позволяет позже перейти к `Fin`-коду без переписывания логики трассы.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w : Nat}

/-!
## TraceStep / Trace

`TraceStep` — один шаг канонического DT:
мы храним выбранную переменную, значение ветки,
номер клаузы и позицию литерала внутри этой клаузы.
-/

structure TraceStep (F : CNF n w) where
  /-- Индекс ветвящейся переменной. -/
  var : Fin n
  /-- Значение, которое задаёт ветвь. -/
  value : Bool
  /-- Индекс выбранной «первой pending» клаузы. -/
  clauseIndex : Nat
  /-- Позиция выбранного свободного литерала (внутренний индекс). -/
  literalIndex : Nat
  deriving Repr

/-!
Фиксированная длина трассы `t`: в дальнейшем удобно считать кардинальности
для `Vector` (например, `B^t`).
-/
abbrev Trace (F : CNF n w) (t : Nat) : Type :=
  Vector (TraceStep F) t

/-!
## Из канонической трассы в `Trace`

Ниже мы переводим `Core.CNF.CanonicalTrace` в список шагов,
а затем упаковываем его в `Vector` длины `t`.
-/

namespace CanonicalTrace

variable {F : CNF n w}

private lemma leadingClauses_length_lt
    {ρ : Restriction n}
    (selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses) :
    selection.leadingClauses.length < F.clauses.length := by
  -- `clauses = leading ++ clause :: suffix`
  have hlen :
      F.clauses.length =
        selection.leadingClauses.length + 1 + selection.suffix.length := by
    have h := congrArg List.length selection.clausesDecomposition
    -- length (leading ++ clause :: suffix) = length leading + 1 + length suffix
    simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hlt :
      selection.leadingClauses.length <
        selection.leadingClauses.length + 1 + selection.suffix.length := by
    have h1 : selection.leadingClauses.length < selection.leadingClauses.length + 1 :=
      Nat.lt_succ_self _
    have h2 :
        selection.leadingClauses.length + 1
          ≤ selection.leadingClauses.length + 1 + selection.suffix.length := by
      exact Nat.le_add_right _ _
    exact lt_of_lt_of_le h1 h2
  simpa [hlen] using hlt

/-- Шаг трассы, извлечённый из канонического выбора. -/
noncomputable def stepOfSelection
    {ρ : Restriction n}
    (selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses)
    (choice : ClausePendingWitness.Selection selection.witness) :
    TraceStep F :=
  { var := choice.literal.idx
    value := choice.value
    clauseIndex := selection.leadingClauses.length
    literalIndex := choice.index.1 }

/-!
Список шагов для канонической трассы.
Мы сохраняем исходный порядок, чтобы позже можно было однозначно
восстанавливать ограничение.
-/
noncomputable def stepsList :
    {ρ : Restriction n} → {t : Nat} →
      Core.CNF.CanonicalTrace (F := F) ρ t → List (TraceStep F)
  | _, _, Core.CNF.CanonicalTrace.nil => []
  | _, _, Core.CNF.CanonicalTrace.cons selection choice tail =>
      stepOfSelection (selection := selection) (choice := choice) :: stepsList tail

@[simp] lemma stepsList_length :
    ∀ {ρ : Restriction n} {t : Nat}
      (trace : Core.CNF.CanonicalTrace (F := F) ρ t),
        (stepsList trace).length = t
  | _, _, Core.CNF.CanonicalTrace.nil => by
      rfl
  | _, _, Core.CNF.CanonicalTrace.cons selection choice tail => by
      have htail := stepsList_length (trace := tail)
      simp [stepsList, htail]

/-- Преобразование канонической трассы в `Trace` фиксированной длины. -/
noncomputable def toTrace
    {ρ : Restriction n} {t : Nat}
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    Trace F t :=
  ⟨(stepsList trace).toArray, by
    -- Длину массива извлекаем напрямую из `stepsList_length`.
    simp [List.size_toArray, stepsList_length (trace := trace)]⟩

@[simp] lemma clauseIndex_lt
    {ρ : Restriction n}
    (selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses)
    (choice : ClausePendingWitness.Selection selection.witness) :
    (stepOfSelection (selection := selection) (choice := choice)).clauseIndex
      < F.clauses.length := by
  -- Ссылаемся на общую лемму о длине `leadingClauses`.
  simpa [stepOfSelection] using
    (leadingClauses_length_lt (selection := selection))

end CanonicalTrace

/-!
## Bad-событие для depth-2

Мы фиксируем `BadCNF` как существование канонической трассы длины `t`.
Это достаточная и детерминированная форма для encoding/injection.
-/

def BadCNF (F : CNF n w) (t : Nat) (ρ : Restriction n) : Prop :=
  Nonempty (Core.CNF.CanonicalTrace (F := F) ρ t)

noncomputable def traceOfBadCNF {F : CNF n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadCNF (F := F) t ρ) : Trace F t :=
  CanonicalTrace.toTrace (trace := Classical.choice hbad)

/-!
## Базовая оценка: Bad → t ≤ freeCount

Для канонической трассы длина не может превышать число свободных
координат.  Это используется в "малой n" ветке.
-/

lemma badCNF_length_le_freeCount
    {F : CNF n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadCNF (F := F) t ρ) :
    t ≤ ρ.freeCount := by
  rcases hbad with ⟨trace⟩
  exact Core.CNF.CanonicalTrace.length_le_freeCount (trace := trace)

/-!
## Bad-событие для семейства формул

`BadFamily` означает, что **какая-то** формула из списка имеет
каноническую трассу длины `t`. Для корректного encoding нам важна
детерминизация: мы всегда выбираем **первую** формулу по индексу.
-/

def BadFamily (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ i, ∃ hi : i < F.length, BadCNF (F := F.get ⟨i, hi⟩) t ρ

lemma badFamily_length_le_freeCount
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    t ≤ ρ.freeCount := by
  rcases hbad with ⟨i, hi, hbad_i⟩
  exact badCNF_length_le_freeCount (hbad := hbad_i)

noncomputable def firstBadIndex
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) : Nat :=
  by
    classical
    exact Nat.find hbad

lemma firstBadIndex_spec
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    ∃ hi : firstBadIndex (F := F) (t := t) (ρ := ρ) hbad < F.length,
      BadCNF (F := F.get ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad, hi⟩) t ρ := by
  -- `Nat.find_spec` даёт свидетеля с минимальным индексом.
  classical
  simpa [firstBadIndex] using (Nat.find_spec hbad)

/-- Каноническая трасса, извлечённая из `BadFamily`. -/
noncomputable def firstBadTrace
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    Trace (F := F.get ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad,
      (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩) t :=
  traceOfBadCNF (hbad := (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).2)

/-- Из `BadFamily` извлекаем индекс формулы и трассу длины `t`. -/
lemma badFamily_trace
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    ∃ j, ∃ hj : j < F.length,
      Nonempty (Trace (F := F.get ⟨j, hj⟩) t) := by
  refine ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad, ?_, ?_⟩
  · exact (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).1
  · exact ⟨firstBadTrace (F := F) (t := t) (ρ := ρ) hbad⟩

/-!
## Good-событие для семейства формул

`GoodFamily` фиксирует, что **ни одна** формула из списка не имеет
канонической трассы длины `t`. Это естественное отрицание `BadFamily`.
Такое определение удобно для дальнейшей детерминизации:

* `BadFamily` — существует плохая формула;
* `GoodFamily` — все формулы «хорошие».
-/

def GoodFamily (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∀ i (hi : i < F.length), ¬ BadCNF (F := F.get ⟨i, hi⟩) t ρ

lemma goodFamily_iff_not_badFamily
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n} :
    GoodFamily (F := F) t ρ ↔ ¬ BadFamily (F := F) t ρ := by
  classical
  constructor
  · intro hgood hbad
    rcases hbad with ⟨i, hi, hbad_i⟩
    exact (hgood i hi) hbad_i
  · intro hnot i hi hbad_i
    exact hnot ⟨i, hi, hbad_i⟩

end MultiSwitching
end AC0
end Pnp3
