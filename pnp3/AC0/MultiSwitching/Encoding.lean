import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.CanonicalTrace
import AC0.MultiSwitching.CanonicalDT
import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.TraceBridge

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
## Fintype/кардинальности для `Vector` (array-based)

В Lean 4 `Vector` реализован через `Array`, а в Mathlib уже есть
кардинальность для `List.Vector`. Чтобы получать явные формулы,
строим эквивалентность между ними и унаследуем `Fintype`.
-/

def vectorEquivListVector (α : Type) (n : Nat) :
    Vector α n ≃ List.Vector α n :=
  { toFun := fun v =>
      ⟨v.toList, by
        calc
          v.toList.length = v.toArray.size := by simp [Vector.toList]
          _ = n := v.size_toArray⟩
    invFun := fun v =>
      ⟨v.1.toArray, by
        simpa [List.size_toArray] using v.2⟩
    left_inv := by
      intro v
      cases v with
      | mk arr h =>
          apply (Vector.toArray_inj).1
          simp [Vector.toList]
    right_inv := by
      intro v
      cases v with
      | mk l hl =>
          apply Subtype.ext
          simp [Vector.toList] }

instance instFintypeVector (α : Type) (n : Nat) [Fintype α] :
    Fintype (Vector α n) :=
  Fintype.ofEquiv (List.Vector α n) (vectorEquivListVector α n).symm

lemma card_Vector (α : Type) (n : Nat) [Fintype α] :
    Fintype.card (Vector α n) = Fintype.card α ^ n := by
  classical
  simpa using
    (Fintype.card_congr (vectorEquivListVector α n)).trans (card_vector (α := α) n)

/-!
## Простая CNF-инъекция через каноническую трассу (depth‑2)

Этот блок закрывает **следующий пункт** плана: encoding/decode и инъективность
для depth‑2 CNF. Мы используем уже существующую структуру `CanonicalTrace` и
штрих‑код `SelectionTrace.Barcode`, но храним в коде только пары `(индекс,бит)`
(этого достаточно, чтобы восстановить исходное ограничение через `unassign`).

Важно: этот шаг — минимальная, детерминированная инъекция,
которая нужна для proof‑by‑encoding. Дополнительные поля (позиции литералов,
индекс клаузы) можно добавить позже для более тонких подсчётов.
-/

/-!
## AuxBound: канонический код размера `B^t`

Этот тип соответствует пункту плана (Phase 2.2):
фиксируем абстрактный размер кода `B`, и получаем кардинал `B^t`.
Далее его можно инстанцировать «жирным» `B`, например
`B = 2 * n * (m+1) * (k+1) * (|F|+1)`.
-/

abbrev AuxBound (B t : Nat) : Type :=
  Vector (Fin B) t

lemma card_AuxBound (B t : Nat) :
    Fintype.card (AuxBound B t) = B ^ t := by
  classical
  simp [AuxBound, card_Vector, Fintype.card_fin]

def auxBoundCodes (B t : Nat) [Fintype (AuxBound B t)] : Finset (AuxBound B t) :=
  Finset.univ

@[simp] lemma auxBoundCodes_card (B t : Nat) [Fintype (AuxBound B t)] :
    (auxBoundCodes B t).card = Fintype.card (AuxBound B t) := by
  simp [auxBoundCodes]

/-!
### AuxSimple: минимальный код пути

`AuxSimple n t` хранит ровно `t` пар `(индекс, значение)`,
то есть функцию `Fin t → BitFix n`.
-/

abbrev AuxSimple (n t : Nat) : Type :=
  Fin t → BitFix n

/-!
### Вспомогательная «жирная» кодировка трассы

Чтобы получить классическую оценку вида `B^t`, полезно иметь отдельный
тип кодов для «шагов трассы». Мы сознательно берём **очень грубую**
схему кодирования:

* `var` — индекс переменной (`Fin n`);
* `value` — значение ветви (`Bool`);
* `clauseIndex` и `literalIndex` кодируются через `Fin.ofNat`,
  то есть берутся по модулю выбранной верхней границы.

Это не нужно для восстановления рестрикции (этим занимается `AuxSimple`),
но позволяет получить явную оценку на число кодов.
-/

/-- Верхняя граница на число клауз в семействе CNF (грубая). -/
def maxClauses {n w : Nat} (F : FormulaFamily n w) : Nat :=
  F.foldl (fun m G => Nat.max m G.clauses.length) 0

/-!
### Технические леммы про `foldl` с `Nat.max`

`maxClauses` выражается через `List.foldl` с операцией `Nat.max`. Чтобы
не таскать эти рассуждения по всему файлу, фиксируем два небольших факта:

* стартовый параметр `m` не больше результата foldl;
* foldl монотонен по стартовому параметру `m`.
-/

lemma le_foldl_max
    {n w : Nat} (rest : List (CNF n w)) (m : Nat) :
    m ≤ rest.foldl (fun m G => Nat.max m G.clauses.length) m := by
  induction rest generalizing m with
  | nil =>
      simp
  | cons G rest ih =>
      have h1 : m ≤ Nat.max m G.clauses.length := Nat.le_max_left _ _
      have h2 :
          Nat.max m G.clauses.length
            ≤ rest.foldl (fun m G => Nat.max m G.clauses.length)
                (Nat.max m G.clauses.length) := by
        simpa using ih (m := Nat.max m G.clauses.length)
      exact Nat.le_trans h1 h2

lemma foldl_max_le_foldl_max
    {n w : Nat} (rest : List (CNF n w)) {m m' : Nat} (h : m ≤ m') :
    rest.foldl (fun m G => Nat.max m G.clauses.length) m
      ≤ rest.foldl (fun m G => Nat.max m G.clauses.length) m' := by
  induction rest generalizing m m' with
  | nil =>
      simpa using h
  | cons G rest ih =>
      have h' :
          Nat.max m G.clauses.length ≤ Nat.max m' G.clauses.length := by
        exact max_le_max h (le_rfl)
      simpa [List.foldl] using ih h'

lemma clauses_length_le_maxClauses
    {n w : Nat} {F : FormulaFamily n w} {G : CNF n w}
    (hG : G ∈ F) : G.clauses.length ≤ maxClauses F := by
  induction F with
  | nil =>
      cases hG
  | cons G0 rest ih =>
      have hG' : G = G0 ∨ G ∈ rest := by
        simpa using hG
      cases hG' with
      | inl h =>
          subst h
          -- В начале foldl стоит `max 0 G'.clauses.length`, т.е. просто длина.
          have hle := le_foldl_max (rest := rest) (m := G.clauses.length)
          simpa [maxClauses] using hle
      | inr h =>
          have hrest := ih h
          -- Монотонность foldl по стартовому значению.
          have hmono :
              maxClauses rest ≤ maxClauses (G0 :: rest) := by
            have hfold :=
              foldl_max_le_foldl_max (rest := rest)
                (m := 0) (m' := G0.clauses.length) (by exact Nat.zero_le _)
            simpa [maxClauses] using hfold
          exact Nat.le_trans hrest hmono

/-!
Код одного шага трассы: `Fin n × Bool × Fin (m+1) × Fin (w+1)`.
Здесь `m` — грубая верхняя граница на число клауз.
-/

abbrev TraceStepCode (n w m : Nat) : Type :=
  Fin n × Bool × Fin (m + 1) × Fin (w + 1)

abbrev TraceCode (n w m t : Nat) : Type :=
  Vector (TraceStepCode n w m) t

lemma card_TraceCode (n w m t : Nat) :
    Fintype.card (TraceCode n w m t) =
      (2 * n * (m + 1) * (w + 1)) ^ t := by
  classical
  simp [TraceCode, TraceStepCode, card_Vector, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_bool, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm]

noncomputable def traceStepCode
    {n w : Nat} {F : CNF n w} (m : Nat) (step : TraceStep F) :
    TraceStepCode n w m :=
  (step.var,
    step.value,
    Fin.ofNat (m + 1) step.clauseIndex,
    Fin.ofNat (w + 1) step.literalIndex)

noncomputable def traceCodeOfTrace
    {n w t : Nat} {F : CNF n w} (m : Nat) (trace : Trace F t) :
    TraceCode n w m t :=
  trace.map (traceStepCode (F := F) m)

/-!
### Вспомогательное извлечение `BitFix` из «широкого» кода

Для декодирования достаточно пары `(индекс, значение)`. Мы извлекаем её
из `TraceStepCode`, игнорируя `clauseIndex` и `literalIndex`.
-/

noncomputable def bitFixOfTraceStepCode
    {n w m : Nat} (step : TraceStepCode n w m) : BitFix n :=
  (step.1, step.2.1)

noncomputable def auxSimpleOfTraceCode
    {n w m t : Nat} (code : TraceCode n w m t) : AuxSimple n t :=
  fun i => bitFixOfTraceStepCode (code.get i)

/-!
Код для семейства: добавляем индекс формулы (грубый `Fin (|F|+1)`),
и саму трассу. Такой код достаточно компактный и используется и в
подсчётах, и в инъективном декодировании.
-/

abbrev AuxStepSmall (w : Nat) : Type :=
  Bool × Fin (w + 1)

abbrev AuxTraceSmall (w t : Nat) : Type :=
  Vector (AuxStepSmall w) t

lemma card_AuxTraceSmall (w t : Nat) :
    Fintype.card (AuxTraceSmall w t) = (2 * (w + 1)) ^ t := by
  classical
  simp [AuxTraceSmall, AuxStepSmall, card_Vector, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

abbrev FamilyTraceCodeSmall {n w : Nat} (F : FormulaFamily n w) (t : Nat) : Type :=
  Fin (F.length + 1) × AuxTraceSmall w t

abbrev AuxTraceFamilySmall {n w : Nat} (F : FormulaFamily n w) (t : Nat) : Type :=
  FamilyTraceCodeSmall F t

lemma card_AuxTraceFamilySmall {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    Fintype.card (AuxTraceFamilySmall (F := F) t) =
      (F.length + 1) * (2 * (w + 1)) ^ t := by
  classical
  simp [AuxTraceFamilySmall, FamilyTraceCodeSmall, AuxTraceSmall, AuxStepSmall,
    Fintype.card_prod, card_Vector, Fintype.card_fin, Fintype.card_bool,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, card_AuxTraceSmall]

def auxTraceFamilySmallCodes {n w : Nat} (F : FormulaFamily n w) (t : Nat)
    [Fintype (AuxTraceFamilySmall (F := F) t)] :
    Finset (AuxTraceFamilySmall (F := F) t) :=
  Finset.univ

@[simp] lemma auxTraceFamilySmallCodes_card {n w : Nat}
    (F : FormulaFamily n w) (t : Nat)
    [Fintype (AuxTraceFamilySmall (F := F) t)] :
    (auxTraceFamilySmallCodes (F := F) t).card =
      Fintype.card (AuxTraceFamilySmall (F := F) t) := by
  simp [auxTraceFamilySmallCodes]

/-!
### «Широкий» код для семейства

Добавляем в шаги трассы переменную и индекс клаузы, чтобы сделать
декодирование однозначным. База становится больше, но инъекция
становится прямой.
-/

abbrev FamilyTraceCodeWide {n w : Nat} (F : FormulaFamily n w) (t : Nat) : Type :=
  Fin (F.length + 1) × TraceCode n w (maxClauses F) t

lemma card_FamilyTraceCodeWide {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    Fintype.card (FamilyTraceCodeWide (F := F) t) =
      (F.length + 1) * (2 * n * (maxClauses F + 1) * (w + 1)) ^ t := by
  classical
  have hcard_trace :
      Fintype.card (TraceCode n w (maxClauses F) t) =
        (2 * n * (maxClauses F + 1) * (w + 1)) ^ t := by
    simpa [TraceCode, TraceStepCode, card_Vector, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using
      (card_TraceCode (n := n) (w := w) (m := maxClauses F) (t := t))
  calc
    Fintype.card (FamilyTraceCodeWide (F := F) t)
        = (F.length + 1) * Fintype.card (TraceCode n w (maxClauses F) t) := by
            simp [FamilyTraceCodeWide, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ = (F.length + 1) * (2 * n * (maxClauses F + 1) * (w + 1)) ^ t := by
          simp [hcard_trace]

def familyTraceCodeWideCodes {n w : Nat} (F : FormulaFamily n w) (t : Nat)
    [Fintype (FamilyTraceCodeWide (F := F) t)] :
    Finset (FamilyTraceCodeWide (F := F) t) :=
  Finset.univ

@[simp] lemma familyTraceCodeWideCodes_card {n w : Nat}
    (F : FormulaFamily n w) (t : Nat)
    [Fintype (FamilyTraceCodeWide (F := F) t)] :
    (familyTraceCodeWideCodes (F := F) t).card =
      Fintype.card (FamilyTraceCodeWide (F := F) t) := by
  simp [familyTraceCodeWideCodes]

lemma card_AuxSimple (n t : Nat) :
    Fintype.card (AuxSimple n t) = (2 * n) ^ t := by
  classical
  -- `BitFix n = Fin n × Bool`, поэтому кардинал одного шага = 2 * n.
  simp [AuxSimple, BitFix, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

def auxSimpleCodes (n t : Nat) [Fintype (AuxSimple n t)] : Finset (AuxSimple n t) :=
  Finset.univ

@[simp] lemma auxSimpleCodes_card (n t : Nat) [Fintype (AuxSimple n t)] :
    (auxSimpleCodes n t).card = Fintype.card (AuxSimple n t) := by
  simp [auxSimpleCodes]

def auxTraceSmallCodes (w t : Nat) [Fintype (AuxTraceSmall w t)] :
    Finset (AuxTraceSmall w t) := by
  exact Finset.univ

@[simp] lemma auxTraceSmallCodes_card (w t : Nat) [Fintype (AuxTraceSmall w t)] :
    (auxTraceSmallCodes w t).card = Fintype.card (AuxTraceSmall w t) := by
  simp [auxTraceSmallCodes]

/-!
### «Расширенный» код шага: `AuxSimple × AuxTraceSmall`

Чтобы обеспечить инъективность, мы храним **полный** список присвоений
(переменная + значение) и дополнительно — позиции выбранных литералов.
Это увеличивает базу, но делает декодирование однозначным.
-/

abbrev AuxTraceVar (n w t : Nat) : Type :=
  AuxSimple n t × AuxTraceSmall w t

lemma card_AuxTraceVar (n w t : Nat) :
    Fintype.card (AuxTraceVar n w t) =
      (2 * n) ^ t * (2 * (w + 1)) ^ t := by
  classical
  simp [AuxTraceVar, card_AuxTraceSmall, card_AuxSimple, Fintype.card_prod,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

abbrev FamilyTraceCodeVar {n w : Nat} (F : FormulaFamily n w) (t : Nat) : Type :=
  Fin (F.length + 1) × AuxTraceVar n w t

lemma card_FamilyTraceCodeVar {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    Fintype.card (FamilyTraceCodeVar (F := F) t) =
      (F.length + 1) * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
  classical
  simp [FamilyTraceCodeVar, AuxTraceVar, card_AuxTraceVar, Fintype.card_prod,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

def familyTraceCodeVarCodes {n w : Nat} (F : FormulaFamily n w) (t : Nat)
    [Fintype (FamilyTraceCodeVar (F := F) t)] :
    Finset (FamilyTraceCodeVar (F := F) t) :=
  Finset.univ

@[simp] lemma familyTraceCodeVarCodes_card {n w : Nat}
    (F : FormulaFamily n w) (t : Nat)
    [Fintype (FamilyTraceCodeVar (F := F) t)] :
    (familyTraceCodeVarCodes (F := F) t).card =
      Fintype.card (FamilyTraceCodeVar (F := F) t) := by
  simp [familyTraceCodeVarCodes]

/-!
### Кодирование CanonicalTrace → AuxSimple

Мы извлекаем список `(индекс, значение)` из штрих‑кода и трактуем его
как `Fin t → BitFix n` через `List.get`.
-/

noncomputable def auxSimpleOfTrace
    {n w t : Nat} {F : CNF n w} {ρ : Restriction n}
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    AuxSimple n t := by
  classical
  -- Используем `barcode.assignedFixes` длины `t`.
  let code := Core.CNF.CanonicalTrace.barcode (trace := trace)
  -- Приводим индекс `i : Fin t` к `Fin code.assignedFixes.length`.
  have hlen :
      code.assignedFixes.length = t := by
    simpa using
      (Core.CNF.CanonicalTrace.barcode_assignedFixes_length (trace := trace))
  refine fun i => code.assignedFixes.get (Fin.cast hlen.symm i)

/-!
### Кодирование CanonicalTrace → AuxTraceSmall

Для «малого» алфавита нам нужны только два поля:

* направление ветви (бит),
* позиция выбранного свободного литерала (индекс в `w.free`).

Это даёт размер алфавита `2*(w+1)` и убирает `n` из степени.
-/

noncomputable def auxTraceSmallOfTrace
    {n w t : Nat} {F : CNF n w} {ρ : Restriction n}
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    AuxTraceSmall w t :=
  (CanonicalTrace.toTrace trace).map
    (fun step => (step.value, Fin.ofNat (w + 1) step.literalIndex))

/-!
### Декодирование: восстановление ограничения

Декодируем, просто «раз‑фиксируя» все координаты из Aux‑кода.
-/

noncomputable def decodeAuxSimple
    {n t : Nat} (ρ' : Restriction n) (aux : AuxSimple n t) :
    Restriction n :=
  Core.SelectionTrace.reconstructRestriction (ρ := ρ') (List.ofFn aux)

lemma decodeAuxSimple_ofTrace
    {n w t : Nat} {F : CNF n w} {ρ : Restriction n}
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    decodeAuxSimple (ρ' := Core.CNF.CanonicalTrace.finalRestriction trace)
      (aux := auxSimpleOfTrace (trace := trace)) = ρ := by
  classical
  have hfinal :
      Core.SelectionTrace.finalRestriction
          (Core.CNF.CanonicalTrace.toSelectionTrace (trace := trace))
        = Core.CNF.CanonicalTrace.finalRestriction trace := by
    induction trace with
    | nil =>
        simp [Core.CNF.CanonicalTrace.finalRestriction,
          Core.CNF.CanonicalTrace.toSelectionTrace,
          Core.SelectionTrace.finalRestriction]
    | cons _ _ tail ih =>
        simp [Core.CNF.CanonicalTrace.finalRestriction,
          Core.CNF.CanonicalTrace.toSelectionTrace,
          Core.SelectionTrace.finalRestriction, ih]
  -- Переписываем `List.ofFn` через список фиксаций из штрих‑кода.
  have hlist :
      List.ofFn (auxSimpleOfTrace (trace := trace)) =
        (Core.CNF.CanonicalTrace.barcode (trace := trace)).assignedFixes := by
    -- `List.ofFn` от `List.get` возвращает исходный список.
    -- Здесь используется каст индекса, поэтому применяем `List.ofFn_congr`.
    set code := Core.CNF.CanonicalTrace.barcode (trace := trace)
    have hlen : code.assignedFixes.length = t := by
      simpa using
        (Core.CNF.CanonicalTrace.barcode_assignedFixes_length (trace := trace))
    have hcongr :
        List.ofFn
            (fun i : Fin t =>
              code.assignedFixes.get (Fin.cast hlen.symm i))
          =
        List.ofFn
            (fun i : Fin code.assignedFixes.length =>
              code.assignedFixes.get i) := by
      simpa using
        (List.ofFn_congr (h := hlen)
          (f := fun i : Fin code.assignedFixes.length => code.assignedFixes.get i)).symm
    calc
      List.ofFn (auxSimpleOfTrace (trace := trace))
          =
          List.ofFn
            (fun i : Fin t =>
              code.assignedFixes.get (Fin.cast hlen.symm i)) := by
            simp [auxSimpleOfTrace, code, hlen]
      _ = List.ofFn
            (fun i : Fin code.assignedFixes.length =>
              code.assignedFixes.get i) := hcongr
      _ = code.assignedFixes := by
            simpa using
              (List.ofFn_get (l := code.assignedFixes))
  -- Дальше используем тот факт, что `decode` штрих‑кода восстанавливает `ρ`.
  have hdecode :
      Core.SelectionTrace.decode
          (Core.CNF.CanonicalTrace.barcode (trace := trace)) = ρ := by
    simpa using (Core.CNF.CanonicalTrace.decode_barcode (trace := trace))
  -- `SelectionTrace.decode` — это `reconstructRestriction` от `assignedFixes`.
  simpa [decodeAuxSimple, hlist, hfinal] using hdecode

/-!
### Инъективное encoding для BadCNF

Для каждой «плохой» рестрикции строим код:

* `ρ'` — финальное ограничение после трассы длины `t`;
* `aux` — список зафиксированных пар `(индекс, значение)`.
-/

def BadInRsCNF {n w : Nat} (F : CNF n w) (s t : Nat) : Type :=
  {ρ : Restriction n // ρ ∈ R_s (n := n) s ∧ BadCNF (F := F) t ρ}

/-!
### Семейство CNF: bad‑ограничения для списка формул

Мы выбираем **первую** плохую формулу (по индексу) и используем её
каноническую трассу для кодирования. Это даёт детерминированный encoding.
-/

def BadFamilyInRsCNF {n w : Nat} (F : FormulaFamily n w) (s t : Nat) : Type :=
  {ρ : Restriction n // ρ ∈ R_s (n := n) s ∧ BadFamily (F := F) t ρ}

/-!
### Детерминированная версия для семейства CNF

Мы используем `BadFamily_deterministic` из `TraceBridge` и строим
кодирование через «малый» алфавит `AuxTraceSmall`. Это подготовительная
часть для Step 3.2: алфавит имеет размер `2*(w+1)`, что соответствует
параметру `BParam`.
-/

def BadFamilyDetInRsCNF {n w : Nat} (F : FormulaFamily n w) (s t : Nat) : Type :=
  {ρ : Restriction n // ρ ∈ R_s (n := n) s ∧ BadFamily_deterministic (F := F) t ρ}

noncomputable def canonicalTraceOfBadFamily
    {n w t : Nat} {F : FormulaFamily n w} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    Core.CNF.CanonicalTrace
      (F := F.get
        ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad,
          (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩) ρ t :=
  Classical.choice (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).2

noncomputable def familyTraceCodeSmallOfBad
    {n w t : Nat} {F : FormulaFamily n w} {ρ : Restriction n}
    (hbad : BadFamily (F := F) t ρ) :
    FamilyTraceCodeSmall (F := F) t := by
  classical
  -- Канонический индекс формулы.
  let j := firstBadIndex (F := F) (t := t) (ρ := ρ) hbad
  -- Каноническая трасса и её «минимальный» код.
  let trace := canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad
  let code : AuxTraceSmall w t := auxTraceSmallOfTrace (trace := trace)
  exact ⟨Fin.ofNat (F.length + 1) j, code⟩

noncomputable def familyTraceCodeSmallOfBadDet
    {n w t : Nat} {F : FormulaFamily n w} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) :
    FamilyTraceCodeSmall (F := F) t := by
  classical
  -- Канонический индекс плохой формулы.
  let j := firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad
  -- Детерминированная трасса и её «малый» код.
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  let code : AuxTraceSmall w t := auxTraceSmallOfTrace (trace := trace)
  exact ⟨Fin.ofNat (F.length + 1) j, code⟩

def auxFamilySimpleCodes
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    Finset (Fin (F.length + 1) × AuxSimple n t) := by
  classical
  exact (Finset.univ).product (auxSimpleCodes n t)

@[simp] lemma auxFamilySimpleCodes_card
    {n w t : Nat} (F : FormulaFamily n w) :
    (auxFamilySimpleCodes (F := F) t).card =
      (F.length + 1) * (2 * n) ^ t := by
  classical
  have hcard_fun :
      Fintype.card (Fin t → Fin n × Bool) = (n * 2) ^ t := by
    have hcard_fun_base :
        Fintype.card (Fin t → Fin n × Bool) =
          (Fintype.card (Fin n × Bool)) ^ (Fintype.card (Fin t)) :=
      Fintype.card_fun (α := Fin t) (β := Fin n × Bool)
    simpa [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hcard_fun_base
  calc
    (auxFamilySimpleCodes (F := F) t).card
        = (F.length + 1) * Fintype.card (Fin t → Fin n × Bool) := by
            simp [auxFamilySimpleCodes, auxSimpleCodes_card, AuxSimple, BitFix,
              Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ = (F.length + 1) * (n * 2) ^ t := by
          simp [hcard_fun]
    _ = (F.length + 1) * (2 * n) ^ t := by
          simp [Nat.mul_comm]

noncomputable def encodeBadFamilyCNF
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxFamilySimpleCodes (F := F) t)} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let aux := auxSimpleOfTrace (trace := trace)
  let code :=
    (Fin.ofNat (F.length + 1)
      (firstBadIndex (F := F) (t := t) (ρ := ρ) hbad), aux)
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad,
            (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩)
        (ρ := ρ) (s := s) (t := t) hρs trace)
  refine ⟨⟨ρ', code⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxFamilySimpleCodes, auxSimpleCodes]⟩

/-!
### Encoding для детерминированного BadFamily (тот же «толстый» алфавит)

Эта версия полностью аналогична `encodeBadFamilyCNF`, но опирается на
детерминированный предикат.  Она полезна для постепенного перехода
к малому алфавиту: сейчас мы сохраняем инъекцию через `AuxSimple`,
а затем заменим её на `AuxTraceSmall`.
-/

noncomputable def encodeBadFamilyDetCNF
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyDetInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxFamilySimpleCodes (F := F) t)} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let aux := auxSimpleOfTrace (trace := trace)
  let code := (Fin.ofNat (F.length + 1)
    (firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad), aux)
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    have hbad' :
        BadFamily (F := F) t ρ := badFamily_deterministic_implies_badFamily
          (F := F) (t := t) (ρ := ρ) hbad
    have htrace :
        Core.CNF.CanonicalTrace
          (F := F.get
            ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
              (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩) ρ t :=
      canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad'
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
            (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩)
        (ρ := ρ) (s := s) (t := t) hρs htrace)
  refine ⟨⟨ρ', code⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxFamilySimpleCodes, auxSimpleCodes]⟩

noncomputable def decodeBadFamilyDetCNF
    {n w t : Nat} (F : FormulaFamily n w) :
    (Restriction n × (Fin (F.length + 1) × AuxSimple n t)) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := aux.2)

lemma decode_encodeBadFamilyDetCNF
    {n w t s : Nat} (F : FormulaFamily n w)
    (ρbad : BadFamilyDetInRsCNF (F := F) s t) :
    decodeBadFamilyDetCNF (F := F)
        (encodeBadFamilyDetCNF (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  have hdecode := decodeAuxSimple_ofTrace (trace := trace)
  simpa [encodeBadFamilyDetCNF, decodeBadFamilyDetCNF, trace] using hdecode

lemma encodeBadFamilyDetCNF_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadFamilyDetCNF (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx := decode_encodeBadFamilyDetCNF (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadFamilyDetCNF (F := F) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyDetCNF (F := F) (t := t)
          (encodeBadFamilyDetCNF (F := F) (s := s) (t := t) x).1
        =
      decodeBadFamilyDetCNF (F := F) (t := t)
          (encodeBadFamilyDetCNF (F := F) (s := s) (t := t) y).1 := by
    simpa [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

/-!
### Encoding для детерминированного BadFamily (малый алфавит)

Здесь мы используем `FamilyTraceCodeSmall` и тем самым устраняем
экспоненту по `n`. Эта версия нужна для финального шага 3.2.
-/

noncomputable def encodeBadFamilyDetCNF_small
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyDetInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxTraceFamilySmallCodes (F := F) t)} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let code := familyTraceCodeSmallOfBadDet (F := F) (t := t) (ρ := ρ) hbad
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    -- Используем стандартную лемму о финальной рестрикции трассы.
    have hbad' :
        BadFamily (F := F) t ρ := badFamily_deterministic_implies_badFamily
          (F := F) (t := t) (ρ := ρ) hbad
    have htrace :
        Core.CNF.CanonicalTrace
          (F := F.get
            ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
              (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩) ρ t :=
      canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad'
    -- Из `htrace` получаем принадлежность.
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
            (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩)
        (ρ := ρ) (s := s) (t := t) hρs htrace)
  refine ⟨⟨ρ', code⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxTraceFamilySmallCodes]⟩

/-!
### Encoding для детерминированного BadFamily (расширенный код)

Мы храним полный `AuxSimple` (переменная + значение) и дополнительно
`AuxTraceSmall` (позиции литералов). Это гарантирует инъективность.
-/

noncomputable def encodeBadFamilyDetCNF_var
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyDetInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (familyTraceCodeVarCodes (F := F) t)} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let aux := auxSimpleOfTrace (trace := trace)
  let auxSmall := auxTraceSmallOfTrace (trace := trace)
  let code : FamilyTraceCodeVar (F := F) t :=
    ⟨Fin.ofNat (F.length + 1)
        (firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad),
      (aux, auxSmall)⟩
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    have hbad' :
        BadFamily (F := F) t ρ := badFamily_deterministic_implies_badFamily
          (F := F) (t := t) (ρ := ρ) hbad
    have htrace :
        Core.CNF.CanonicalTrace
          (F := F.get
            ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
              (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩) ρ t :=
      canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad'
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndex (F := F) (t := t) (ρ := ρ) hbad',
            (firstBadIndex_spec (F := F) (t := t) (ρ := ρ) hbad').1⟩)
        (ρ := ρ) (s := s) (t := t) hρs htrace)
  refine ⟨⟨ρ', code⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [familyTraceCodeVarCodes]⟩

noncomputable def decodeBadFamilyDetCNF_var
    {n w t : Nat} (F : FormulaFamily n w) :
    (Restriction n × FamilyTraceCodeVar (F := F) t) → Restriction n
  | ⟨ρ', code⟩ => decodeAuxSimple (ρ' := ρ') (aux := code.2.1)

lemma decode_encodeBadFamilyDetCNF_var
    {n w t s : Nat} (F : FormulaFamily n w)
    (ρbad : BadFamilyDetInRsCNF (F := F) s t) :
    decodeBadFamilyDetCNF_var (F := F)
        (encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  have hdecode := decodeAuxSimple_ofTrace (trace := trace)
  simpa [encodeBadFamilyDetCNF_var, decodeBadFamilyDetCNF_var, trace] using hdecode

lemma encodeBadFamilyDetCNF_var_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx := decode_encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyDetCNF_var (F := F) (t := t)
          (encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) x).1
        =
      decodeBadFamilyDetCNF_var (F := F) (t := t)
          (encodeBadFamilyDetCNF_var (F := F) (s := s) (t := t) y).1 := by
    simpa [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

noncomputable def decodeBadFamilyCNF
    {n w t : Nat} (F : FormulaFamily n w) :
    (Restriction n × (Fin (F.length + 1) × AuxSimple n t)) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := aux.2)

lemma decode_encodeBadFamilyCNF
    {n w t s : Nat} (F : FormulaFamily n w)
    (ρbad : BadFamilyInRsCNF (F := F) s t) :
    decodeBadFamilyCNF (F := F)
        (encodeBadFamilyCNF (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := canonicalTraceOfBadFamily (F := F) (t := t) (ρ := ρ) hbad
  have hdecode := decodeAuxSimple_ofTrace (trace := trace)
  simpa [encodeBadFamilyCNF, decodeBadFamilyCNF, trace] using hdecode

lemma encodeBadFamilyCNF_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadFamilyCNF (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx := decode_encodeBadFamilyCNF (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadFamilyCNF (F := F) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyCNF (F := F) (t := t)
          (encodeBadFamilyCNF (F := F) (s := s) (t := t) x).1
        =
      decodeBadFamilyCNF (F := F) (t := t)
          (encodeBadFamilyCNF (F := F) (s := s) (t := t) y).1 := by
    simpa [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this


noncomputable def encodeBadCNF
    {n w t s : Nat} (F : CNF n w) :
    BadInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product (auxSimpleCodes n t)} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  -- Берём любую каноническую трассу длины `t`.
  let trace : Core.CNF.CanonicalTrace (F := F) ρ t := Classical.choice hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let aux := auxSimpleOfTrace (trace := trace)
  -- Показываем, что `ρ'` лежит в `R_{s-t}`.
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    -- Используем лемму из `CanonicalTrace` (через файл `CanonicalTrace.lean`).
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F) (ρ := ρ) (s := s) (t := t) hρs trace)
  refine ⟨⟨ρ', aux⟩, ?_⟩
  -- Принадлежность продукту — просто `hρ'` и `aux ∈ univ`.
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxSimpleCodes]⟩

noncomputable def decodeBadCNF
    {n w t : Nat} (F : CNF n w) :
    (Restriction n × AuxSimple n t) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := aux)

lemma decode_encodeBadCNF
    {n w t s : Nat} (F : CNF n w)
    (ρbad : BadInRsCNF (F := F) s t) :
    decodeBadCNF (F := F) (encodeBadCNF (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  -- Переписываем код через выбранную трассу.
  let trace : Core.CNF.CanonicalTrace (F := F) ρ t := Classical.choice hbad
  have hdecode :=
    decodeAuxSimple_ofTrace (trace := trace)
  -- Разворачиваем `encodeBadCNF`/`decodeBadCNF`.
  simpa [encodeBadCNF, decodeBadCNF, trace] using hdecode

lemma encodeBadCNF_injective
    {n w t s : Nat} (F : CNF n w) :
    Function.Injective (encodeBadCNF (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  -- Декодируем и восстанавливаем исходные рестрикции.
  have hx := decode_encodeBadCNF (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadCNF (F := F) (s := s) (t := t) y
  -- Из равенства кодов получаем равенство ограничений.
  have hρ :
      (decodeBadCNF (F := F) (t := t) (encodeBadCNF (F := F) (s := s) (t := t) x).1)
        =
      (decodeBadCNF (F := F) (t := t) (encodeBadCNF (F := F) (s := s) (t := t) y).1) := by
    simpa [hxy]
  -- Согласуем через `hx`/`hy`.
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

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
### Специализация для `AuxBound`

Это удобная форма для «жирного» кода размера `B^t`.
-/

lemma badRestrictions_card_le_of_auxBound_encoding
    (A : CCDTAlgorithm n k ℓ t F) (s t' B : Nat)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product (auxBoundCodes B t))) :
    (badRestrictions (n := n) s (BadEvent (A := A))).card
      ≤ (R_s (n := n) t').card * B ^ t := by
  classical
  have h :=
    badRestrictions_card_le_of_encoding_product
      (A := A) (s := s) (t' := t') (codes := auxBoundCodes B t) witness
  -- Разворачиваем кардинал `AuxBound`.
  simpa [auxBoundCodes_card, card_AuxBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

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

end MultiSwitching
end AC0
end Pnp3
