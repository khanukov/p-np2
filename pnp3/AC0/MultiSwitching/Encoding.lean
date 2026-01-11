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
    Fintype.card_bool, Fintype.card_fin, Nat.mul_comm]

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
    Nat.mul_comm]

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
            simp [FamilyTraceCodeWide, Fintype.card_prod]
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
  simp [AuxSimple, BitFix, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, Nat.mul_comm]

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
  simp [AuxTraceVar, card_AuxTraceSmall, Fintype.card_prod,
    Nat.mul_comm]

abbrev FamilyTraceCodeVar {n w : Nat} (F : FormulaFamily n w) (t : Nat) : Type :=
  Fin (F.length + 1) × AuxTraceVar n w t

lemma card_FamilyTraceCodeVar {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    Fintype.card (FamilyTraceCodeVar (F := F) t) =
      (F.length + 1) * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
  classical
  -- Карта произведения: `Fin (len+1)` × `AuxTraceVar`.
  -- Затем раскрываем `card_AuxTraceVar` и переставляем множители.
  calc
    Fintype.card (FamilyTraceCodeVar (F := F) t)
        = Fintype.card (Fin (F.length + 1))
            * Fintype.card (AuxTraceVar n w t) := by
            simp [FamilyTraceCodeVar, Fintype.card_prod]
    _ = (F.length + 1) * ((2 * n) ^ t * (2 * (w + 1)) ^ t) := by
          -- Явно раскрываем `card_AuxTraceVar`, чтобы не зависеть от `simp`.
          rw [card_AuxTraceVar]
          simp
    _ = (F.length + 1) * (2 * n) ^ t * (2 * (w + 1)) ^ t := by
          ac_rfl

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

abbrev Aux (n t k m : Nat) : Type :=
  Fin t → (BitFix n × Fin k × Fin m)

lemma card_Aux (n t k m : Nat) :
    Fintype.card (Aux n t k m) = (2 * n * k * m) ^ t := by
  classical
  -- `Fintype.card_fun` даёт степень кардинала кодом для одного шага.
  -- Кардинал одного шага = (2 * n) * k * m.
  simp [Aux, BitFix, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

lemma card_Aux_le (n t k m : Nat) :
    Fintype.card (Aux n t k m) ≤ (2 * n * k * m) ^ t := by
  simp [card_Aux, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Универсальное множество кодов `Aux` как `Finset.univ`. -/
def auxCodes (n t k m : Nat) [Fintype (Aux n t k m)] : Finset (Aux n t k m) :=
  Finset.univ

@[simp] lemma auxCodes_card (n t k m : Nat) [Fintype (Aux n t k m)] :
    (auxCodes n t k m).card = Fintype.card (Aux n t k m) := by
  simp [auxCodes]

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
            simp [auxSimpleOfTrace, code]
      _ = List.ofFn
            (fun i : Fin code.assignedFixes.length =>
              code.assignedFixes.get i) := hcongr
      _ = code.assignedFixes := by
            simp
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
              Nat.mul_comm]
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
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
            (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩)
        (ρ := ρ) (s := s) (t := t) hρs trace)
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
    simp [hxy]
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
    -- Из `trace` получаем принадлежность.
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
            (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩)
        (ρ := ρ) (s := s) (t := t) hρs trace)
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
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
            (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩)
        (ρ := ρ) (s := s) (t := t) hρs trace)
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
    simp [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

/-!
### Encoding для детерминированного BadFamily через "полный" Aux

Мы строим код длины `t`, где на каждом шаге храним:

* `BitFix n` — какая переменная фиксируется и какое значение выбирается;
* `Fin (w+1)` — позиция выбранного литерала в списке свободных литералов;
* `Fin (F.length+1)` — индекс формулы (один и тот же для всех шагов).

Этот формат соответствует условию из блока Stage‑1: код явно хранит
все ветвления и позволяет восстановить исходную рестрикцию через
`reconstructRestriction`, игнорируя дополнительные поля.
-/

noncomputable def auxOfTraceStep
    {n w m : Nat} {F : CNF n w}
    (j : Fin m) (step : TraceStep F) :
    BitFix n × Fin (w + 1) × Fin m :=
  -- `Fin.ofNat` просто берёт индекс по модулю `(w+1)`;
  -- для инъекции нам критично хранить `BitFix n`, а индекс литерала
  -- играет роль «контекстного тега» и не участвует в восстановлении ρ.
  ((step.var, step.value), Fin.ofNat (w + 1) step.literalIndex, j)

noncomputable def auxOfTrace
    {n w t m : Nat} {F : CNF n w} {ρ : Restriction n}
    (j : Fin m) (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    Aux n t (w + 1) m := by
  classical
  -- Канонические шаги трассы, упакованные в `Vector`.
  let steps := CanonicalTrace.toTrace (trace := trace)
  -- Для получения `BitFix` берём фиксированные пары из штрих‑кода.
  let code := Core.CNF.CanonicalTrace.barcode (trace := trace)
  have hlen :
      code.assignedFixes.length = t := by
    simpa using
      (Core.CNF.CanonicalTrace.barcode_assignedFixes_length (trace := trace))
  -- Для каждого шага берём `(BitFix, literalIndex, formulaIndex)`.
  refine fun i =>
    let bitFix :=
      code.assignedFixes.get (Fin.cast hlen.symm i)
    let step := steps.get i
    (bitFix, Fin.ofNat (w + 1) step.literalIndex, j)

/-!
### Декодирование Aux → Restriction

Для восстановления исходной рестрикции нам нужен только список `BitFix`.
Остальные поля (`Fin (w+1)` и `Fin m`) игнорируются.
-/

noncomputable def auxSimpleOfAux
    {n t k m : Nat} (aux : Aux n t k m) : AuxSimple n t :=
  fun i => (aux i).1

lemma auxSimpleOfAux_ofTrace
    {n w t m : Nat} {F : CNF n w} {ρ : Restriction n}
    (j : Fin m) (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    auxSimpleOfAux (auxOfTrace (j := j) (trace := trace))
      = auxSimpleOfTrace (trace := trace) := by
  classical
  -- Сравниваем функции по индексам.
  funext i
  simp [auxSimpleOfAux, auxOfTrace, auxSimpleOfTrace]

noncomputable def encodeBadFamilyDetCNF_aux
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyDetInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxCodes n t (w + 1) (F.length + 1))} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  -- Выбираем первую плохую формулу и её детерминированную трассу.
  let j := firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  let ρ' := Core.CNF.CanonicalTrace.finalRestriction trace
  let aux := auxOfTrace (j := Fin.ofNat (F.length + 1) j) (trace := trace)
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    simpa [ρ'] using
      (Core.CNF.CanonicalTrace.finalRestriction_mem_R_s
        (F := F.get
          ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
            (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩)
        (ρ := ρ) (s := s) (t := t) hρs trace)
  refine ⟨⟨ρ', aux⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxCodes]⟩

noncomputable def decodeBadFamilyDetCNF_aux
    {n w t : Nat} (F : FormulaFamily n w) :
    (Restriction n × Aux n t (w + 1) (F.length + 1)) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := auxSimpleOfAux aux)

lemma decode_encodeBadFamilyDetCNF_aux
    {n w t s : Nat} (F : FormulaFamily n w)
    (ρbad : BadFamilyDetInRsCNF (F := F) s t) :
    decodeBadFamilyDetCNF_aux (F := F)
        (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := firstBadTraceDet (F := F) (t := t) (ρ := ρ) hbad
  -- Используем `decodeAuxSimple_ofTrace` и согласуем код.
  have hdecode := decodeAuxSimple_ofTrace (trace := trace)
  have haux :
      auxSimpleOfAux
          (auxOfTrace (j := Fin.ofNat (F.length + 1)
            (firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad))
            (trace := trace))
        = auxSimpleOfTrace (trace := trace) := by
    simpa using
      (auxSimpleOfAux_ofTrace
        (j := Fin.ofNat (F.length + 1)
          (firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad))
        (trace := trace))
  simpa [encodeBadFamilyDetCNF_aux, decodeBadFamilyDetCNF_aux,
    auxOfTrace, haux, trace] using hdecode

lemma encodeBadFamilyDetCNF_aux_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx := decode_encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyDetCNF_aux (F := F) (t := t)
          (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) x).1
        =
      decodeBadFamilyDetCNF_aux (F := F) (t := t)
          (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) y).1 := by
    simp [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

/-!
### CCDT‑обёртка над детерминированным BadFamily

Чтобы подключить Stage‑1/Stage‑2 к интерфейсу `BadEvent`, нам нужен
детерминированный `CCDTAlgorithm`, который **эквивалентен**
`BadFamily_deterministic` (для `t > 0`).

Мы строим **честный** CCDT на основе канонических деревьев `canonicalDT_CNF`:

* для каждой формулы в семействе считаем глубину её канонического дерева;
* выбираем индекс, дающий **максимальную** глубину;
* если семейство пустое — возвращаем лист.

Это чисто детерминированная конструкция (выбор по максимуму),
и мост `BadEvent ↔ BadFamily_deterministic` доказывается через леммы
из `TraceBridge.lean`, связывающие глубину `canonicalDT_CNF` и
детерминированные канонические трассы.
-/

/--
  Глубина канонического дерева для фиксированной формулы семейства.

  Это чисто вспомогательная функция: мы фиксируем `F` и `ρ` и
  рассматриваем глубину `canonicalDT_CNF` для каждого индекса семейства.
  Такой вид удобен, когда нужно сравнивать глубины разных формул.
-/
noncomputable def canonicalDepthAt
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    Fin F.length → Nat :=
  fun i => PDT.depth (canonicalDT_CNF (F := F.get i) ρ)

/--
  Максимизатор глубины на списке индексов.

  * Если список пуст, возвращает `none`.
  * Если список непуст, возвращает индекс с максимальной глубиной
    канонического дерева `canonicalDT_CNF`.
  * При равенстве глубин выбираем **последний** (по позиции в списке)
    индекс — это фиксирует детерминированность и упрощает доказательства.

  Мы реализуем это рекурсивно: сначала берём максимум на хвосте, затем
  сравниваем его с головой и выбираем лучший.
-/
noncomputable def maxDepthIndexList
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    List (Fin F.length) → Option (Fin F.length)
  | [] => none
  | i :: rest =>
      match maxDepthIndexList F ρ rest with
      | none => some i
      | some j =>
          if canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ i then some i else some j

/--
  Максимизатор глубины на всём семействе.

  Эквивалентен `maxDepthIndexList` на `List.finRange F.length`. Это
  удобное определение, чтобы не таскать по коду явный список индексов.
-/
noncomputable def maxDepthIndex?
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    Option (Fin F.length) :=
  maxDepthIndexList F ρ (List.finRange F.length)

lemma maxDepthIndexList_spec
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    ∀ {xs i},
      maxDepthIndexList F ρ xs = some i →
      ∀ j ∈ xs, canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ i
  | [], _, h => by
      simp [maxDepthIndexList] at h
  | x :: xs, i, h => by
      classical
      -- Разбираем вариант результата из хвоста.
      cases hrest : maxDepthIndexList F ρ xs with
      | none =>
          -- В хвосте нет индексов, значит выбран `x`.
          simp [maxDepthIndexList, hrest] at h
          subst h
          intro j hj
          have hj' : j = x ∨ j ∈ xs := by
            simpa using hj
          cases hj' with
          | inl hmem =>
              subst hmem
              simp [canonicalDepthAt]
          | inr hmem =>
              cases xs with
              | nil =>
                  cases hmem
              | cons y tail =>
                  have hne : maxDepthIndexList F ρ (y :: tail) ≠ none := by
                    cases htail : maxDepthIndexList F ρ tail with
                    | none =>
                        simp [maxDepthIndexList, htail]
                    | some j =>
                        by_cases hcmp : canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ y
                        · simp [maxDepthIndexList, htail, hcmp]
                        · simp [maxDepthIndexList, htail, hcmp]
                  exact (hne hrest).elim
      | some j =>
          -- Хвост дал кандидата `j`; сравниваем с `x`.
          have hrest' :
              ∀ j' ∈ xs,
                canonicalDepthAt F ρ j' ≤ canonicalDepthAt F ρ j := by
            exact maxDepthIndexList_spec F ρ (xs := xs) (i := j) hrest
          simp [maxDepthIndexList, hrest] at h
          by_cases hcmp :
              canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ x
          · -- Если `x` не хуже `j`, то новый максимум — `x`.
            simp [hcmp] at h
            subst h
            intro j' hj'
            have hj'' : j' = x ∨ j' ∈ xs := by
              simpa using hj'
            cases hj'' with
            | inl hmem =>
                subst hmem
                simp [canonicalDepthAt]
            | inr hmem =>
                exact (hrest' _ hmem).trans hcmp
          · -- Иначе максимум остаётся `j` из хвоста.
            simp [hcmp] at h
            subst h
            intro j' hj'
            have hj'' : j' = x ∨ j' ∈ xs := by
              simpa using hj'
            cases hj'' with
            | inl hmem =>
                subst hmem
                exact le_of_lt (lt_of_not_ge hcmp)
            | inr hmem =>
                exact hrest' _ hmem

lemma maxDepthIndex?_spec
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    ∀ {i},
      maxDepthIndex? (F := F) (ρ := ρ) = some i →
      ∀ j, canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ i := by
  intro i h
  have hspec :=
    maxDepthIndexList_spec (F := F) (ρ := ρ) (xs := List.finRange F.length) (i := i) h
  intro j
  exact hspec j (by
    simp [List.mem_finRange])

lemma maxDepthIndex?_none_iff_length_zero
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    maxDepthIndex? (F := F) (ρ := ρ) = none ↔ F.length = 0 := by
  classical
  constructor
  · intro hnone
    by_contra hpos
    cases hlist : List.finRange F.length with
    | nil =>
        have hlen : F.length = 0 := (List.finRange_eq_nil).1 hlist
        exact hpos hlen
    | cons i xs =>
        have hne : maxDepthIndexList F ρ (i :: xs) ≠ none := by
          cases htail : maxDepthIndexList F ρ xs with
          | none =>
              simp [maxDepthIndexList, htail]
          | some j =>
              by_cases hcmp : canonicalDepthAt F ρ j ≤ canonicalDepthAt F ρ i
              · simp [maxDepthIndexList, htail, hcmp]
              · simp [maxDepthIndexList, htail, hcmp]
        exact (hne (by simpa [maxDepthIndex?, maxDepthIndexList, hlist] using hnone)).elim
  · intro hlen
    have hlist : List.finRange F.length = [] := by
      simpa [List.finRange_eq_nil] using hlen
    simp [maxDepthIndex?, maxDepthIndexList, hlist]

/-- Канонический CCDT для семейства CNF через `canonicalDT_CNF`. -/
noncomputable def canonicalCCDTAlgorithmCNF
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) :
    CCDTAlgorithm n w 0 t F :=
  by
    classical
    exact
      { ccdt := fun ρ =>
          match maxDepthIndex? (F := F) (ρ := ρ) with
          | none =>
              -- Пустое семейство: дерево — лист.
              PDT.leaf ρ.mask
          | some i =>
              -- Выбираем формулу с максимальной глубиной канонического дерева.
              canonicalDT_CNF (F := F.get i) ρ }

lemma badEvent_canonicalCCDT_iff_badFamilyDet
    {n w t : Nat} (F : FormulaFamily n w) (ρ : Restriction n) (ht : 0 < t) :
    BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ ↔
      BadFamily_deterministic (F := F) t ρ := by
  classical
  have ht0 : t ≠ 0 := Nat.ne_of_gt ht
  by_cases hnone :
      maxDepthIndex? (F := F) (ρ := ρ) = none
  · -- Пустое семейство: ни одна формула не может быть плохой при `t > 0`.
    have hlen : F.length = 0 :=
      (maxDepthIndex?_none_iff_length_zero (F := F) (ρ := ρ)).1 hnone
    have hbeFalse :
        ¬ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ := by
      intro hbe
      have hdepth :
          PDT.depth ((canonicalCCDTAlgorithmCNF (F := F) t).ccdt ρ) = 0 := by
        simp [canonicalCCDTAlgorithmCNF, hnone, PDT.depth]
      have hle : t ≤ 0 := by
        simpa [BadEvent, hdepth] using hbe
      exact (ht0 (Nat.eq_zero_of_le_zero hle))
    have hbadFalse : ¬ BadFamily_deterministic (F := F) t ρ := by
      intro hbad
      rcases hbad with ⟨i, hi, _⟩
      exact (Nat.lt_asymm hi (by simpa [hlen] using hi)).elim
    constructor
    · intro hbe
      exact (hbeFalse hbe).elim
    · intro hbad
      exact (hbadFalse hbad).elim
  · -- Непустой случай: выбран индекс максимальной глубины.
    cases hmax : maxDepthIndex? (F := F) (ρ := ρ) with
    | none =>
        exact (False.elim (hnone hmax))
    | some i =>
        have hspec := maxDepthIndex?_spec (F := F) (ρ := ρ) (i := i) hmax
        constructor
        · intro hbe
          -- Глубина выбранной формулы ≥ t, значит есть детерминированная bad‑трасса.
          have hdepth :
              t ≤ canonicalDepthAt F ρ i := by
            simpa [BadEvent, canonicalCCDTAlgorithmCNF, hmax, canonicalDepthAt] using hbe
          have hbadC :
              BadCNF_deterministic (F := F.get i) t ρ := by
            exact badCNF_deterministic_of_depth_ge_canonicalDT
              (F := F.get i) (t := t) (ρ := ρ) hdepth
          exact ⟨i.1, i.2, hbadC⟩
        · intro hbad
          rcases hbad with ⟨j, hj, hbadC⟩
          let j' : Fin F.length := ⟨j, hj⟩
          have hdepth_j :
              t ≤ canonicalDepthAt F ρ j' := by
            exact depth_ge_of_badCNF_deterministic
              (F := F.get j') (t := t) (ρ := ρ) hbadC
          have hdepth_i :
              canonicalDepthAt F ρ j' ≤ canonicalDepthAt F ρ i := hspec j'
          have hdepth :
              t ≤ canonicalDepthAt F ρ i := by
            exact hdepth_j.trans hdepth_i
          -- Возвращаемся к `BadEvent` для CCDT.
          simpa [BadEvent, canonicalCCDTAlgorithmCNF, hmax, canonicalDepthAt] using hdepth

lemma badRestrictions_eq_canonicalCCDT_badFamilyDet
    {n w t s : Nat} (F : FormulaFamily n w) (ht : 0 < t)
    [DecidablePred (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))]
    [DecidablePred (BadFamily_deterministic (F := F) t)] :
    badRestrictions (n := n) s
        (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))
      =
    badRestrictions (n := n) s (BadFamily_deterministic (F := F) t) := by
  classical
  ext ρ
  -- Равенство следует из эквивалентности `BadEvent ↔ BadFamily_deterministic`
  -- на всех ограничениях в `R_s`.
  constructor
  · intro hmem
    have hmem' :
        ρ ∈ R_s (n := n) s ∧ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ := by
      simpa [mem_badRestrictions] using hmem
    rcases hmem' with ⟨hRs, hbad⟩
    exact (mem_badRestrictions).2 ⟨hRs,
      (badEvent_canonicalCCDT_iff_badFamilyDet (F := F) (ρ := ρ) ht).1 hbad⟩
  · intro hmem
    have hmem' :
        ρ ∈ R_s (n := n) s ∧ BadFamily_deterministic (F := F) t ρ := by
      simpa [mem_badRestrictions] using hmem
    rcases hmem' with ⟨hRs, hbad⟩
    exact (mem_badRestrictions).2 ⟨hRs,
      (badEvent_canonicalCCDT_iff_badFamilyDet (F := F) (ρ := ρ) ht).2 hbad⟩

/-!
### Прямой encoding для BadEvent канонического CCDT (CNF)

Для `t > 0` мы переводим `BadEvent` в `BadFamily_deterministic` через
`badEvent_canonicalCCDT_iff_badFamilyDet`. Для случая `t = 0` плохими
являются **все** ограничения из `R_s`, поэтому encoding берётся как
простая инъекция `ρ ↦ (ρ, auxDefault0)`.
-/

/-- Канонический элемент `Aux` при `t = 0`. -/
def auxDefault0 (n k m : Nat) : Aux n 0 k m :=
  fun i => (Fin.elim0 i)

noncomputable def encodeBadEvent_canonicalCCDT
    {n w t s : Nat} (F : FormulaFamily n w) :
    {ρ // ρ ∈ badRestrictions (n := n) s
      (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))}
      → {c // c ∈ (R_s (n := n) (s - t)).product
        (auxCodes n t (w + 1) (F.length + 1))} := by
  classical
  intro ρbad
  by_cases ht : t = 0
  · subst ht
    have hmem :
        ρbad.1 ∈ R_s (n := n) s := by
      exact (mem_badRestrictions (n := n) (s := s)
        (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) 0))).1
          ρbad.property |>.1
    let aux0 : Aux n 0 (w + 1) (F.length + 1) :=
      auxDefault0 n (w + 1) (F.length + 1)
    have hmem' :
        ρbad.1 ∈ R_s (n := n) (s - 0) := by
      simpa using hmem
    refine ⟨⟨ρbad.1, aux0⟩, ?_⟩
    refine Finset.mem_product.2 ?_
    have haux : aux0 ∈ auxCodes n 0 (w + 1) (F.length + 1) := by
      simpa [auxCodes] using (Finset.mem_univ aux0)
    exact ⟨hmem', haux⟩
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hmem :
        ρbad.1 ∈ R_s (n := n) s := by
      exact (mem_badRestrictions (n := n) (s := s)
        (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).1
          ρbad.property |>.1
    have hbadEvent :
        BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρbad.1 := by
      exact (mem_badRestrictions (n := n) (s := s)
        (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).1
          ρbad.property |>.2
    have hbad :
        BadFamily_deterministic (F := F) t ρbad.1 :=
      (badEvent_canonicalCCDT_iff_badFamilyDet (F := F) (ρ := ρbad.1) htpos).1
        hbadEvent
    let ρbad' : BadFamilyDetInRsCNF (F := F) s t :=
      ⟨ρbad.1, hmem, hbad⟩
    exact encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) ρbad'

lemma encodeBadEvent_canonicalCCDT_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadEvent_canonicalCCDT (F := F) (t := t) (s := s)) := by
  classical
  intro x y hxy
  by_cases ht : t = 0
  · subst ht
    have hpair :
        (encodeBadEvent_canonicalCCDT (F := F) (t := 0) (s := s) x).1.1 =
          (encodeBadEvent_canonicalCCDT (F := F) (t := 0) (s := s) y).1.1 := by
      exact congrArg Prod.fst (congrArg Subtype.val hxy)
    have hxy' : x.1 = y.1 := by
      simpa [encodeBadEvent_canonicalCCDT] using hpair
    exact Subtype.ext hxy'
  · have henc :
        Function.Injective (encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t)) :=
      encodeBadFamilyDetCNF_aux_injective (F := F) (s := s) (t := t)
    let toBad :
        {ρ // ρ ∈ badRestrictions (n := n) s
          (BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))}
          → BadFamilyDetInRsCNF (F := F) s t := by
      intro ρbad
      have hmem : ρbad.1 ∈ R_s (n := n) s := by
        exact (mem_badRestrictions (n := n) (s := s)
          (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).1
            ρbad.property |>.1
      have hbadEvent :
          BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρbad.1 := by
        exact (mem_badRestrictions (n := n) (s := s)
          (bad := BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t))).1
            ρbad.property |>.2
      have hbad :
          BadFamily_deterministic (F := F) t ρbad.1 := by
        have htpos : 0 < t := Nat.pos_of_ne_zero ht
        exact (badEvent_canonicalCCDT_iff_badFamilyDet (F := F) (ρ := ρbad.1) htpos).1 hbadEvent
      exact ⟨ρbad.1, hmem, hbad⟩
    have hcode :
        encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) (toBad x) =
          encodeBadFamilyDetCNF_aux (F := F) (s := s) (t := t) (toBad y) := by
      simpa [encodeBadEvent_canonicalCCDT, ht, toBad] using hxy
    have hxy' := henc hcode
    have hρ : x.1 = y.1 := by
      simpa [toBad] using congrArg Subtype.val hxy'
    exact Subtype.ext hρ

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
    simp [hxy]
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
  | ⟨ρ', aux⟩ =>
      -- `F` не участвует в вычислении, но сохраняем его ради унифицированного интерфейса.
      have _ := F
      decodeAuxSimple (ρ' := ρ') (aux := aux)

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
    simp [hxy]
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

/-!
### EncodingWitness для канонического CCDT (CNF)

Этот свидетель связывает построенный выше encoding для `BadEvent`
с общими комбинаторными леммами для `EncodingWitness`.
-/

noncomputable def encodingWitness_canonicalCCDT_CNF
    {n w t s : Nat} (F : FormulaFamily n w) :
    EncodingWitness (A := canonicalCCDTAlgorithmCNF (F := F) t) (s := s)
      (codes := (R_s (n := n) (s - t)).product
        (auxCodes n t (w + 1) (F.length + 1))) := by
  classical
  refine { encode := ?_, inj := ?_ }
  · intro ρbad
    exact encodeBadEvent_canonicalCCDT (F := F) (t := t) (s := s) ρbad
  · intro x y hxy
    exact encodeBadEvent_canonicalCCDT_injective (F := F) (t := t) (s := s) hxy

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
