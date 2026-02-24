import ThirdPartyFacts.PsubsetPpoly
import Proof.Turing.Encoding
import Mathlib.Data.Finset.Card
/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы не повторяем
  полную формализацию классов `P`, `NP` и `P/poly`,
  а лишь фиксируем их последствия в виде именованных утверждений.  Это
  позволяет шагу D ссылаться на внешний факт `P ⊆ P/poly`
  и на целевое утверждение `P ≠ NP` без дублирования кода.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — конкретное утверждение «`P ⊆ P/poly`», предоставленное
    внешним пакетом (см. `ThirdPartyFacts/PsubsetPpoly.lean`).
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из двух пунктов
    выше.  В ранней библиотеке проекта эта теорема доказана напрямую (см. `NP_separation.lean`).

  На уровне текущего каталога `pnp3/` мы используем эти утверждения как
  внешние факты.  Включение `P ⊆ P/poly` импортируется из модуля
  `ThirdPartyFacts/PsubsetPpoly.lean`, который напрямую переиспользует
  доказательство из пакета `Facts/PsubsetPpoly`.
-/

open Facts.PsubsetPpoly

namespace Pnp3
namespace ComplexityInterfaces

/-!
### Базовые определения

Мы переиспользуем минимальные структуры из внешнего пакета `P ⊆ P/poly`.
Это гарантирует совместимость с импортируемым утверждением `P ⊆ P/poly`
и позволяет безболезненно расширять интерфейс при необходимости
добавления новых сведений о классах сложности.
-/

/-- Тип языков, используемый во внешнем пакете. -/
abbrev Language := Complexity.Language

/-- Битовые строки фиксированной длины из внешнего пакета. -/
abbrev Bitstring := Complexity.Bitstring

/--
Semantic decider model for fixed input length `n`.

`Carrier` is an explicit computational witness type, `eval` is its semantics.
Using this wrapper prevents solver interfaces from depending on a bare opaque
`Bitstring n → Bool` field only.
-/
structure SemanticDecider (n : Nat) where
  Carrier : Type
  eval : Carrier → Bitstring n → Bool

namespace SemanticDecider

/-- Canonical semantic model where the witness is the function itself. -/
@[simp] def ofFunction (n : Nat) : SemanticDecider n where
  Carrier := Bitstring n → Bool
  eval := fun f x => f x

end SemanticDecider

/-- Класс `P` из лёгкой формализации внешнего пакета. -/
abbrev P : Language → Prop := Facts.PsubsetPpoly.P.{0}

/-- Класс `P/poly` из того же пакета. -/
abbrev Ppoly : Language → Prop := Facts.PsubsetPpoly.Ppoly

/-- Вариант `P/poly`, в котором witness хранит явный carrier и `eval`. -/
abbrev PpolyStructured (L : Language) : Prop :=
  Facts.PsubsetPpoly.Complexity.PpolyStructured.{0} L

/-!
### Non-trivial structured circuit interface

`PpolyStructured` above is a migration shim from the external package and keeps
an arbitrary evaluator in the witness.  For switching-based arguments we need a
fixed circuit syntax with fixed semantics, otherwise locality claims become
vacuous.  The declarations below provide that stricter interface.
-/

/-- Fixed Boolean circuit syntax used in the strict structured interface. -/
inductive FormulaCircuit : Nat → Type
  | const  {n : Nat} : Bool → FormulaCircuit n
  | input  {n : Nat} : Fin n → FormulaCircuit n
  | not    {n : Nat} : FormulaCircuit n → FormulaCircuit n
  | and    {n : Nat} : FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  | or     {n : Nat} : FormulaCircuit n → FormulaCircuit n → FormulaCircuit n

namespace FormulaCircuit

/-- Semantics of `FormulaCircuit`. -/
def eval {n : Nat} : FormulaCircuit n → Bitstring n → Bool
  | const b, _ => b
  | input i, x => x i
  | not c, x => !(eval c x)
  | and c₁ c₂, x => eval c₁ x && eval c₂ x
  | or c₁ c₂, x => eval c₁ x || eval c₂ x

/-- Syntactic size of `FormulaCircuit`. -/
def size {n : Nat} : FormulaCircuit n → Nat
  | const _ => 1
  | input _ => 1
  | not c => size c + 1
  | and c₁ c₂ => size c₁ + size c₂ + 1
  | or c₁ c₂ => size c₁ + size c₂ + 1

/-- Syntactic depth of `FormulaCircuit` (gate layers). -/
def depth {n : Nat} : FormulaCircuit n → Nat
  | const _ => 0
  | input _ => 0
  | not c => depth c + 1
  | and c₁ c₂ => Nat.max (depth c₁) (depth c₂) + 1
  | or c₁ c₂ => Nat.max (depth c₁) (depth c₂) + 1

/-- Set of input coordinates that syntactically occur in the formula. -/
def support {n : Nat} : FormulaCircuit n → Finset (Fin n)
  | const _ => ∅
  | input i => {i}
  | not c => support c
  | and c₁ c₂ => support c₁ ∪ support c₂
  | or c₁ c₂ => support c₁ ∪ support c₂

/--
If two inputs agree on all coordinates from `support c`, then `c` evaluates
to the same value on both.
-/
lemma eval_eq_of_eq_on_support
    {n : Nat} (c : FormulaCircuit n) {x y : Bitstring n}
    (hxy : ∀ i ∈ support c, x i = y i) :
    eval c x = eval c y := by
  induction c with
  | const b =>
      simp [eval]
  | input i =>
      have hEq : x i = y i := hxy i (by simp [support])
      simpa [eval] using hEq
  | not c ih =>
      have hEq : eval c x = eval c y := ih hxy
      simp [eval, hEq]
  | and c₁ c₂ ih₁ ih₂ =>
      have hEq₁ : eval c₁ x = eval c₁ y := ih₁ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      have hEq₂ : eval c₂ x = eval c₂ y := ih₂ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      simp [eval, hEq₁, hEq₂]
  | or c₁ c₂ ih₁ ih₂ =>
      have hEq₁ : eval c₁ x = eval c₁ y := ih₁ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      have hEq₂ : eval c₂ x = eval c₂ y := ih₂ (by
        intro i hi
        exact hxy i (by simp [support, hi]))
      simp [eval, hEq₁, hEq₂]

/-- The number of support coordinates is bounded by formula size. -/
lemma support_card_le_size {n : Nat} (c : FormulaCircuit n) :
    (support c).card ≤ size c := by
  induction c with
  | const b =>
      simp [support, size]
  | input i =>
      simp [support, size]
  | not c ih =>
      simpa [support, size] using Nat.le_trans ih (Nat.le_add_right _ _)
  | and c₁ c₂ ih₁ ih₂ =>
      calc
        (support (FormulaCircuit.and c₁ c₂)).card
            = (support c₁ ∪ support c₂).card := by simp [support]
        _ ≤ (support c₁).card + (support c₂).card :=
          Finset.card_union_le (support c₁) (support c₂)
        _ ≤ size c₁ + size c₂ := Nat.add_le_add ih₁ ih₂
        _ ≤ size (FormulaCircuit.and c₁ c₂) := by simp [size]
  | or c₁ c₂ ih₁ ih₂ =>
      calc
        (support (FormulaCircuit.or c₁ c₂)).card
            = (support c₁ ∪ support c₂).card := by simp [support]
        _ ≤ (support c₁).card + (support c₂).card :=
          Finset.card_union_le (support c₁) (support c₂)
        _ ≤ size c₁ + size c₂ := Nat.add_le_add ih₁ ih₂
        _ ≤ size (FormulaCircuit.or c₁ c₂) := by simp [size]

end FormulaCircuit

/-- Strict non-uniform witness with fixed circuit syntax/semantics. -/
structure InPpolyFormula (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x

/-- Strict structured class: polynomial-size fixed-syntax formula families. -/
def PpolyFormula (L : Language) : Prop := ∃ _ : InPpolyFormula L, True

/--
Depth-bounded strict formula witness.

`d` is a global depth cap for every family member `witness.family n`.
-/
structure InPpolyFormulaDepth (L : Language) (d : Nat) where
  witness : InPpolyFormula L
  family_depth_le : ∀ n, FormulaCircuit.depth (witness.family n) ≤ d

/-- Strict structured class with explicit global depth bound `d`. -/
def PpolyFormulaDepth (L : Language) (d : Nat) : Prop :=
  ∃ _ : InPpolyFormulaDepth L d, True

/--
Non-trivial non-uniform witness used by the active magnification bridge.

Unlike the lightweight imported `InPpoly`, this interface fixes concrete
syntax/semantics (`FormulaCircuit.eval`) and concrete size
(`FormulaCircuit.size`) rather than allowing a witness-defined evaluator.
-/
structure InPpolyReal (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, FormulaCircuit n
  family_size_le : ∀ n, FormulaCircuit.size (family n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x

/-- Non-trivial non-uniform class used in place of lightweight `Ppoly`. -/
def PpolyReal (L : Language) : Prop := ∃ _ : InPpolyReal L, True

/-- Any strict formula witness is a `PpolyReal` witness. -/
theorem PpolyReal_of_PpolyFormula {L : Language} :
    PpolyFormula L → PpolyReal L := by
  intro h
  rcases h with ⟨w, _⟩
  exact ⟨{ polyBound := w.polyBound
           polyBound_poly := w.polyBound_poly
           family := w.family
           family_size_le := w.family_size_le
           correct := w.correct }, trivial⟩

/-- Any depth-bounded strict formula witness is a strict formula witness. -/
theorem PpolyFormula_of_PpolyFormulaDepth {L : Language} {d : Nat} :
    PpolyFormulaDepth L d → PpolyFormula L := by
  intro h
  rcases h with ⟨wd, _⟩
  exact ⟨wd.witness, trivial⟩

/-- Any strict formula witness yields a lightweight `P/poly` witness. -/
theorem Ppoly_of_PpolyFormula {L : Language} :
    PpolyFormula L → Ppoly L := by
  intro h
  rcases h with ⟨w, _⟩
  refine ⟨{ polyBound := w.polyBound
            polyBound_poly := trivial
            circuits := fun n x => FormulaCircuit.eval (w.family n) x
            correct := ?_ }, trivial⟩
  intro n x
  exact w.correct n x

/--
Совместимость: любой структурный witness сразу даёт текущий (облегчённый)
`P/poly` интерфейс.
-/
theorem Ppoly_of_PpolyStructured {L : Language} :
    PpolyStructured L → Ppoly L := by
  exact Facts.PsubsetPpoly.Complexity.ppoly_iff_ppolyStructured.mpr

/-- Обратная совместимость: текущий `Ppoly` можно поднять в структурную форму. -/
theorem PpolyStructured_of_Ppoly {L : Language} :
    Ppoly L → PpolyStructured L := by
  exact Facts.PsubsetPpoly.Complexity.ppoly_iff_ppolyStructured.mp

/-!
  Конструктивное определение NP через полиномиальный верификатор.

  В отличие от класса `P`, который фиксируется через Turing-машины из
  внешнего пакета, для NP мы используем *абстрактный* верификатор:
  функцию `verify`, которая принимает вход `x` и сертификат `w`.
  Это позволяет формально строить свидетельства `NP` для языков, где
  полный TM-уровень пока не развёрнут в коде.

  Важно: мы сохраняем требование полиномиальной длины сертификата и
  вводим функцию `runTime`, чтобы явно фиксировать полиномиальный
  временной бюджет в интерфейсе. Конкретная реализация TM-уровня
  (и перенос верификатора на ленту) может быть добавлена позднее
  без изменения потребителей определения.
-/

/-- Полиномиальный предел длины сертификата для входа длины `n`. -/
def certificateLength (n k : Nat) : Nat := n ^ k + k

/--
Склейка двух битовых строк. Первые `n` позиций берём из `x`,
оставшиеся `m` — из `w`. Такая кодировка позволяет передать вход и
сертификат в одном слове для верификатора.
-/
noncomputable def concatBitstring {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Bitstring (n + m) := fun i =>
  by
    classical
    by_cases h : (i : Nat) < n
    · exact x ⟨i, h⟩
    · have hge : n ≤ (i : Nat) := Nat.le_of_not_gt h
      let t := Classical.choose (Nat.exists_eq_add_of_le hge)
      have ht : (i : Nat) = n + t :=
        Classical.choose_spec (Nat.exists_eq_add_of_le hge)
      have ht_lt : t < m := by
        have : n + t < n + m := by
          simpa [ht] using i.isLt
        exact (Nat.add_lt_add_iff_left).1 this
      exact w ⟨t, ht_lt⟩

/-!
### TM-мост для `NP`

Иногда удобнее иметь формулировку NP прямо через Turing-машины из
внешнего пакета `Facts.PsubsetPpoly`. Ниже мы добавляем определение
`NP_TM` и лемму, которая переводит такое TM-свидетельство в абстрактное
`NP`-свидетельство в TM-терминах.
-/

/--
`NP_TM`: версия `NP`, сформулированная через верификатор-TM из внешнего
пакета. Машина читает вход и сертификат, склеенные в одну строку.

Эта формулировка является усилением: из неё всегда можно получить
`NP` в абстрактном смысле (см. `NP_of_NP_TM`).
-/
def NP_TM (L : Language) : Prop :=
  ∃ (M : Facts.PsubsetPpoly.TM.{0}) (c k : Nat),
    (∀ n,
      M.runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          Facts.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + certificateLength n k)
              (concatBitstring x w) = true)

/-!
### Canonical NP track (TM-faithful)

From this point onward we expose canonical `NP := NP_TM`.
-/

/-- Canonical NP class: TM verifier with polynomial runtime. -/
abbrev NP (L : Language) : Prop := NP_TM L

/-- Runtime-faithful NP track, defined directly via verifier TMs. -/
abbrev NP_strict (L : Language) : Prop := NP_TM L

/-- Backward-compatible alias kept for older imports. -/
theorem NP_of_NP_TM {L : Language} : NP_TM L → NP L := by
  intro h
  exact h

/-- Strict-track counterpart of `NP ⊄ Ppoly`. -/
def NP_strict_not_subset_Ppoly : Prop := ∃ L, NP_strict L ∧ ¬ Ppoly L

/-- Strict-track counterpart of `NP ⊄ PpolyFormula`. -/
def NP_strict_not_subset_PpolyFormula : Prop := ∃ L, NP_strict L ∧ ¬ PpolyFormula L

/--
Strict-track counterpart of depth-bounded formula separation:
`NP_TM ⊄ PpolyFormulaDepth d`.
-/
def NP_strict_not_subset_PpolyFormulaDepth (d : Nat) : Prop :=
  ∃ L, NP_strict L ∧ ¬ PpolyFormulaDepth L d

/-- Strict-track counterpart of `NP ⊄ PpolyReal`. -/
def NP_strict_not_subset_PpolyReal : Prop := ∃ L, NP_strict L ∧ ¬ PpolyReal L

/-!
### Формулировки целевых утверждений
-/

/-- Интерпретация утверждения «`NP ⊄ P/poly`» через существование языка. -/
def NP_not_subset_Ppoly : Prop := ∃ L, NP L ∧ ¬ Ppoly L

/-- Strict structured separation: there exists `L ∈ NP` with `L ∉ PpolyFormula`. -/
def NP_not_subset_PpolyFormula : Prop := ∃ L, NP L ∧ ¬ PpolyFormula L

/--
Depth-bounded strict structured separation:
there exists `L ∈ NP` with `L ∉ PpolyFormulaDepth d`.
-/
def NP_not_subset_PpolyFormulaDepth (d : Nat) : Prop :=
  ∃ L, NP L ∧ ¬ PpolyFormulaDepth L d

/--
Constructive-style bridge contract for depth-bounded formulas:
every lightweight non-uniform witness can be reified into a strict
depth-bounded formula witness with global depth cap `d`.
-/
def Ppoly_to_PpolyFormulaDepth (d : Nat) : Prop :=
  ∀ L : Language, Ppoly L → PpolyFormulaDepth L d

/-- Separation against the non-trivial non-uniform class `PpolyReal`. -/
def NP_not_subset_PpolyReal : Prop := ∃ L, NP L ∧ ¬ PpolyReal L

/-- Any strict-track separation implies the corresponding lightweight one. -/
theorem NP_not_subset_Ppoly_of_NP_strict_not_subset_Ppoly :
    NP_strict_not_subset_Ppoly → NP_not_subset_Ppoly := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/-- Any strict-track formula separation implies lightweight formula separation. -/
theorem NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula :
    NP_strict_not_subset_PpolyFormula → NP_not_subset_PpolyFormula := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/--
Any strict-track depth-bounded formula separation implies lightweight
depth-bounded formula separation.
-/
theorem NP_not_subset_PpolyFormulaDepth_of_NP_strict_not_subset_PpolyFormulaDepth
    {d : Nat} :
    NP_strict_not_subset_PpolyFormulaDepth d →
      NP_not_subset_PpolyFormulaDepth d := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩

/-- Any strict-track `PpolyReal` separation implies lightweight one. -/
theorem NP_not_subset_PpolyReal_of_NP_strict_not_subset_PpolyReal :
    NP_strict_not_subset_PpolyReal → NP_not_subset_PpolyReal := by
  intro h
  rcases h with ⟨L, hNPs, hNot⟩
  exact ⟨L, hNPs, hNot⟩


/-- Утверждение «`P ⊆ P/poly`», предоставленное внешним пакетом. -/
def P_subset_Ppoly : Prop :=
  ∀ L, Facts.PsubsetPpoly.P.{0} L → Facts.PsubsetPpoly.Ppoly L

/--
  Доказательство включения `P ⊆ P/poly`, предоставленное внешним модулем.
  Когда появится реальное доказательство, его достаточно связать с
  `ThirdPartyFacts.PsubsetPpoly.proof`.
-/
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly := by
  intro L hL
  exact (ThirdPartyFacts.P_subset_Ppoly_proof (L := L) hL)

/-- Итоговое целевое утверждение `P ≠ NP`. -/
def P_ne_NP : Prop := Facts.PsubsetPpoly.P.{0} ≠ NP

/-!
### Логический вывод `NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`
-/

/--
  Конкретная версия классического вывода: если существует язык из `NP`, не
  принадлежащий `P/poly`, а также доказано включение `P ⊆ P/poly`, то классы
  `P` и `NP` не совпадают.

  Этот аргумент полностью повторяет доказательство из архивной
  библиотеки (`P_ne_NP_of_nonuniform_separation_concrete`) и не опирается на
  дополнительные аксиомы: достаточно логики множеств и базового свойства
  включения.
-/
theorem P_ne_NP_of_nonuniform_separation_concrete
    (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) :
    P_ne_NP := by
  classical
  -- Предположим противное и выведем противоречие с `hNP`.
  refine fun hEq => ?_
  have hNP_subset_P : ∀ {L : Language}, NP L → Facts.PsubsetPpoly.P.{0} L := by
    intro L hL
    have hEq_pointwise : Facts.PsubsetPpoly.P.{0} L = NP L := congrArg (fun f => f L) hEq
    exact hEq_pointwise.symm ▸ hL
  have hNP_subset_Ppoly : ∀ {L : Language}, NP L → Ppoly L := by
    intro L hL
    exact hP L (hNP_subset_P hL)
  rcases hNP with ⟨L₀, hL₀_NP, hL₀_not_Ppoly⟩
  exact hL₀_not_Ppoly (hNP_subset_Ppoly hL₀_NP)

/-- Совместимость с прежним именем аксиомы. -/
theorem P_ne_NP_of_nonuniform_separation
    (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_separation_concrete hNP hP

/-- Strict-track non-uniform separation implies `P ≠ NP` (via lightweight bridge). -/
theorem P_ne_NP_of_NP_strict_not_subset_Ppoly
    (hStrict : NP_strict_not_subset_Ppoly)
    (hP : P_subset_Ppoly := P_subset_Ppoly_proof) :
    P_ne_NP := by
  exact P_ne_NP_of_nonuniform_separation
    (NP_not_subset_Ppoly_of_NP_strict_not_subset_Ppoly hStrict) hP

/--
Strict formula-track separation implies `P ≠ NP` once we provide the same
bridge used in the lightweight path (`NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`).
-/
theorem P_ne_NP_of_NP_strict_not_subset_PpolyFormula
    (hStrict : NP_strict_not_subset_PpolyFormula)
    (hFormulaToPpoly :
      NP_not_subset_PpolyFormula → NP_not_subset_Ppoly)
    (hP : P_subset_Ppoly := P_subset_Ppoly_proof) :
    P_ne_NP := by
  have hLight : NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula hStrict
  exact P_ne_NP_of_nonuniform_separation (hFormulaToPpoly hLight) hP

/--
Depth-bounded strict formula-track separation implies `P ≠ NP` once we provide
the corresponding depth-bounded bridge
`NP_not_subset_PpolyFormulaDepth d -> NP_not_subset_Ppoly`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_PpolyFormulaDepth
    {d : Nat}
    (hStrict : NP_strict_not_subset_PpolyFormulaDepth d)
    (hFormulaDepthToPpoly :
      NP_not_subset_PpolyFormulaDepth d → NP_not_subset_Ppoly)
    (hP : P_subset_Ppoly := P_subset_Ppoly_proof) :
    P_ne_NP := by
  have hLight : NP_not_subset_PpolyFormulaDepth d :=
    NP_not_subset_PpolyFormulaDepth_of_NP_strict_not_subset_PpolyFormulaDepth hStrict
  exact P_ne_NP_of_nonuniform_separation (hFormulaDepthToPpoly hLight) hP

/--
From a constructive bridge `Ppoly -> PpolyFormulaDepth d`, any depth-bounded
formula separation immediately yields non-uniform separation.
-/
theorem NP_not_subset_Ppoly_of_Ppoly_to_PpolyFormulaDepth
    {d : Nat}
    (hBridge : Ppoly_to_PpolyFormulaDepth d) :
    NP_not_subset_PpolyFormulaDepth d → NP_not_subset_Ppoly := by
  intro hSepDepth
  rcases hSepDepth with ⟨L, hNP, hNotDepth⟩
  refine ⟨L, hNP, ?_⟩
  intro hPpoly
  exact hNotDepth (hBridge L hPpoly)

/--
Strict `PpolyReal`-track separation implies `P ≠ NP` once we provide a bridge
from `NP_not_subset_PpolyReal` to `NP_not_subset_Ppoly`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_PpolyReal
    (hStrict : NP_strict_not_subset_PpolyReal)
    (hRealToPpoly :
      NP_not_subset_PpolyReal → NP_not_subset_Ppoly)
    (hP : P_subset_Ppoly := P_subset_Ppoly_proof) :
    P_ne_NP := by
  have hLight : NP_not_subset_PpolyReal :=
    NP_not_subset_PpolyReal_of_NP_strict_not_subset_PpolyReal hStrict
  exact P_ne_NP_of_nonuniform_separation (hRealToPpoly hLight) hP

/--
  Удобная форма для работы от противного: если из предположения
  `∀ L, NP L → P/poly` можно вывести противоречие, то автоматически
  существует язык из `NP`, не лежащий в `P/poly`.

  При работе от противного мы используем классическое рассуждение:
  отрицание импликации `NP L → Ppoly L` даёт одновременно `NP L` и
  `¬ Ppoly L`, то есть явный контрпример к включению.
-/
theorem NP_not_subset_Ppoly_of_contra
    (hContra : (∀ L : Language, NP L → Ppoly L) → False) :
    NP_not_subset_Ppoly := by
  classical
  -- Отрицание универсального включения даёт конкретный язык `L`.
  have hNotAll : ¬ (∀ L : Language, NP L → Ppoly L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  -- Из `¬ (NP L → Ppoly L)` классически выводим `NP L`.
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → Ppoly L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  -- А также `¬ Ppoly L`.
  have hNotPpoly : ¬ Ppoly L := by
    intro hPpoly
    have hImp : NP L → Ppoly L := by
      intro _hL
      exact hPpoly
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpoly⟩

/-- Contra form for the strict structured class `PpolyFormula`. -/
theorem NP_not_subset_PpolyFormula_of_contra
    (hContra : (∀ L : Language, NP L → PpolyFormula L) → False) :
    NP_not_subset_PpolyFormula := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP L → PpolyFormula L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → PpolyFormula L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyFormula : ¬ PpolyFormula L := by
    intro hPpolyFormula
    have hImp : NP L → PpolyFormula L := by
      intro _hL
      exact hPpolyFormula
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyFormula⟩

/-- Contra form for `PpolyReal`. -/
theorem NP_not_subset_PpolyReal_of_contra
    (hContra : (∀ L : Language, NP L → PpolyReal L) → False) :
    NP_not_subset_PpolyReal := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP L → PpolyReal L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → PpolyReal L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyReal : ¬ PpolyReal L := by
    intro hPpolyReal
    have hImp : NP L → PpolyReal L := by
      intro _hL
      exact hPpolyReal
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyReal⟩

/-- `NP ⊄ PpolyReal` immediately yields `NP ⊄ PpolyFormula`. -/
theorem NP_not_subset_PpolyFormula_of_PpolyReal
    (hSep : NP_not_subset_PpolyReal) :
    NP_not_subset_PpolyFormula := by
  rcases hSep with ⟨L, hNP, hNotReal⟩
  refine ⟨L, hNP, ?_⟩
  intro hFormula
  exact hNotReal (PpolyReal_of_PpolyFormula hFormula)

/--
Separation against the larger class `PpolyFormula` implies separation against
every depth-bounded subclass `PpolyFormulaDepth d`.
-/
theorem NP_not_subset_PpolyFormulaDepth_of_NP_not_subset_PpolyFormula
    {d : Nat}
    (hSep : NP_not_subset_PpolyFormula) :
    NP_not_subset_PpolyFormulaDepth d := by
  rcases hSep with ⟨L, hNP, hNotFormula⟩
  refine ⟨L, hNP, ?_⟩
  intro hDepth
  exact hNotFormula (PpolyFormula_of_PpolyFormulaDepth hDepth)

/-- Эквивалентная форма `NP_not_subset_Ppoly` через отрицание включения. -/
theorem NP_not_subset_Ppoly_iff_not_forall :
    NP_not_subset_Ppoly ↔ ¬ (∀ L : Language, NP L → Ppoly L) := by
  constructor
  · intro hSep hAll
    rcases hSep with ⟨L, hNP, hNotPpoly⟩
    exact hNotPpoly (hAll L hNP)
  · intro hNotAll
    exact NP_not_subset_Ppoly_of_contra (by
      intro hAll
      exact hNotAll hAll)

/-! ### Strict-track contra forms -/

/-- Contra form for strict non-uniform separation (`NP_TM ⊄ Ppoly`). -/
theorem NP_strict_not_subset_Ppoly_of_contra
    (hContra : (∀ L : Language, NP_strict L → Ppoly L) → False) :
    NP_strict_not_subset_Ppoly := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP_strict L → Ppoly L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP_strict L := by
    by_contra hNP
    have hImp : NP_strict L → Ppoly L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpoly : ¬ Ppoly L := by
    intro hPpoly
    have hImp : NP_strict L → Ppoly L := by
      intro _hL
      exact hPpoly
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpoly⟩

/-- Contra form for strict formula separation (`NP_TM ⊄ PpolyFormula`). -/
theorem NP_strict_not_subset_PpolyFormula_of_contra
    (hContra : (∀ L : Language, NP_strict L → PpolyFormula L) → False) :
    NP_strict_not_subset_PpolyFormula := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP_strict L → PpolyFormula L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP_strict L := by
    by_contra hNP
    have hImp : NP_strict L → PpolyFormula L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyFormula : ¬ PpolyFormula L := by
    intro hPpolyFormula
    have hImp : NP_strict L → PpolyFormula L := by
      intro _hL
      exact hPpolyFormula
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyFormula⟩

/-- Contra form for strict `PpolyReal` separation (`NP_TM ⊄ PpolyReal`). -/
theorem NP_strict_not_subset_PpolyReal_of_contra
    (hContra : (∀ L : Language, NP_strict L → PpolyReal L) → False) :
    NP_strict_not_subset_PpolyReal := by
  classical
  have hNotAll : ¬ (∀ L : Language, NP_strict L → PpolyReal L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  have hNP : NP_strict L := by
    by_contra hNP
    have hImp : NP_strict L → PpolyReal L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  have hNotPpolyReal : ¬ PpolyReal L := by
    intro hPpolyReal
    have hImp : NP_strict L → PpolyReal L := by
      intro _hL
      exact hPpolyReal
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpolyReal⟩

end ComplexityInterfaces
end Pnp3
