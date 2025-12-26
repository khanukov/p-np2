import Mathlib.Data.Fin.Tuple.Basic
import ThirdPartyFacts.PsubsetPpoly
/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы не повторяем
  полную формализацию классов `P` и `P/poly`,
  а также используем компактное, но полноценное определение `NP`
  через полиномиальный верификатор.  Это позволяет шагу D ссылаться на
  внешний факт `P ⊆ P/poly`
  и на целевое утверждение `P ≠ NP` без дублирования кода.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — конкретное утверждение «`P ⊆ P/poly`», предоставленное
    внешним пакетом (см. `ThirdPartyFacts/PsubsetPpoly.lean`).
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из двух пунктов
    выше.  В ранней библиотеке проекта эта теорема доказана напрямую (см. `NP_separation.lean`).

  На уровне текущего каталога `pnp3/` мы продолжаем рассматривать эти
  утверждения как внешние факты.  Включение `P ⊆ P/poly` поступает из
  внешнего модуля `ThirdPartyFacts/PsubsetPpoly.lean` и по умолчанию остаётся
  аксиоматическим, пока не подключено конкретное доказательство.
-/

open Facts.PsubsetPpoly

namespace Pnp3
namespace ComplexityInterfaces

/-!
### Базовые определения

Мы переиспользуем минимальные структуры из внешнего пакета `P ⊆ P/poly`.
Это гарантирует совместимость с импортируемым утверждением `P ⊆ P/poly`
и даёт единую точку входа для стандартного определения `NP` через
полиномиальный верификатор, не меняя интерфейс шагов D.
-/

/-- Тип языков, используемый во внешнем пакете. -/
abbrev Language := Complexity.Language

/-- Битстроки фиксированной длины, согласованные с внешним пакетом. -/
abbrev Bitstring := Facts.PsubsetPpoly.Bitstring

/-- Класс `P` из лёгкой формализации внешнего пакета. -/
abbrev P : Language → Prop := Facts.PsubsetPpoly.P.{0}

/-- Класс `P/poly` из того же пакета. -/
abbrev Ppoly : Language → Prop := Facts.PsubsetPpoly.Ppoly

/-- Конкатенация входа и сертификата в единый битстринг длины `n + m`. -/
def concatBitstring {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Bitstring (n + m) :=
  Fin.append x w

/-- Полиномиальная граница длины сертификата: `n ↦ n^c + c`. -/
def verifierBound (c : Nat) (n : Nat) : Nat := n ^ c + c

/--
  Полноценное определение класса `NP` через полиномиальный верификатор.
  Мы используем тот же стиль полиномиальной оценки, что и для `P` в
  лёгком пакете (`n^c + c`), и кодируем пару `(x, w)` простой конкатенацией.
-/
def NP (L : Language) : Prop :=
  ∃ (V : Language) (c : Nat),
    Facts.PsubsetPpoly.Complexity.polyTimeDecider.{0} V ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (verifierBound c n),
          V (n + verifierBound c n) (concatBitstring x w) = true)

/-!
### Базовый пример: пустой язык лежит в NP
-/

/-- Язык, который отвергает все входы. -/
def falseLanguage : Language := fun _ _ => false

/-- Тьюрингова машина, которая всегда отклоняет вход. -/
def rejectTM : Facts.PsubsetPpoly.TM.{0} where
  state := Bool
  start := false
  accept := true
  step := fun s _ => (s, false, Facts.PsubsetPpoly.Move.stay)
  runTime := fun _ => 0

lemma rejectTM_accepts (n : Nat) (x : Bitstring n) :
    Facts.PsubsetPpoly.TM.accepts (M := rejectTM) (n := n) x = false := by
  simp [Facts.PsubsetPpoly.TM.accepts, Facts.PsubsetPpoly.TM.run,
    Facts.PsubsetPpoly.TM.runConfig, rejectTM]

theorem polyTimeDecider_falseLanguage :
    Facts.PsubsetPpoly.Complexity.polyTimeDecider.{0} falseLanguage := by
  refine ⟨rejectTM, 0, ?_, ?_⟩
  · intro n
    simp [rejectTM]
  · intro n x
    simpa [falseLanguage] using (rejectTM_accepts n x)

/-!
### Формулировки целевых утверждений
-/

/-- Интерпретация утверждения «`NP ⊄ P/poly`» через существование языка. -/
def NP_not_subset_Ppoly : Prop := ∃ L, NP L ∧ ¬ Ppoly L

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

/--
  Удобная форма для работы от противного: если из предположения
  `∀ L, NP L → P/poly` можно вывести противоречие, то автоматически
  существует язык из `NP`, не лежащий в `P/poly`.

  В отличие от ранней версии, здесь используется полноценное определение `NP`,
  поэтому для извлечения контрпримера применяется классическая логика
  (разбор по случаям).
-/
theorem NP_not_subset_Ppoly_of_contra
    (hContra : (∀ L : Language, NP L → Ppoly L) → False) :
    NP_not_subset_Ppoly :=
by
  classical
  -- Отрицание универсального включения даёт конкретный язык `L`.
  have hNotAll : ¬ (∀ L : Language, NP L → Ppoly L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  by_cases hNP : NP L
  · have hNotPpoly : ¬ Ppoly L := by
      intro hP
      exact hNotImp (fun _ => hP)
    exact ⟨L, hNP, hNotPpoly⟩
  · have hImp : NP L → Ppoly L := by
      intro h
      exact (False.elim (hNP h))
    exact (False.elim (hNotImp hImp))

/-- Эквивалентная форма `NP_not_subset_Ppoly` через отрицание включения. -/
theorem NP_not_subset_Ppoly_iff_not_forall :
    NP_not_subset_Ppoly ↔ ¬ (∀ L : Language, NP L → Ppoly L) :=
by
  constructor
  · intro hSep
    classical
    rcases hSep with ⟨L, hNP, hNotPpoly⟩
    intro hAll
    exact hNotPpoly (hAll L hNP)
  · intro hNotAll
    classical
    rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
    by_cases hNP : NP L
    · have hNotPpoly : ¬ Ppoly L := by
        intro hP
        exact hNotImp (fun _ => hP)
      exact ⟨L, hNP, hNotPpoly⟩
    · have hImp : NP L → Ppoly L := by
        intro h
        exact (False.elim (hNP h))
      exact (False.elim (hNotImp hImp))

end ComplexityInterfaces
end Pnp3
