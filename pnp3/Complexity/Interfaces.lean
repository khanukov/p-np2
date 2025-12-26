import ThirdPartyFacts.PsubsetPpoly
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
и позволяет позднее заменить временные определения полноценными
конструктивными описаниями из архивного проекта без изменения интерфейса.
-/

/-- Тип языков, используемый во внешнем пакете. -/
abbrev Language := Complexity.Language

/-- Класс `P` из лёгкой формализации внешнего пакета. -/
abbrev P : Language → Prop := Facts.PsubsetPpoly.P.{0}

/-- Класс `P/poly` из того же пакета. -/
abbrev Ppoly : Language → Prop := Facts.PsubsetPpoly.Ppoly

/--
  Временное определение класса `NP`.  Здесь это просто абстрактный
  предикат на языках; конкретная конструкция через недетерминированные
  машины Тьюринга будет подключена при интеграции с архивной библиотекой.
-/
def NP (_L : Language) : Prop := True

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

  Важно, что наше временное определение `NP` редуцируется к `True`,
  поэтому `¬ (NP L → Ppoly L)` сводится к `¬ Ppoly L`.  Это позволяет
  легко распаковать контрпример из отрицания универсального включения.
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
  -- Поскольку `NP L` сводится к `True`, отрицание импликации означает
  -- `¬ Ppoly L`.
  have hNotPpoly : ¬ Ppoly L := by
    simpa [NP] using hNotImp
  -- Формируем требуемый контрпример.
  refine ⟨L, ?_, hNotPpoly⟩
  simp [NP]

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
    have hNotPpoly : ¬ Ppoly L := by simpa [NP] using hNotImp
    refine ⟨L, ?_, hNotPpoly⟩
    simp [NP]

end ComplexityInterfaces
end Pnp3
