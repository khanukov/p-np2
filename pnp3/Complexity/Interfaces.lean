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

namespace Pnp3
namespace ComplexityInterfaces

/-- Заглушка для утверждения `NP ⊄ P/poly`. -/
axiom NP_not_subset_Ppoly : Prop

/-- Утверждение «`P ⊆ P/poly`», предоставленное внешним пакетом. -/
abbrev P_subset_Ppoly : Prop :=
  ThirdPartyFacts.P_subset_Ppoly

/--
  Доказательство включения `P ⊆ P/poly`, предоставленное внешним модулем.
  Когда появится реальное доказательство, его достаточно связать с
  `ThirdPartyFacts.PsubsetPpoly.proof`.
-/
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly := by
  simpa [P_subset_Ppoly] using ThirdPartyFacts.P_subset_Ppoly_proof

/-- Итоговое целевое утверждение `P ≠ NP`. -/
axiom P_ne_NP : Prop

/--
  Классический вывод: если `NP ⊄ P/poly`, но `P ⊆ P/poly`, то `P ≠ NP`.
  Подробное доказательство реализовано в отдельной библиотеке (см. `NP_separation.lean`).
-/
axiom P_ne_NP_of_nonuniform_separation
  (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) : P_ne_NP

end ComplexityInterfaces
end Pnp3
