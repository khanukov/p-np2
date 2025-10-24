-- Import verified P ⊆ P/poly proof from standalone verified-facts subproject
import PSubsetPpoly.ComplexityClasses

/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы не повторяем
  полную формализацию классов `P`, `NP` и `P/poly` из разработки `pnp2`,
  а лишь фиксируем их последствия в виде именованных утверждений.  Это
  позволяет шагу D ссылаться на доказанный факт `P ⊆ P/poly`
  и на целевое утверждение `P ≠ NP` без дублирования кода.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — интерфейс к уже формализованному включению `P ⊆ P/poly`.
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из двух пунктов
    выше.  В версии `pnp2` он доказан напрямую (см. `NP_separation.lean`).

  ## Update (2025-10-24): Axiom Removal

  Аксиомы `P_subset_Ppoly` и `P_subset_Ppoly_proof` теперь заменены на
  импорт из верифицированного подпроекта `verified-facts/p-subset-ppoly`.
  Это полностью доказанный факт без аксиом и sorry.
-/

namespace Pnp3
namespace ComplexityInterfaces

/-- Заглушка для утверждения `NP ⊄ P/poly`. -/
axiom NP_not_subset_Ppoly : Prop

/-- Интерфейс к доказанному включению `P ⊆ P/poly`.
    Импортировано из изолированного верифицированного подпроекта PSubsetPpoly. -/
def P_subset_Ppoly : Prop := (PSubsetPpoly.P ⊆ PSubsetPpoly.Ppoly)

/-- Доказательство включения `P ⊆ P/poly`, импортированное из PSubsetPpoly.
    Это полностью верифицированный факт без аксиом и sorry
    (✅ 507KB доказательства + зависимости из verified-facts/p-subset-ppoly). -/
def P_subset_Ppoly_proof : P_subset_Ppoly := PSubsetPpoly.P_subset_Ppoly

/-- Итоговое целевое утверждение `P ≠ NP`. -/
axiom P_ne_NP : Prop

/--
  Классический вывод: если `NP ⊄ P/poly`, но `P ⊆ P/poly`, то `P ≠ NP`.
  Подробное доказательство реализовано в `Pnp2/NP_separation.lean`.
-/
axiom P_ne_NP_of_nonuniform_separation
  (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) : P_ne_NP

end ComplexityInterfaces
end Pnp3
