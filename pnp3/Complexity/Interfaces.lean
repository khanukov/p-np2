/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы не повторяем
  полную формализацию классов `P`, `NP` и `P/poly` из разработки `pnp2`,
  а лишь фиксируем их последствия в виде именованных утверждений.  Это
  позволяет шагу D ссылаться на доказанный в `pnp2` факт `P ⊆ P/poly`
  и на целевое утверждение `P ≠ NP` без дублирования кода.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — интерфейс к уже формализованному включению `P ⊆ P/poly`.
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из двух пунктов
    выше.  В версии `pnp2` он доказан напрямую (см. `NP_separation.lean`).

  На уровне текущего каталога `pnp3/` эти утверждения считаются внешними
  фактами (аксиомами) и используются при связывании магнификации с итоговым
  разделением классов.
-/

namespace Pnp3
namespace ComplexityInterfaces

/-- Заглушка для утверждения `NP ⊄ P/poly`. -/
axiom NP_not_subset_Ppoly : Prop

/-- Интерфейс к доказанному в `pnp2` включению `P ⊆ P/poly`. -/
axiom P_subset_Ppoly : Prop

/-- Доказательство включения `P ⊆ P/poly`, заимствованное из `pnp2`. -/
axiom P_subset_Ppoly_proof : P_subset_Ppoly

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
