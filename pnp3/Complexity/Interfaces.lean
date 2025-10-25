import Pnp2.ComplexityClasses
import Pnp2.NP_separation

/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы импортируем
  полную формализацию классов `P`, `NP` и `P/poly` из разработки `pnp2`,
  включая доказанное включение `P ⊆ P/poly`.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — пропозициональная версия включения `P ⊆ P/poly`.
  * `P_subset_Ppoly_proof` — доказательство этого включения из `pnp2`.
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из `NP_separation.lean`.
-/

namespace Pnp3
namespace ComplexityInterfaces

/-- Заглушка для утверждения `NP ⊄ P/poly`. -/
def NP_not_subset_Ppoly : Prop := NP ⊄ Ppoly

/-- Пропозициональная версия включения `P ⊆ P/poly`. -/
def P_subset_Ppoly : Prop := P ⊆ Ppoly

/-- Доказательство включения `P ⊆ P/poly`, импортированное из `pnp2`. -/
theorem P_subset_Ppoly_proof : P_subset_Ppoly := _root_.P_subset_Ppoly

/-- Итоговое целевое утверждение `P ≠ NP`. -/
def P_ne_NP : Prop := P ≠ NP

/--
  Классический вывод: если `NP ⊄ P/poly`, но `P ⊆ P/poly`, то `P ≠ NP`.
  Доказательство взято из `Pnp2/NP_separation.lean`.
-/
theorem P_ne_NP_of_nonuniform_separation
  (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) : P_ne_NP :=
  P_ne_NP_of_NP_not_subset_Ppoly hNP hP

end ComplexityInterfaces
end Pnp3
