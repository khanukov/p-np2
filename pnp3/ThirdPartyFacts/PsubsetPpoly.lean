/-
  pnp3/ThirdPartyFacts/PsubsetPpoly.lean

  Формальный интерфейс к внешнему факту `P ⊆ P/poly`.  После помещения
  всех определений стоечного пакета в пространство имён `Facts.PsubsetPpoly`
  возможные конфликты имён с прежними формализациями исчезают, и мы можем напрямую импортировать
  доказательство из каталога `Facts/PsubsetPpoly`.
-/

import FactPsubsetPpoly

namespace Pnp3
namespace ThirdPartyFacts
namespace PsubsetPpoly

-- Чтобы сделать источники явными, работаем в пространстве имён
-- `Facts.PsubsetPpoly`.  Оно содержит определения классов сложности и
-- доказательство включения.
open Facts.PsubsetPpoly

/--
  Формулируем внешнее утверждение «`P ⊆ P/poly`» как явно квантифицированное
  включение классов: для любого языка `L`, если он лежит в `P`, то он лежит в
  `P/poly`.
-/
def statement : Prop := ∀ L, Complexity.P L → Complexity.Ppoly L

/--
  Доказательство включения `P ⊆ P/poly`, предоставленное модулем
  `Facts/PsubsetPpoly`.
-/
theorem proof : statement := by
  intro L hL
  -- Оборачиваем импортированную теорему в локальное пространство имён.
  exact Proof.complexity_P_subset_Ppoly hL

end PsubsetPpoly

/-- Утверждение «`P ⊆ P/poly`», используемое внутри `pnp3`. -/
abbrev P_subset_Ppoly : Prop := PsubsetPpoly.statement

/-- Доказательство включения `P ⊆ P/poly`, предоставленное внешним пакетом. -/
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly :=
  PsubsetPpoly.proof

end ThirdPartyFacts
end Pnp3
