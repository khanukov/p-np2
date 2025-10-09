import LowerBounds.LB_LocalCircuits
import Magnification.LocalityLift

/-!
  pnp3/LowerBounds/LB_GeneralFromLocal.lean

  Этот файл собирает мост "общие схемы → локальные схемы".  Используя
  аксиому `locality_lift`, мы редуцируем гипотезу о малом общем решателе
  GapMCSP к наличию локального решателя.  После этого применяется уже
  доказанная лемма `LB_LocalCircuits_core`, что завершает аргумент.
-/

namespace Pnp3
namespace LowerBounds

open Magnification

/--
  Если существует малый общий решатель GapMCSP, то по `locality_lift`
  существует и локальный решатель сопоставимых параметров.  Но локальные
  решатели запрещены `LB_LocalCircuits_core`, значит общих решателей тоже
  быть не может.  Все численные оценки, возвращаемые `locality_lift`,
  сохраняются в распаковке `obtain`, чтобы их можно было использовать в
  дальнейшем (например, при построении явного противоречия).
-/
theorem LB_GeneralFromLocal
  {p : Models.GapMCSPParams}
  (solver : SmallGeneralCircuitSolver p) : False := by
  classical
  obtain ⟨T, loc, hT, hM, hℓ, hdepth⟩ := locality_lift solver
  exact LB_LocalCircuits_core (p := p) (solver := loc)

end LowerBounds
end Pnp3
