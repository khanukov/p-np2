import Magnification.FinalResult
import Magnification.Bridge_to_Magnification_Partial
import Complexity.Interfaces
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/Audit/Axioms.lean

  Единая точка аудита «висящих» аксиом/placeholder-ов.  Этот файл нужен,
  чтобы быстро видеть, какие именно зависимости ещё остаются в ключевых
  фактах (switching/shrinkage → магнификация → финальный результат).

  Как пользоваться:
  * компилируйте этот файл вместе с проектом;
  * проверяйте вывод `#print axioms ...` и убеждайтесь, что список
    зависит только от ожидаемых внешних фактов.
-/

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification

-- Блок, который должен исчезнуть после закрытия multi-switching.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.ac0PolylogBoundWitness_of_multi_switching

-- Итоговые утверждения пайплайна (активный формульный выход).
#print axioms NP_not_subset_PpolyFormula_final
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas
