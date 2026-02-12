import Complexity.Reductions
import Models.Model_PartialMCSP

/-!
  pnp3/ThirdPartyFacts/Hirahara2022.lean

  Hirahara (FOCS 2022): Partial MCSP is NP-hard under randomized reductions.

  В этом файле мы фиксируем внешний результат в виде аксиом, но с
  корректными *асимптотическими* типами:

  * профильный язык `gapPartialMCSP_Language_profile`;
  * NP-трудность под randomized polytime many-one сведениями.

  Для обратной совместимости оставляем legacy-аксиому для фиксированного
  параметра и purely-logical `Is_NP_Hard`.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Complexity
open Models

/--
  Асимптотическая формулировка внешнего факта Hirahara (2022):
  существует профиль порогов Partial MCSP, NP-трудный под randomized
  polytime many-one сведениями.
-/
axiom PartialMCSP_profile_is_NP_Hard_rpoly :
  ∃ (prof : GapPartialMCSPProfile),
    Is_NP_Hard_rpoly (gapPartialMCSP_Language_profile prof)

/--
  Legacy-совместимость: прежняя аксиома NP-трудности в purely-logical типе
  для фиксированных параметров.
-/
axiom PartialMCSP_is_NP_Hard :
  ∃ (p : GapPartialMCSPParams), Is_NP_Hard (gapPartialMCSP_Language p)

end ThirdPartyFacts
end Pnp3
