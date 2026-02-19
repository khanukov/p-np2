import Complexity.Reductions
import Models.Model_PartialMCSP

/-!
  pnp3/ThirdPartyFacts/Hirahara2022.lean

  Hirahara (FOCS 2022): Partial MCSP is NP-hard under randomized reductions.

  Мы фиксируем этот внешний результат в виде аксиомы.  В текущем проекте
  редукции моделируются логически (`Is_NP_Hard` из `Complexity/Reductions.lean`),
  поэтому аксиома выражает NP-трудность языка Partial MCSP для некоторых
  фиксированных параметров.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Complexity
open Models

/--
  Hirahara (2022): Partial MCSP NP-hard.

  Формально: существует параметр `p`, такой что язык `gapPartialMCSP_Language p`
  NP-труден в смысле `Is_NP_Hard`.
-/
axiom PartialMCSP_is_NP_Hard :
  ∃ (p : GapPartialMCSPParams), Is_NP_Hard (gapPartialMCSP_Language p)

end ThirdPartyFacts
end Pnp3
