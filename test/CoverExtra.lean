import Pnp.BoolFunc
import Pnp.Boolcube
import Pnp.Sunflower.RSpread
-- Additional cover modules are still incomplete, so we test RSpread only.

open BoolFunc
open Boolcube

namespace CoverExtraTests



/-- A nonempty family is `1`-spread. -/
example : RSpread (R := 1) ({∅} : Finset (Finset (Fin 1))) := by
  have hA : ({∅} : Finset (Finset (Fin 1))).Nonempty := by simp
  simpa using RSpread.one_of_nonempty (A := {∅}) (hA := hA)


-- Further cover lemmas are not yet available in the migrated code.

end CoverExtraTests

