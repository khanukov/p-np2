import Pnp2.BoolFunc
import Pnp2.Boolcube
import Pnp2.Sunflower.RSpread
-- Additional cover modules are still incomplete, so we test RSpread only.

open BoolFunc
open Boolcube

namespace CoverExtraTests



/-- A nonempty family is `1`-spread. -/
example : RSpread (R := 1) ({∅} : Finset (Finset (Fin 1))) := by
  have hA : ({∅} : Finset (Finset (Fin 1))).Nonempty := by simp
  simpa using RSpread.one_of_nonempty (A := {∅}) (hA := hA)

/-- Bounding the filtered cardinal for a trivial family. -/
example (S : Finset (Fin 1)) :
    let A : Finset (Finset (Fin 1)) := {∅}
    ((A.filter fun T ↦ S ⊆ T).card : ℝ) ≤
      A.card * Real.rpow (1 : ℝ) (-(S.card : ℝ)) := by
  intro A
  classical
  have hA : A.Nonempty := by simp [A]
  have hspread : RSpread (R := 1) A :=
    RSpread.one_of_nonempty (A := A) (hA := hA)
  simpa [A] using
    RSpread.card_filter_le (A := A) (h := hspread) (S := S)


-- Further cover lemmas are not yet available in the migrated code.

end CoverExtraTests

