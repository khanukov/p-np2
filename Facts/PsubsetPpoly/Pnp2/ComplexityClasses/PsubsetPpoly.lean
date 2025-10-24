import Pnp2.ComplexityClasses
import Pnp2.PsubsetPpoly

/-!
  Bridge the constructive proof of `P \u2286 P/poly` with the high-level
  complexity class interface.  By splitting this file off from
  `ComplexityClasses.lean` we avoid a circular import between the
  definitions of the classes and the simulation infrastructure.
-/

namespace Pnp2
namespace PsubsetPpoly

open Pnp2
open Pnp2.ComplexityClasses

/--
  The classical inclusion `P ⊆ P/poly`, restated in terms of the language
  interface from `ComplexityClasses.lean`.
-/
theorem complexity_P_subset_Ppoly :
    P ⊆ Ppoly := by
  intro L hL
  rcases hL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨Complexity.inPpoly_of_polyBound (M := M) (c := c)
      hRun hCorrect, trivial⟩

end PsubsetPpoly
end Pnp2
