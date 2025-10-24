import Pnp2.PsubsetPpoly
import Pnp2.ComplexityClasses.PsubsetPpoly

/-!
# Fact: `P ⊆ P/poly`

This module exposes the classical inclusion of polynomial-time languages into
non-uniform polynomial size.  It simply re-exports the development from the
original `Pnp2` project so that the fact can be consumed as a standalone
library inside the monorepo.
-/

namespace Facts
namespace PsubsetPpoly

export Complexity (inPpoly_of_polyBound)
export Pnp2.PsubsetPpoly (complexity_P_subset_Ppoly)

end PsubsetPpoly
end Facts
