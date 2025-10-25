import Proof.Simulation
import Proof.Complexity.PsubsetPpoly

/-!
# Fact: `P ⊆ P/poly`

This module exposes the classical inclusion of polynomial-time languages into
non-uniform polynomial size.  It re-exports the standalone development housed in
`Facts/PsubsetPpoly/Proof`, presenting a minimal interface for downstream
projects.
-/

namespace Facts
namespace PsubsetPpoly

export Complexity (inPpoly_of_polyBound)
export Proof (complexity_P_subset_Ppoly)

end PsubsetPpoly
end Facts
