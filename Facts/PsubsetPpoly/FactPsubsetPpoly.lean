import Proof.Complexity.Interfaces

/-!
# External fact `P ⊆ P/poly`

This module exposes the lightweight interface defined in
`Proof/Complexity/Interfaces.lean`.  It merely re-exports the theorem
recording the inclusion so that downstream projects can depend on the
named statement without pulling in any additional infrastructure.
-/

namespace Facts
namespace PsubsetPpoly

export Complexity (Bitstring Language P Ppoly)
export Proof (complexity_P_subset_Ppoly)

end PsubsetPpoly
end Facts
