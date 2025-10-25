import Proof.Complexity.Interfaces
import Proof.Complexity.PsubsetPpoly

/-!
# External fact `P ⊆ P/poly`

This module exposes the lightweight interface defined in
`Proof/Complexity/Interfaces.lean`.  It imports the constructive bridge
`Proof/Complexity/PsubsetPpoly.lean` so we re-export the actual proof of the
inclusion rather than postulating it as an axiom.  Downstream projects can
depend on the named statement without pulling in any additional
infrastructure.
-/

namespace Facts
namespace PsubsetPpoly

export Complexity (Bitstring Language P Ppoly)
export Proof (complexity_P_subset_Ppoly)

end PsubsetPpoly
end Facts
