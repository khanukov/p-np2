import Proof.Simulation.Configuration
import Proof.Simulation.Core
import Proof.Simulation.Bounds

/-!
Bridging module that re-exports the layered simulation development.  Downstream
clients can simply import `Proof.Simulation` to access the configuration
encoding, the straight-line simulation core, and the final gate-count bounds.
-/

namespace Proof

/-!
The namespace is intentionally left empty: all re-exported declarations live in
submodules.  The empty namespace documents that this file exists purely for
organisation and does not introduce additional theory.
-/

end Proof
