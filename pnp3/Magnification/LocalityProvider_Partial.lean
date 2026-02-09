import Magnification.Facts_Magnification_Partial
import ThirdPartyFacts.PpolyFormula

namespace Pnp3
namespace Magnification

open Models

/--
Default locality provider used by the current pipeline.
At the moment it is instantiated from `ThirdPartyFacts.ppolyStructured_circuit_locality`;
the rest of the magnification bridge only depends on this provider interface.
-/
noncomputable def defaultStructuredLocalityProviderPartial :
    StructuredLocalityProviderPartial := by
  intro p hPpolyStructured
  exact
    ThirdPartyFacts.ppolyStructured_circuit_locality
      (Models.gapPartialMCSP_Language p) hPpolyStructured (Models.partialInputLen p)

end Magnification
end Pnp3
