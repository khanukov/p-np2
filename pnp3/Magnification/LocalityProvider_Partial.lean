import Magnification.Facts_Magnification_Partial

namespace Pnp3
namespace Magnification

/--
The strict structured interface (`PpolyFormula`) has no built-in default
provider in the current tree.  Downstream theorems therefore keep locality as
an explicit hypothesis.
-/
def hasDefaultStructuredLocalityProviderPartial : Prop := False

end Magnification
end Pnp3
