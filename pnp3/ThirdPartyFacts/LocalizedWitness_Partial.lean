import LowerBounds.LB_GeneralFromLocal_Partial

/-!
  pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean

  Explicit external scaffold for the remaining "localized witness" gap in the
  partial magnification chain.

  This file intentionally contains one named axiom, so the unresolved external
  input is centralized and auditable.
-/

namespace Pnp3
namespace ThirdPartyFacts

/--
  External localized witness package for the partial general→local bridge.

  For each Partial-MCSP parameter set `p`, this supplies the narrow witness
  contract consumed by `LB_GeneralFromLocal_partial`.
-/
axiom localizedFamilyWitness_partial
  (p : Models.GapPartialMCSPParams) :
  LowerBounds.LocalizedFamilyWitnessHypothesis_partial p

end ThirdPartyFacts
end Pnp3
