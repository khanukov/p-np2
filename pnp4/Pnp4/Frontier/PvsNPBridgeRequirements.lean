import Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG

namespace Pnp4
namespace Frontier

open AlgorithmsToLowerBounds

/--
Restricted lower-bound milestone currently targeted by the pnp4 MCSP/coin
track.

This records an `AC0[p]` exclusion only.  It deliberately carries no
`PpolyDAG` lower bound and therefore is not, by itself, a `P != NP` source.
-/
structure AC0pRestrictedLowerBoundSource where
  model : AC0pFamilyModel
  p : Nat
  hp : Nat.Prime p
  L : BitVecLanguage
  notInAC0p : ¬ InAC0p model p L

/-- The restricted conclusion provided by an `AC0[p]` milestone. -/
theorem AC0pRestrictedLowerBoundSource.restrictedConclusion
    (src : AC0pRestrictedLowerBoundSource) :
    ¬ InAC0p src.model src.p src.L :=
  src.notInAC0p

/--
The honest pnp4-to-`P != NP` source requirement.

The existing final bridge needs an explicit `NP` language with a verified
`PpolyDAG` lower bound.  Restricted lower bounds such as `L notin AC0[p]`
do not discharge this field.
-/
structure PvsNPBridgeRequirement where
  verifiedSource : VerifiedNPDAGLowerBoundSource

/-- A pnp4 bridge requirement feeds the existing final `P != NP` theorem. -/
theorem P_ne_NP_of_pnp4_bridge_requirement
    (req : PvsNPBridgeRequirement) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_verified_source req.verifiedSource

/--
Explicit missing bridge from a restricted milestone to a verified DAG source.

This is the additional mathematical source needed if one wants to turn a pnp4
restricted `AC0[p]` lower bound into the existing final `P != NP` bridge.
-/
structure RestrictedToVerifiedDAGBridge
    (_restricted : AC0pRestrictedLowerBoundSource) where
  verifiedSource : VerifiedNPDAGLowerBoundSource

/--
A restricted pnp4 lower bound yields `P != NP` only after an explicit bridge to
a verified `NP` language lower bound against `PpolyDAG`.
-/
theorem P_ne_NP_of_restricted_source_and_dag_bridge
    (restricted : AC0pRestrictedLowerBoundSource)
    (bridge : RestrictedToVerifiedDAGBridge restricted) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_verified_source bridge.verifiedSource

end Frontier
end Pnp4
