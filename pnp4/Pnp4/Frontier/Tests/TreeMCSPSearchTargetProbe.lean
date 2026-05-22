import Pnp4.Frontier.Tests.TreeCircuitWitnessCodecProbe
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter

namespace Pnp4
namespace Frontier
namespace Tests

/--
Staging threshold schedule for the tree-MCSP search-target pin.

This is intentionally simple for L0 target pinning and does not claim to be
an optimized or research-final threshold.
-/
def stagingTreeThreshold : Nat → Nat :=
  fun n => n + 1

/--
Staging per-output-bit solver size schedule for the target pin.

Chosen as an explicit weak polynomial bound for the L0 target surface.
-/
def stagingSolverSizeBound : Nat → Nat :=
  fun n => n ^ 2 + 1

/--
Staging witness encoding inherited from the finite-index tree-circuit codec.

This encoding is a staging artifact (finite-index/one-hot style), not an
optimized serialization claim.
-/
noncomputable def stagingTreeWitnessEncoding :
    TreeMCSPSearchWitnessEncoding stagingTreeThreshold :=
  finiteIndexTreeMCSPSearchWitnessEncoding stagingTreeThreshold

/--
Pinned concrete staging SearchMCSP weak-circuit target.

No lower-bound theorem is proved here; this only pins the explicit target
object required for subsequent `hWeak` feasibility work.
-/
noncomputable def stagingTreeSearchTarget :
    SearchMCSPWeakCircuitLowerBoundTarget :=
  treeMCSPSearchWeakLowerBoundTarget
    stagingTreeThreshold
    stagingTreeWitnessEncoding
    Pnp4.Frontier.ContractExpansion.C_DAG
    stagingSolverSizeBound

end Tests
end Frontier
end Pnp4
