import Pnp4.Frontier.PvsNPBridgeRequirements

namespace Pnp4
namespace Frontier

open AlgorithmsToLowerBounds

/--
Repository-local `P/poly` endpoint used by the pnp4 frontier.

The current formal final bridge represents non-uniform polynomial-size circuits
by `PpolyDAG`, so this abbreviation intentionally names the endpoint while
reusing the already verified DAG interface.
-/
abbrev NP_not_subset_Ppoly : Prop :=
  Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG

/--
The existing final bridge from the repository-local `P/poly` endpoint to
`P != NP`.
-/
theorem P_ne_NP_of_NP_not_subset_Ppoly
    (hNP : NP_not_subset_Ppoly) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  exact Pnp3.ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
    hNP
    Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal

/--
Mainline pnp4 source package for compression/search-MCSP magnification.

`weakLowerBound` is the concrete weak lower-bound target, for example a
search-MCSP or resource-bounded-compression lower bound.  The final field is the
published/theorem-facing magnification step: from that weak lower bound one
must produce a verified `NP` language lower bound against `PpolyDAG`.

This is intentionally stronger than an `AC0[p]` restricted milestone and is the
kind of source that can feed the final `P != NP` bridge.
-/
structure SearchMCSPWeakLowerBound where
  weakLowerBound : Prop
  weakLowerBoundProof : weakLowerBound
  magnifiesToVerifiedDAGSource :
    weakLowerBound → VerifiedNPDAGLowerBoundSource

/-- Extract the verified DAG lower-bound source from a magnification package. -/
def SearchMCSPWeakLowerBound.verifiedSource
    (src : SearchMCSPWeakLowerBound) :
    VerifiedNPDAGLowerBoundSource :=
  src.magnifiesToVerifiedDAGSource src.weakLowerBoundProof

/--
Compression/search-MCSP magnification endpoint: a fully discharged weak
lower-bound package yields `NP not_subset P/poly` in the repository-local
`PpolyDAG` sense.
-/
theorem NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound
    (src : SearchMCSPWeakLowerBound) :
    NP_not_subset_Ppoly :=
  NP_not_subset_PpolyDAG_of_verified_source src.verifiedSource

/--
Final consequence of the compression/search-MCSP magnification mainline.

This theorem is deliberately not available from a restricted `AC0[p]` source
alone; it requires a magnification package that reaches `PpolyDAG`.
-/
theorem P_ne_NP_of_searchMCSPWeakLowerBound
    (src : SearchMCSPWeakLowerBound) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_NP_not_subset_Ppoly
    (NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound src)

/--
What counts as mainline pnp4 progress toward `P != NP`: either a direct
verified DAG source, or a compression/search-MCSP magnification package that
produces one.
-/
structure PvsNPMainlineProgress where
  verifiedSource : VerifiedNPDAGLowerBoundSource

/-- Direct final consequence of a mainline progress package. -/
theorem P_ne_NP_of_mainlineProgress
    (progress : PvsNPMainlineProgress) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_verified_source progress.verifiedSource

/-- A search-MCSP magnification source is accepted mainline progress. -/
def PvsNPMainlineProgress.of_searchMCSPWeakLowerBound
    (src : SearchMCSPWeakLowerBound) :
    PvsNPMainlineProgress where
  verifiedSource := src.verifiedSource

end Frontier
end Pnp4
