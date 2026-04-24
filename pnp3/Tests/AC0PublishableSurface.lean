import LowerBounds.AC0_GapMCSP

namespace Pnp3
namespace Tests

open LowerBounds
open Models

example (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p :=
  gapPartialMCSP_not_in_AC0 p

example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  gapPartialMCSP_no_semantic_AC0_solver p

example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False :=
  gapPartialMCSP_no_syntactic_AC0_solver p

example (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False :=
  gapPartialMCSP_no_constructive_AC0_solver p

example (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p ↔ GapPartialMCSP_NotInSmallAC0 p :=
  gapPartialMCSP_not_in_AC0_iff_notInSmallAC0 p

end Tests
end Pnp3
