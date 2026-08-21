import LowerBounds.AC0_GapMCSP

set_option linter.deprecated false

namespace Pnp3
namespace Tests

open LowerBounds
open Models

example (p) : GapPartialMCSP_not_in_AC0 p := gapPartialMCSP_not_in_AC0 p

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

example {p : GapPartialMCSPParams}
    (params : SmallAC0ParamsPartial p)
    (easy : AC0EasyFamilyDataPartial params.ac0) : False :=
  false_of_smallAC0Params_and_easyFamilyData params easy

example {p : GapPartialMCSPParams}
    (params : SmallAC0ParamsPartial p)
    {F : Core.Family params.ac0.n}
    (hF : ThirdPartyFacts.AC0FamilyWitnessProp params.ac0 F)
    (hCard : Nat.pow 2 (Nat.pow 2 params.ac0.n) ≤ F.toFinset.card) : False :=
  false_of_smallAC0Params_and_large_AC0Family params hF hCard

example (p : GapPartialMCSPParams)
    (package : SmallAC0Solver_Partial p) : False :=
  false_of_enrichedSmallAC0PackagePartial p package

example (p : GapPartialMCSPParams) :
    EnrichedSmallAC0PackagePartialInconsistent p :=
  not_exists_enrichedSmallAC0PackagePartial p

end Tests
end Pnp3
