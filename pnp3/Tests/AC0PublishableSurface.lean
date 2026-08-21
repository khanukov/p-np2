import LowerBounds.AC0_GapMCSP

namespace Pnp3
namespace Tests

open LowerBounds
open Models

-- These checks pin the historical enriched-package aliases only.  Their
-- standard-looking names are not standard AC0 claims.

-- Deprecated compatibility declarations from `AC0_GapMCSP.lean`.
set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_in_AC0 p ↔ EnrichedSmallAC0PackagePartialExists p :=
  Iff.rfl

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p ↔
      EnrichedSmallAC0PackagePartialInconsistent p :=
  Iff.rfl

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  gapPartialMCSP_no_semantic_AC0_solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False :=
  gapPartialMCSP_no_syntactic_AC0_solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False :=
  gapPartialMCSP_no_constructive_AC0_solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p :=
  gapPartialMCSP_not_in_AC0 p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p :=
  gapPartialMCSP_notInSmallAC0_of_not_in_AC0 p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p ↔ GapPartialMCSP_NotInSmallAC0 p :=
  gapPartialMCSP_not_in_AC0_iff_notInSmallAC0 p

-- Deprecated compatibility declarations from `AC0_GapMCSP_Final.lean`.
set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p ↔
      EnrichedSmallAC0PackagePartialInconsistent p :=
  Iff.rfl

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  gapPartialMCSP_noSmallAC0Solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False :=
  gapPartialMCSP_noSyntacticSmallAC0Solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False :=
  gapPartialMCSP_noConstructiveSmallAC0Solver p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p :=
  gapPartialMCSP_notInSmallAC0 p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : SmallAC0Solver_Partial_Syntactic p, True :=
  gapPartialMCSP_notInSmallAC0_syntactic p

set_option linter.deprecated false in
example (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : ConstructiveSmallAC0Solver_Partial p, True :=
  gapPartialMCSP_notInSmallAC0_constructive p

-- Deprecated compatibility declaration from `AntiChecker_Partial.lean`.
set_option linter.deprecated false in
example {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p)
    {F : Core.Family solver.params.ac0.n}
    (hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0 F)
    (hCard : Nat.pow 2 (Nat.pow 2 solver.params.ac0.n) ≤ F.toFinset.card) :
    False :=
  noSmallAC0Solver_partial_of_family_card solver hF hCard

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
