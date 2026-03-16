import Magnification.AC0AtlasBridge

/-!
  pnp3/Magnification/AC0ApproxFamilyBridge.lean

  Direct contradiction-facing bridge from source-side semantic switching data
  to the existing counting endpoint in `Counting.Atlas_to_LB_Core`.

  This module packages the family-level route that is currently the shortest
  path from source semantics to contradiction:
  produce one source-linked scenario budget together with one finite family `Y`
  that already lies in a common `ApproxClass` and is larger than the counting
  capacity bound for that class.

  Compared to the singleton small-mismatch route in `AC0AtlasBridge`, this
  route does not ask for a polylog-small exact mismatch set. Instead it targets
  the already formalized contradiction theorem `Counting.incompatibility`
  directly.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/--
Provenance-aware family-level source package for the direct `ApproxClass`
counting contradiction.

The source theorem is asked to produce one scenario budget together with one
finite family `Y` of Boolean functions that all lie in the same `ApproxClass`,
and whose cardinality already exceeds the counting capacity bound for that
dictionary/union budget/error tuple.
-/
structure SemanticSwitchingApproxFamilyPackagePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  pack : AC0AtlasBridge.SemanticSwitchingScenarioBudgetPartial hFormula
  Y : Finset (Core.BitVec pack.cert.ac0.n → Bool)
  hApprox :
    ∀ g ∈ Y,
      g ∈ Counting.ApproxClass
        (R := pack.pack.scenario.atlas.dict)
        (k := pack.pack.scenario.k)
        (ε := pack.pack.scenario.atlas.epsilon)
  hLarge :
    Counting.capacityBound
        (Counting.dictLen pack.pack.scenario.atlas.dict)
        pack.pack.scenario.k
        (Nat.pow 2 pack.cert.ac0.n)
        pack.pack.scenario.atlas.epsilon
        pack.pack.epsilon_nonneg
        pack.pack.epsilon_le_half
      < Y.card

/--
Provider-level version of the family-level direct contradiction package.
-/
def SemanticSwitchingApproxFamilyProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (SemanticSwitchingApproxFamilyPackagePartial hFormula)

/--
One family-level source package immediately yields contradiction by the existing
counting endpoint for `ApproxClass`.
-/
theorem contradiction_of_semanticSwitchingApproxFamilyPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingApproxFamilyPackagePartial hFormula) :
    False := by
  classical
  exact
    Counting.incompatibility
      (R := pkg.pack.pack.scenario.atlas.dict)
      (D := Counting.dictLen pkg.pack.pack.scenario.atlas.dict)
      (k := pkg.pack.pack.scenario.k)
      (ε := pkg.pack.pack.scenario.atlas.epsilon)
      (hR := rfl)
      pkg.pack.pack.epsilon_nonneg
      pkg.pack.pack.epsilon_le_half
      pkg.Y
      pkg.hApprox
      pkg.hLarge

/--
If the source layer can produce the family-level `ApproxClass` contradiction
package for a fixed slice, then that slice cannot have a `PpolyFormula`
witness.
-/
theorem no_ppolyFormula_of_semanticSwitchingApproxFamilyProvider
    (hProv : SemanticSwitchingApproxFamilyProviderPartial)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    False := by
  rcases hProv hFormula with ⟨pkg⟩
  exact contradiction_of_semanticSwitchingApproxFamilyPackage pkg

/--
Strict fixed-slice formula separation from the family-level direct
contradiction package.
-/
theorem NP_strict_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider
    (hProv : SemanticSwitchingApproxFamilyProviderPartial)
    {p : GapPartialMCSPParams}
    (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
    ComplexityInterfaces.NP_strict_not_subset_PpolyFormula := by
  refine
    ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra ?_
  intro hAll
  have hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    hAll _ hNPstrict
  exact no_ppolyFormula_of_semanticSwitchingApproxFamilyProvider hProv hFormula

/--
Non-strict fixed-slice formula separation from the family-level direct
contradiction package.
-/
theorem NP_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider
    (hProv : SemanticSwitchingApproxFamilyProviderPartial)
    {p : GapPartialMCSPParams}
    (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
    ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    ComplexityInterfaces.NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula <|
      NP_strict_not_subset_PpolyFormula_of_semanticSwitchingApproxFamilyProvider
        hProv hNPstrict

end Magnification
end Pnp3
