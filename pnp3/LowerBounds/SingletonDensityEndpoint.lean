import LowerBounds.SingletonProvenanceEndpoint

/-!
  pnp3/LowerBounds/SingletonDensityEndpoint.lean

  Density-oriented endpoint layer for the active singleton source route.

  This module packages exactly what the current internal route already provides
  beyond bare `ApproxClass` membership:

  * one source-produced singleton/provenance package,
  * one bounded witness `S` coming from the same atlas scenario,
  * the inherited low-density error bound `errU ≤ ε`,
  * the numeric bound `ε ≤ 1 / (n + 2)`,
  * the natural mismatch testset `T = mismatchSet (coveredB S) f` together with
    its density estimate.

  The module intentionally stops before contradiction. Its purpose is to make
  the next frontier explicit: a new endpoint must consume density-controlled
  singleton provenance directly, without requiring polylog-small mismatch
  cardinality or a large family.
-/

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

/--
Endpoint-facing singleton package with its source-produced bounded witness and
its inherited density bound.
-/
structure SemanticSwitchingSingletonDensityPackagePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  prov : SemanticSwitchingSingletonProvenancePackagePartial hFormula
  S : List (Core.Subcube prov.pack.cert.ac0.n)
  hlen : S.length ≤ prov.pack.k
  hsub : Core.listSubset S prov.pack.scenario.atlas.dict
  herr : Core.errU prov.f S ≤ prov.pack.scenario.atlas.epsilon
  hEpsLeInv : prov.pack.scenario.atlas.epsilon ≤ (1 : Core.Q) / (prov.pack.cert.ac0.n + 2)

/--
The current internal provider realizes the singleton density package directly.
-/
theorem singletonDensityPackage_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty (SemanticSwitchingSingletonDensityPackagePartial hFormula) := by
  classical
  let cert := Magnification.AC0LocalityBridge.semanticSwitchingCertificate_internal hFormula
  let base := LowerBounds.scenarioFromAC0_with_polylog
    cert.ac0 cert.F cert.hFam cert.hpolyW
  let pack : Magnification.AC0AtlasBridge.SemanticSwitchingBoundedAtlasScenarioPartial hFormula := {
    cert := cert
    k := base.1
    scenario := base.2
    family_eq := by
      simpa [base] using
        LowerBounds.scenarioFromAC0_with_polylog_family_eq
          cert.ac0 cert.F cert.hFam cert.hpolyW
  }
  let f : Core.BitVec pack.cert.ac0.n → Bool :=
    fun x => ComplexityInterfaces.FormulaCircuit.eval
      ((Classical.choose hFormula).family (Models.partialInputLen p))
      (ThirdPartyFacts.castBitVec pack.cert.hsame x)
  let prov : SemanticSwitchingSingletonProvenancePackagePartial hFormula := {
    pack := pack
    f := f
    hSingleton := by
      simp [pack, cert, f, Magnification.AC0LocalityBridge.semanticSwitchingCertificate_internal]
      funext x
      rfl
    hk := by
      simpa [pack, base] using
        LowerBounds.scenarioFromAC0_with_polylog_k_eq cert.ac0 cert.F cert.hFam cert.hpolyW
    hEval := by
      intro x
      simp [f]
  }
  rcases singletonProvenance_boundedWitness prov with ⟨S, hlen, hsub, herr⟩
  have hEpsLeInv : prov.pack.scenario.atlas.epsilon ≤ (1 : Core.Q) / (prov.pack.cert.ac0.n + 2) := by
    simpa [prov, pack, base] using
      (LowerBounds.scenarioFromAC0_with_polylog_completeBounds_strong
        cert.ac0 cert.F cert.hFam cert.hpolyW).2.2.2.2
  exact ⟨{
    prov := prov
    S := S
    hlen := hlen
    hsub := hsub
    herr := herr
    hEpsLeInv := hEpsLeInv
  }⟩

/--
The natural mismatch testset attached to the bounded witness of a singleton
 density package.
-/
noncomputable def naturalMismatchTestsetOfSingletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    Finset (Core.BitVec pkg.prov.pack.cert.ac0.n) :=
  Counting.mismatchSet (fun x => Core.coveredB pkg.S x) pkg.prov.f

/--
The natural mismatch testset is always a valid `ApproxOnTestset` witness for
 the packaged singleton function.
-/
theorem approxOnNaturalMismatchTestset_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    pkg.prov.f ∈ Counting.ApproxOnTestset
      (R := pkg.prov.pack.scenario.atlas.dict)
      (k := pkg.prov.pack.k)
      (T := naturalMismatchTestsetOfSingletonDensityPackage pkg) := by
  exact Counting.approxOnTestset_of_mismatchSet pkg.hlen pkg.hsub

/--
`errU ≤ ε` gives a density bound on the natural mismatch testset.
-/
theorem naturalMismatchTestset_density_le_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    ((((naturalMismatchTestsetOfSingletonDensityPackage pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)))
      ≤ pkg.prov.pack.scenario.atlas.epsilon := by
  simpa [naturalMismatchTestsetOfSingletonDensityPackage] using
    Counting.mismatchSet_density_le_of_errU_le pkg.prov.f pkg.S
      pkg.prov.pack.scenario.atlas.epsilon pkg.herr

/--
For the current singleton route, the natural mismatch testset has density at
most `1 / (n + 2)`.
-/
theorem naturalMismatchTestset_density_le_inv_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    ((((naturalMismatchTestsetOfSingletonDensityPackage pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)))
      ≤ (1 : Core.Q) / (pkg.prov.pack.cert.ac0.n + 2) := by
  exact le_trans
    (naturalMismatchTestset_density_le_of_singletonDensityPackage pkg)
    pkg.hEpsLeInv

/--
Nat-crossmul form of the same density control.
-/
theorem naturalMismatchTestset_card_le_inv_mul_pow_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    (((naturalMismatchTestsetOfSingletonDensityPackage pkg).card : Nat) : Core.Q)
      ≤ ((1 : Core.Q) / (pkg.prov.pack.cert.ac0.n + 2)) *
          (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)) := by
  have hCardErr :
      (((naturalMismatchTestsetOfSingletonDensityPackage pkg).card : Nat) : Core.Q)
        ≤ pkg.prov.pack.scenario.atlas.epsilon *
            (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)) := by
    simpa [naturalMismatchTestsetOfSingletonDensityPackage] using
      Counting.mismatchSet_card_le_of_errU_le pkg.prov.f pkg.S
        pkg.prov.pack.scenario.atlas.epsilon pkg.herr
  have hPowNonneg :
      (0 : Core.Q) ≤ (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)) := by
    positivity
  exact le_trans hCardErr <|
    mul_le_mul_of_nonneg_right pkg.hEpsLeInv hPowNonneg

/--
Endpoint-facing corollary: the current internal source line yields one linked
function together with one explicit testset whose approximation guarantee is
tracked only through density, not cardinality.
-/
theorem linked_natural_testset_density_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    pkg.prov.f ∈ Counting.ApproxOnTestset
      (R := pkg.prov.pack.scenario.atlas.dict)
      (k := pkg.prov.pack.k)
      (T := naturalMismatchTestsetOfSingletonDensityPackage pkg) ∧
    ((((naturalMismatchTestsetOfSingletonDensityPackage pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 pkg.prov.pack.cert.ac0.n : Nat) : Core.Q)))
      ≤ (1 : Core.Q) / (pkg.prov.pack.cert.ac0.n + 2) := by
  classical
  intro pkg
  exact ⟨
    approxOnNaturalMismatchTestset_of_singletonDensityPackage pkg,
    naturalMismatchTestset_density_le_inv_of_singletonDensityPackage pkg
  ⟩

/--
If one can additionally prove that the natural singleton testset already has
capacity below `1`, then the existing testset-capacity contradiction theorem
applies immediately.

This theorem intentionally isolates the next missing input on the density
branch. The current repository does not yet prove the hypothesis
`testsetCapacity < 1` for this natural testset.
-/
theorem old_testset_endpoint_of_singletonDensityPackage_of_testsetCapacity_lt_one
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula)
    (hCap :
      LowerBounds.testsetCapacity
          (sc := pkg.prov.pack.scenario)
          (T := naturalMismatchTestsetOfSingletonDensityPackage pkg)
        < 1) :
    False := by
  classical
  let T := naturalMismatchTestsetOfSingletonDensityPackage pkg
  let Y : Finset (Core.BitVec pkg.prov.pack.cert.ac0.n → Bool) := {pkg.prov.f}
  have hSubset : Y ⊆ LowerBounds.familyFinset (sc := pkg.prov.pack.scenario) := by
    intro f hf
    have hfEq : f = pkg.prov.f := by
      simpa [Y] using hf
    have hfF : pkg.prov.f ∈ pkg.prov.pack.cert.F := by
      simpa [pkg.prov.hSingleton]
    have hfSc : pkg.prov.f ∈ pkg.prov.pack.scenario.family := by
      simpa [pkg.prov.pack.family_eq] using hfF
    have hfFin :
        pkg.prov.f ∈ LowerBounds.familyFinset (sc := pkg.prov.pack.scenario) := by
      exact
        (LowerBounds.mem_familyFinset (sc := pkg.prov.pack.scenario)
          (f := pkg.prov.f)).2 hfSc
    simpa [Y, hfEq] using hfFin
  have hApprox :
      ∀ f ∈ Y,
        f ∈ Counting.ApproxOnTestset
          (R := pkg.prov.pack.scenario.atlas.dict)
          (k := pkg.prov.pack.scenario.k)
          (T := T) := by
    intro f hf
    have hfEq : f = pkg.prov.f := by
      simpa [Y] using hf
    rw [hfEq, pkg.prov.hk]
    exact approxOnNaturalMismatchTestset_of_singletonDensityPackage pkg
  have hLarge :
      LowerBounds.testsetCapacity (sc := pkg.prov.pack.scenario) (T := T) < Y.card := by
    simpa [Y, T] using hCap
  exact
    LowerBounds.no_bounded_atlas_on_testset_of_large_family
      (sc := pkg.prov.pack.scenario)
      (T := T)
      (Y := Y)
      hSubset
      hApprox
      hLarge

end LowerBounds
end Pnp3
