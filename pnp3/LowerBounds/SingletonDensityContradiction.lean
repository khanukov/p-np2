import LowerBounds.SingletonDensityEndpoint

/-!
  pnp3/LowerBounds/SingletonDensityContradiction.lean

  Formula-free contradiction staging layer for singleton density data.

  The previous module `SingletonDensityEndpoint` packages the active internal
  formula route. This file factors out the part that is genuinely independent
  of formula-specific source constructors:

  * one bounded atlas scenario `sc`,
  * one distinguished function `f ∈ sc.family`,
  * one bounded witness `S`,
  * one density/error bound `errU f S ≤ sc.atlas.epsilon`,
  * one numerical estimate `sc.atlas.epsilon ≤ 1 / (n + 2)`.

  The purpose of this module is to make the next positive frontier explicit in
  a DAG-robust form. The raw scenario-level payload is intentionally weak
  enough to be consistent on trivial examples, so any future contradiction
  theorem must consume a stronger, still formula-free, linked variant rather
  than the formula-specific packaging of the current source line.
-/

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

/--
Formula-free singleton density payload over an arbitrary bounded atlas
scenario.
-/
structure AbstractSingletonDensityPayload (n : Nat) where
  sc : BoundedAtlasScenario n
  f : Core.BitVec n → Bool
  hf : f ∈ sc.family
  S : List (Core.Subcube n)
  hlen : S.length ≤ sc.k
  hsub : Core.listSubset S sc.atlas.dict
  herr : Core.errU f S ≤ sc.atlas.epsilon
  hEpsLeInv : sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2)

/--
The raw abstract singleton-density payload is consistent: the empty dictionary
with the constant-zero function satisfies all fields.
-/
theorem nonempty_abstractSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractSingletonDensityPayload n) := by
  classical
  let f : Core.BitVec n → Bool := fun _ => false
  let A : Core.Atlas n := { dict := [], epsilon := 0 }
  let sc : BoundedAtlasScenario n := {
    atlas := A
    family := [f]
    k := 0
    hε0 := by norm_num
    hε1 := by norm_num
    works := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
    bounded := by
      intro g hg
      have hgEq : g = f := by
        simpa [f] using hg
      subst hgEq
      refine ⟨[], by simp, Core.listSubset_nil _, ?_⟩
      simpa [A, f] using (Core.errU_false_nil (n := n))
  }
  have hInv :
      sc.atlas.epsilon ≤ (1 : Core.Q) / (n + 2) := by
    have hNonneg : (0 : Core.Q) ≤ (1 : Core.Q) / (n + 2) := by
      positivity
    simpa [sc, A] using hNonneg
  exact ⟨{
    sc := sc
    f := f
    hf := by simp [sc, f]
    S := []
    hlen := by simp [sc]
    hsub := Core.listSubset_nil _
    herr := by simpa [sc, A, f] using (Core.errU_false_nil (n := n))
    hEpsLeInv := hInv
  }⟩

/--
Formula-free strengthening of the abstract singleton-density payload by an
explicit link to some target Boolean function.
-/
structure AbstractLinkedSingletonDensityPayload (n : Nat) where
  base : AbstractSingletonDensityPayload n
  target : Core.BitVec n → Bool
  hLink : base.f = target

/--
The current concrete singleton-density package factors through the abstract
scenario-level payload.
-/
def abstractSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractSingletonDensityPayload pkg.prov.pack.cert.ac0.n where
  sc := pkg.prov.pack.scenario
  f := pkg.prov.f
  hf := by
    have hfF : pkg.prov.f ∈ pkg.prov.pack.cert.F := by
      simpa [pkg.prov.hSingleton]
    simpa [pkg.prov.pack.family_eq] using hfF
  S := pkg.S
  hlen := by
    rw [pkg.prov.hk]
    exact pkg.hlen
  hsub := pkg.hsub
  herr := pkg.herr
  hEpsLeInv := pkg.hEpsLeInv

/--
The current singleton-density package also yields the minimally strengthened
formula-free payload: an abstract singleton-density object together with an
explicit target-link witness.
-/
noncomputable def abstractLinkedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractLinkedSingletonDensityPayload pkg.prov.pack.cert.ac0.n where
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  target := fun x =>
    ComplexityInterfaces.FormulaCircuit.eval
      ((Classical.choose hFormula).family (Models.partialInputLen p))
      (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)
  hLink := by
    funext x
    exact pkg.prov.hEval x

/--
The natural mismatch testset attached to an abstract singleton-density payload.
-/
noncomputable def naturalMismatchTestsetOfAbstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    Finset (Core.BitVec n) :=
  Counting.mismatchSet (fun x => Core.coveredB pkg.S x) pkg.f

/--
The natural mismatch testset always witnesses `ApproxOnTestset`.
-/
theorem approxOnNaturalMismatchTestset_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    pkg.f ∈ Counting.ApproxOnTestset
      (R := pkg.sc.atlas.dict)
      (k := pkg.sc.k)
      (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg) := by
  exact Counting.approxOnTestset_of_mismatchSet pkg.hlen pkg.hsub

/--
`errU ≤ ε` gives the density bound on the natural mismatch testset already at
the abstract scenario level.
-/
theorem naturalMismatchTestset_density_le_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ((((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 n : Nat) : Core.Q)))
      ≤ pkg.sc.atlas.epsilon := by
  simpa [naturalMismatchTestsetOfAbstractSingletonDensityPayload] using
    Counting.mismatchSet_density_le_of_errU_le pkg.f pkg.S
      pkg.sc.atlas.epsilon pkg.herr

/--
For an abstract singleton-density payload, the natural mismatch testset has
density at most `1 / (n + 2)`.
-/
theorem naturalMismatchTestset_density_le_inv_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ((((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q) /
      (((Nat.pow 2 n : Nat) : Core.Q)))
      ≤ (1 : Core.Q) / (n + 2) := by
  exact le_trans
    (naturalMismatchTestset_density_le_of_abstractSingletonDensityPayload pkg)
    pkg.hEpsLeInv

/--
Nat-crossmul form of the same abstract density bound.
-/
theorem naturalMismatchTestset_card_le_inv_mul_pow_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    (((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q)
      ≤ ((1 : Core.Q) / (n + 2)) * (((Nat.pow 2 n : Nat) : Core.Q)) := by
  have hCardErr :
      (((naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg).card : Nat) : Core.Q)
        ≤ pkg.sc.atlas.epsilon * (((Nat.pow 2 n : Nat) : Core.Q)) := by
    simpa [naturalMismatchTestsetOfAbstractSingletonDensityPayload] using
      Counting.mismatchSet_card_le_of_errU_le pkg.f pkg.S
        pkg.sc.atlas.epsilon pkg.herr
  have hPowNonneg : (0 : Core.Q) ≤ (((Nat.pow 2 n : Nat) : Core.Q)) := by
    positivity
  exact le_trans hCardErr <|
    mul_le_mul_of_nonneg_right pkg.hEpsLeInv hPowNonneg

/--
If one had `testsetCapacity < 1`, the old testset-capacity contradiction would
already follow from the abstract payload alone.
-/
theorem old_testset_endpoint_of_abstractSingletonDensityPayload_of_testsetCapacity_lt_one
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n)
    (hCap :
      LowerBounds.testsetCapacity
          (sc := pkg.sc)
          (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)
        < 1) :
    False := by
  classical
  let T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg
  let Y : Finset (Core.BitVec n → Bool) := {pkg.f}
  have hSubset : Y ⊆ LowerBounds.familyFinset (sc := pkg.sc) := by
    intro f hf
    have hfEq : f = pkg.f := by
      simpa [Y] using hf
    have hfFin : pkg.f ∈ LowerBounds.familyFinset (sc := pkg.sc) := by
      exact (LowerBounds.mem_familyFinset (sc := pkg.sc) (f := pkg.f)).2 pkg.hf
    simpa [Y, hfEq] using hfFin
  have hApprox :
      ∀ f ∈ Y,
        f ∈ Counting.ApproxOnTestset
          (R := pkg.sc.atlas.dict)
          (k := pkg.sc.k)
          (T := T) := by
    intro f hf
    have hfEq : f = pkg.f := by
      simpa [Y] using hf
    rw [hfEq]
    exact approxOnNaturalMismatchTestset_of_abstractSingletonDensityPayload pkg
  have hLarge :
      LowerBounds.testsetCapacity (sc := pkg.sc) (T := T) < Y.card := by
    simpa [Y, T] using hCap
  exact
    LowerBounds.no_bounded_atlas_on_testset_of_large_family
      (sc := pkg.sc)
      (T := T)
      (Y := Y)
      hSubset
      hApprox
      hLarge

/--
But the old testset-capacity hypothesis is impossible already for the abstract
payload, because it is impossible for every bounded atlas scenario.
-/
theorem naturalMismatchTestset_not_testsetCapacity_lt_one_of_abstractSingletonDensityPayload
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    ¬ LowerBounds.testsetCapacity
          (sc := pkg.sc)
          (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)
        < 1 := by
  exact
    LowerBounds.not_testsetCapacity_lt_one
      (sc := pkg.sc)
      (T := naturalMismatchTestsetOfAbstractSingletonDensityPayload pkg)

/--
Current internal route reaches the abstract singleton-density payload.
-/
theorem abstractSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (AbstractSingletonDensityPayload pkg.prov.pack.cert.ac0.n) := by
  classical
  intro pkg
  exact ⟨abstractSingletonDensityPayload_of_singletonDensityPackage pkg⟩

/--
Current internal route reaches the minimally strengthened abstract linked
singleton-density payload as well.
-/
theorem abstractLinkedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (AbstractLinkedSingletonDensityPayload pkg.prov.pack.cert.ac0.n) := by
  classical
  intro pkg
  exact ⟨abstractLinkedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

end LowerBounds
end Pnp3
