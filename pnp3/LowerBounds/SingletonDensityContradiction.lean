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
  theorem must consume a stronger formula-free target. The intermediate
  `AbstractLinkedSingletonDensityPayload` remains available as a compatibility
  wrapper, but it is too weak by itself because its target can be chosen to be
  the distinguished function itself. Even an externally targeted payload is
  still too weak when the target is arbitrary; the first semantically fixed
  frontier is therefore the gap-slice-targeted payload introduced below.
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
Compatibility wrapper around the abstract singleton-density payload with an
explicit target field. This is not yet a meaningful positive frontier, because
`target` can always be chosen to be `base.f`.
-/
structure AbstractLinkedSingletonDensityPayload (n : Nat) where
  base : AbstractSingletonDensityPayload n
  target : Core.BitVec n → Bool
  hLink : base.f = target

/--
The compatibility wrapper is vacuous: any abstract singleton-density payload
trivially yields a linked payload by choosing `target := f`.
-/
def abstractLinkedSingletonDensityPayload_of_abstract
    {n : Nat}
    (pkg : AbstractSingletonDensityPayload n) :
    AbstractLinkedSingletonDensityPayload n where
  base := pkg
  target := pkg.f
  hLink := rfl

/--
Consequently, the current linked wrapper is itself consistent on a trivial
scenario.
-/
theorem nonempty_abstractLinkedSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractLinkedSingletonDensityPayload n) := by
  rcases nonempty_abstractSingletonDensityPayload_false n with ⟨pkg⟩
  exact ⟨abstractLinkedSingletonDensityPayload_of_abstract pkg⟩

/--
Externally targeted abstract singleton-density payload. Unlike the compatibility
wrapper above, this object is parameterized by a fixed target supplied from
outside the payload itself.
-/
structure AbstractTargetedSingletonDensityPayload
    (n : Nat)
    (target : Core.BitVec n → Bool) where
  base : AbstractSingletonDensityPayload n
  hLink : base.f = target

/--
Even the externally targeted payload is consistent for trivial targets such as
the constant-zero function.
-/
theorem nonempty_abstractTargetedSingletonDensityPayload_false
    (n : Nat) :
    Nonempty (AbstractTargetedSingletonDensityPayload n (fun _ => false)) := by
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
  refine ⟨{
    base := {
      sc := sc
      f := f
      hf := by simp [sc, f]
      S := []
      hlen := by simp [sc]
      hsub := Core.listSubset_nil _
      herr := by simpa [sc, A, f] using (Core.errU_false_nil (n := n))
      hEpsLeInv := hInv
    }
    hLink := by
      funext x
      rfl
  }⟩

/--
Semantically fixed singleton-density payload for the concrete gap-PartialMCSP
slice. This is the first non-vacuous target that does not let the consumer
choose the target function internally.
-/
structure AbstractGapTargetedSingletonDensityPayload
    (p : GapPartialMCSPParams) where
  n : Nat
  hsame : n = Models.partialInputLen p
  base : AbstractSingletonDensityPayload n
  hLink :
    base.f = fun x =>
      Models.gapPartialMCSP_Language p (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec hsame x)

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
The current singleton-density package also yields the externally targeted
abstract payload, with the target fixed by the formula witness.
-/
noncomputable def abstractTargetedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractTargetedSingletonDensityPayload
      pkg.prov.pack.cert.ac0.n
      (fun x =>
        ComplexityInterfaces.FormulaCircuit.eval
          ((Classical.choose hFormula).family (Models.partialInputLen p))
          (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)) where
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  hLink := by
    funext x
    exact pkg.prov.hEval x

/--
Current internal formula route also reaches the semantically fixed gap-target
payload.
-/
noncomputable def abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonDensityPackagePartial hFormula) :
    AbstractGapTargetedSingletonDensityPayload p where
  n := pkg.prov.pack.cert.ac0.n
  hsame := pkg.prov.pack.cert.hsame
  base := abstractSingletonDensityPayload_of_singletonDensityPackage pkg
  hLink := by
    funext x
    have hEval := pkg.prov.hEval x
    have hCorrect :=
      (Classical.choose hFormula).correct
        (Models.partialInputLen p)
        (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x)
    exact hEval.trans hCorrect

/--
Current internal formula route also reaches the semantically fixed gap-target
payload.
-/
theorem abstractGapTargetedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty (AbstractGapTargetedSingletonDensityPayload p) := by
  classical
  let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
  exact ⟨abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

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

/--
Current internal route also reaches the externally targeted abstract payload.
-/
theorem abstractTargetedSingletonDensityPayload_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let pkg := Classical.choice (singletonDensityPackage_of_internal_provider hFormula)
    Nonempty (
      AbstractTargetedSingletonDensityPayload
        pkg.prov.pack.cert.ac0.n
        (fun x =>
          ComplexityInterfaces.FormulaCircuit.eval
            ((Classical.choose hFormula).family (Models.partialInputLen p))
            (ThirdPartyFacts.castBitVec pkg.prov.pack.cert.hsame x))) := by
  classical
  intro pkg
  exact ⟨abstractTargetedSingletonDensityPayload_of_singletonDensityPackage pkg⟩

end LowerBounds
end Pnp3
