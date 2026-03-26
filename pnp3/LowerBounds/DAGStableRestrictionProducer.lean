import Complexity.Promise
import Counting.Count_EasyFuncs
import LowerBounds.AcceptedFamilyBarrier
import LowerBounds.SingletonDensityContradiction
import LowerBounds.AsymptoticDAGBarrier
import ThirdPartyFacts.PartialLocalityLift

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces
open Complexity

/--
A strictly DAG-native producer certificate for the Route-B stable-restriction
frontier.

This structure intentionally avoids formula/certificate bridge assumptions.  It
records only the mathematically minimal data that the DAG source side must
provide for a fixed DAG witness `hDag`:

1. a concrete restriction `r`,
2. a half-table alive bound,
3. global stability of the fixed gap target under `r.apply`.

Once this certificate is available, the conversion into the canonical
`stableRestrictionGoal_of_abstractGapTargetedPayload` is purely mechanical.
-/
structure DAGStableRestrictionCertificate
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) where
  /-- Restriction candidate produced by the DAG-side route. -/
  r : Facts.LocalityLift.Restriction (Models.partialInputLen p)
  /-- Required half-table alive bound. -/
  hAliveSmall : r.alive.card ≤ Models.Partial.tableLen p.n / 2
  /--
  Global overwrite-invariance for the semantically fixed target language.

  This is the exact invariant required by the consumer stack; unlike the old
  singleton selector facts, it is not pointwise/one-sided.
  -/
  hStableGap :
    ∀ x : Core.BitVec (Models.partialInputLen p),
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) (r.apply x) =
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) x

/--
Convert a DAG-native Route-B certificate into the canonical stable-restriction
producer goal for the corresponding canonical DAG payload.
-/
theorem stableRestrictionGoal_of_dagStableRestrictionCertificate
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p))
    (cert : DAGStableRestrictionCertificate hDag) :
    stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag) := by
  refine ⟨cert.r, cert.hAliveSmall, ?_⟩
  intro x
  -- The payload is linked extensionally to the fixed gap target; rewrite both
  -- sides through that semantic link and use the certificate stability field.
  have hAtApply :
      (dagCanonicalPayload hDag).base.f
          (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm
            (cert.r.apply x)) =
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) (cert.r.apply x) := by
    simpa using congrArg
      (fun g => g (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm
        (cert.r.apply x)))
      (dagCanonicalPayload hDag).hLink
  have hAtX :
      (dagCanonicalPayload hDag).base.f
          (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm x) =
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := by
    simpa using congrArg
      (fun g => g (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm x))
      (dagCanonicalPayload hDag).hLink
  calc
    (dagCanonicalPayload hDag).base.f
        (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm (cert.r.apply x))
        = Models.gapPartialMCSP_Language p (Models.partialInputLen p) (cert.r.apply x) := hAtApply
    _ = Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := cert.hStableGap x
    _ = (dagCanonicalPayload hDag).base.f
          (ThirdPartyFacts.castBitVec (dagCanonicalPayload hDag).hsame.symm x) := hAtX.symm

/--
Provider form of the new DAG-native source certificate.

This is the Route-B source-side target: each DAG witness must supply one
`DAGStableRestrictionCertificate`.
-/
abbrev dagStableRestrictionCertificateProvider
    (p : GapPartialMCSPParams) : Type :=
  ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
    DAGStableRestrictionCertificate hDag

/--
A DAG-native certificate provider is sufficient to build the canonical Route-B
producer (`dag_stableRestriction_producer`).
-/
theorem dag_stableRestriction_producer_of_certificateProvider
    {p : GapPartialMCSPParams}
    (hCert : dagStableRestrictionCertificateProvider p) :
    dag_stableRestriction_producer p := by
  intro hDag
  exact stableRestrictionGoal_of_dagStableRestrictionCertificate hDag (hCert hDag)

/--
Route-B source package phrased in terms of a DAG-side locality invariant.

Compared with `DAGStableRestrictionCertificate`, this is a slightly more
"mathematical" source contract: instead of postulating overwrite-invariance
`f (r.apply x) = f x` directly, it asks for a coordinate-locality statement on
the alive set of `r`.

This matches the intended DAG-side workflow:
1. extract an alive set + restriction from DAG semantics;
2. prove the target is determined by alive coordinates;
3. convert this locality statement to a stable-restriction certificate.
-/
structure DAGStableRestrictionInvariantPackage
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) where
  /-- Restriction candidate from DAG-side analysis. -/
  r : Facts.LocalityLift.Restriction (Models.partialInputLen p)
  /-- Consumer-side half-table bound. -/
  hAliveSmall : r.alive.card ≤ Models.Partial.tableLen p.n / 2
  /--
  DAG-side locality invariant: the fixed gap target depends only on coordinates
  in `r.alive`.
  -/
  hLocalInvariant :
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ r.alive, x i = y i) →
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) y

/--
Convert DAG-side locality invariants into a Route-B certificate.

The key step is canonical: `r.apply x` and `x` agree on all alive coordinates
by `Restriction.apply_alive`, so the locality invariant immediately yields the
global overwrite-invariance required by `DAGStableRestrictionCertificate`.
-/
def dagStableRestrictionCertificate_of_localInvariant
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p))
    (inv : DAGStableRestrictionInvariantPackage hDag) :
    DAGStableRestrictionCertificate hDag := by
  refine
    { r := inv.r
      hAliveSmall := inv.hAliveSmall
      hStableGap := ?_ }
  intro x
  have hAgree :
      ∀ i ∈ inv.r.alive, (inv.r.apply x) i = x i := by
    intro i hi
    simpa using Facts.LocalityLift.Restriction.apply_alive inv.r x hi
  exact inv.hLocalInvariant (inv.r.apply x) x hAgree

/--
Provider form of the DAG-side locality invariant package.
-/
abbrev dagStableRestrictionInvariantProvider
    (p : GapPartialMCSPParams) : Type :=
  ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
    DAGStableRestrictionInvariantPackage hDag

/--
Main Route-B source bridge requested by the DAG-side plan:

`∀ hDag, DAG-side locality invariants` ⟹
`dagStableRestrictionCertificateProvider` ⟹
`dag_stableRestriction_producer`.
-/
def dagStableRestrictionCertificateProvider_of_invariantProvider
    {p : GapPartialMCSPParams}
    (hInv : dagStableRestrictionInvariantProvider p) :
    dagStableRestrictionCertificateProvider p := by
  intro hDag
  exact dagStableRestrictionCertificate_of_localInvariant hDag (hInv hDag)

/--
Corollary form landing directly at the existing Route-B producer alias.
-/
theorem dag_stableRestriction_producer_of_invariantProvider
    {p : GapPartialMCSPParams}
    (hInv : dagStableRestrictionInvariantProvider p) :
    dag_stableRestriction_producer p := by
  exact dag_stableRestriction_producer_of_certificateProvider
    (dagStableRestrictionCertificateProvider_of_invariantProvider hInv)

/--
TM-witness closure on top of the DAG-native certificate provider.

This theorem is the direct endgame hook for Route B: once the producer side
supplies certificate data for every DAG witness, the existing lower-bound stack
already closes `NP ⊄ PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_of_certificateProvider_TM
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hCert : dagStableRestrictionCertificateProvider p) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM W
    (dag_stableRestriction_producer_of_certificateProvider hCert)

/--
TM-level closure from DAG-side locality invariants.

This is the direct "source-side invariants → strict DAG separation" theorem:
once invariants are available uniformly for each DAG witness, the rest of the
Route-B contradiction stack is already internalized.
-/
theorem NP_not_subset_PpolyDAG_of_invariantProvider_TM
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hInv : dagStableRestrictionInvariantProvider p) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM W
    (dag_stableRestriction_producer_of_invariantProvider hInv)

/--
Quantitative anti-locality payload for the DAG route.

`hSlack` is the corrected counting-style criterion:
the number of coordinates ignored by the restriction (`tableLen - |alive|`)
must be large enough so that the extension cube beats the number of small
circuits (`circuitCountBound` in the current finite-size model).

This is intentionally weaker (and more realistic) than a hard-coded
half-table bound.  It captures the mathematically relevant target discussed in
the DAG barrier notes:

`2^(N - |S|) > M(N, T)`.
-/
structure DAGStableRestrictionSlackPackage
    {p : GapPartialMCSPParams}
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) where
  /-- Restriction candidate from DAG-side analysis. -/
  r : Facts.LocalityLift.Restriction (Models.partialInputLen p)
  /--
  Counting slack: the ignored-coordinate cube is larger than the current
  finite-size upper bound on small circuits.
  -/
  hSlack :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - r.alive.card)
  /--
  DAG-side locality invariant for the fixed target on the alive coordinates.
  -/
  hLocalInvariant :
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ r.alive, x i = y i) →
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) y

/--
Provider form for the slack-based DAG package.
-/
abbrev dagStableRestrictionSlackProvider
    (p : GapPartialMCSPParams) : Type :=
  ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
    DAGStableRestrictionSlackPackage hDag

/--
Slice-indexed (`n,β`) version of the slack provider.

This is the bridge-ready source object: for every slice-parameter pair and for
every DAG witness of the corresponding slice language, we can produce a
`DAGStableRestrictionSlackPackage`.
-/
abbrev dagStableRestrictionSlackProviderOnSlices
    (paramsOf : Nat → Rat → GapPartialMCSPParams) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language (paramsOf n β)),
      DAGStableRestrictionSlackPackage hDag

/--
Bridge from slice-indexed DAG slack packages to the asymptotic barrier module.

The target is language-level slice locality (`SliceLanguageLocalityStatement`)
with explicit counting parameters `T(n,β)` and `M_n(T)`.  Equalities `hT` and
`hM` connect those abstract interfaces to the current concrete finite-size
objects `sNO - 1` and `circuitCountBound`.
-/
theorem sliceLanguageLocality_of_dagSlackProviderOnSlices
    (F : GapSliceFamily)
    (hDagFamily :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hPkg : dagStableRestrictionSlackProviderOnSlices F.paramsOf) :
    SliceLanguageLocalityStatement F := by
  intro n β
  let cert := hPkg n β (hDagFamily n β)
  refine ⟨cert.r.alive, ?_, ?_⟩
  · calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound (F.paramsOf n β).n (F.Tof n β) := by
              simp [F.hM, F.hIndex]
      _ = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
            simp [F.hT]
      _ < 2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - cert.r.alive.card) := cert.hSlack
  · intro x y hAgree
    exact cert.hLocalInvariant x y hAgree

/--
Concrete small-DAG witness on one fixed slice `(p, ε)`.
-/
structure SmallDAGWitnessOnSlice
    (p : GapPartialMCSPParams)
    (SizeBound : Rat → Nat → Prop)
    (ε : Rat) where
  C : DagCircuit (Models.partialInputLen p)
  hSize : SizeBound ε (DagCircuit.size C)
  hCorrect : CorrectOnPromiseSlice C (gapSliceOfParams p)

/--
Generic-solver view of a concrete DAG witness on one fixed slice.

This packages the witness into the existing `SmallGeneralCircuitSolver_Partial`
interface, so the already formalized restriction/shrinkage machinery can be
reused without introducing DAG-specific certificate APIs there.
-/
def generalSolverOfSmallDAGWitnessOnSlice
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    Magnification.SmallGeneralCircuitSolver_Partial p where
  params := {
    params := {
      n := Models.partialInputLen p
      size := DagCircuit.size W.C
      depth := 0
    }
    same_n := rfl
  }
  sem := {
    Carrier := DagCircuit (Models.partialInputLen p)
    eval := fun C x => DagCircuit.eval C x
  }
  witness := W.C
  correct := by
    constructor
    · intro x hx
      exact W.hCorrect.1 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams] using hx)
    · intro x hx
      exact W.hCorrect.2 x (by simpa [GapPartialMCSPPromise, gapSliceOfParams] using hx)

/--
Witness-indexed semantic surviving-cone certificate for the stronger shrinkage
fallback route.

This is the intended semantic intermediate layer between raw DAG semantics and
restriction extraction. It says that the solver induced by `W` is already
determined by one small surviving alive set. A future source theorem may prove
this via forced gates, residual DAGs, or another DAG-specific semantic object;
the current interface deliberately does not commit to which one.
-/
structure SmallDAGWitnessSemanticConeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  r :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  aliveBound : Nat
  hAliveBound : r.alive.card ≤ aliveBound
  hLocal :
    ∀ x y : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      (∀ i ∈ r.alive, x i = y i) →
        ThirdPartyFacts.solverDecideFacts
            (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) x =
          ThirdPartyFacts.solverDecideFacts
            (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) y

/--
Slice-family provider for witness-indexed semantic surviving-cone
certificates.
-/
abbrev smallDAGWitnessSemanticConeProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessSemanticConeCertificateAt W

/--
Witness-indexed semantic restriction extraction for the stronger shrinkage
fallback route.

This is the function-level corollary consumed by the shrinkage route. It is
usually expected to be obtained from a more semantic source object such as
`SmallDAGWitnessSemanticConeCertificateAt`, not proved directly from scratch.
-/
structure SmallDAGWitnessRestrictionExtractionAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  r :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  aliveBound : Nat
  hAliveBound : r.alive.card ≤ aliveBound
  hStable :
    ∀ x : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) (r.apply x) =
        ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) x

/--
Slice-family provider for witness-indexed semantic restriction extractions.
-/
abbrev smallDAGWitnessRestrictionExtractionProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessRestrictionExtractionAt W

/--
Any surviving-cone certificate yields the semantic restriction extraction
needed by the stronger shrinkage route.

This theorem is intentionally simple: it isolates the exact implication the
future DAG-side semantic theorem must feed, without mixing in any arithmetic
side conditions.
-/
def smallDAGWitnessRestrictionExtractionAt_of_semanticConeCertificate
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cone : SmallDAGWitnessSemanticConeCertificateAt W) :
    SmallDAGWitnessRestrictionExtractionAt W := by
  refine
    { r := cone.r
      aliveBound := cone.aliveBound
      hAliveBound := cone.hAliveBound
      hStable := ?_ }
  intro x
  have hAgree :
      ∀ i ∈ cone.r.alive, (cone.r.apply x) i = x i := by
    intro i hi
    simpa using Facts.LocalityLift.Restriction.apply_alive cone.r x hi
  exact cone.hLocal (cone.r.apply x) x hAgree

/--
Provider reduction from semantic surviving-cone certificates to semantic
restriction extractions.
-/
def smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCone : smallDAGWitnessSemanticConeProviderOnSlices F SizeBound) :
    smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound := by
  intro n β ε W
  exact smallDAGWitnessRestrictionExtractionAt_of_semanticConeCertificate
    (hCone n β ε W)

/--
The syntactic input support of the DAG output already yields a stabilizing
restriction extraction.

This is the first direct restricted-model source theorem on the strong sprint:
no shrinkage machinery is needed to see that overwriting all non-support
coordinates cannot change the DAG output.
-/
noncomputable def smallDAGWitnessRestrictionExtractionAt_of_support
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    SmallDAGWitnessRestrictionExtractionAt W := by
  let solver : Magnification.SmallGeneralCircuitSolver_Partial p :=
    generalSolverOfSmallDAGWitnessOnSlice W
  let alive : Finset (Fin (Models.partialInputLen p)) :=
    DagCircuit.support W.C
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
    ThirdPartyFacts.castRestriction hlen.symm rPartial
  refine
    { r := rFacts
      aliveBound := alive.card
      hAliveBound := ?_
      hStable := ?_ }
  · calc
      rFacts.alive.card = rPartial.alive.card := by
        simpa [rFacts] using ThirdPartyFacts.castRestriction_alive_card hlen.symm rPartial
      _ = alive.card := by
        simp [rPartial]
      _ ≤ alive.card := le_rfl
  · have hstablePartial :
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (rPartial.apply x) = solver.decide x := by
      intro x
      change DagCircuit.eval W.C (rPartial.apply x) = DagCircuit.eval W.C x
      apply DagCircuit.eval_eq_of_eq_on_support
      intro i hi
      exact Facts.LocalityLift.Restriction.apply_alive rPartial x hi
    have hstableCast :
        ∀ x0 : Core.BitVec (Models.partialInputLen p),
          ThirdPartyFacts.solverDecideFacts (p := p) solver
              (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x0)) =
            ThirdPartyFacts.solverDecideFacts (p := p) solver
              (ThirdPartyFacts.castBitVec hlen.symm x0) := by
      intro x0
      change
        solver.decide
            (ThirdPartyFacts.castBitVec hlen
              (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x0))) =
          solver.decide
            (ThirdPartyFacts.castBitVec hlen
              (ThirdPartyFacts.castBitVec hlen.symm x0))
      simpa [ThirdPartyFacts.castBitVec_castBitVec_symm] using hstablePartial x0
    have hstableRaw :=
      ThirdPartyFacts.stable_of_stable_cast
        (h := hlen.symm)
        (decide := ThirdPartyFacts.solverDecideFacts (p := p) solver)
        (r := rPartial)
        hstableCast
    intro x
    simpa [solver, generalSolverOfSmallDAGWitnessOnSlice, rFacts] using hstableRaw x

/--
Numeric side conditions upgrading a semantic restriction extraction to the full
restriction-data package required by `ShrinkageCertificate.ofRestriction`.

This layer is intentionally separate from `SmallDAGWitnessRestrictionExtractionAt`
so the source-side blocker is not forced to mix semantic stabilization with
arithmetic packaging.
-/
structure SmallDAGWitnessRestrictionNumericDataAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (E : SmallDAGWitnessRestrictionExtractionAt W) where
  hBoundPolylog :
    E.aliveBound ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  hBoundQuarter :
    E.aliveBound ≤
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4
  hSmallEnough :
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.size * E.r.alive.card.succ
        , ℓ := E.r.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth }

/--
Witness-indexed restriction-level data for the stronger shrinkage fallback
route.

This is the DAG analogue of `FormulaRestrictionCertificateDataPartial`, but
specialized to one concrete slice witness `W` instead of a whole formula-side
extraction interface.
-/
structure SmallDAGWitnessRestrictionCertificateDataAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  r :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  hPolylog :
    r.alive.card ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  hSmallEnough :
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.size * r.alive.card.succ
        , ℓ := r.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth }
  hQuarter :
    r.alive.card ≤
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4
  hStable :
    ∀ x : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) (r.apply x) =
        ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfSmallDAGWitnessOnSlice W) x

/--
Package semantic restriction extraction plus numeric side conditions into the
full restriction-data object required by the shrinkage-certificate builder.
-/
def smallDAGWitnessRestrictionCertificateDataAt_of_extractionAndNumeric
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (E : SmallDAGWitnessRestrictionExtractionAt W)
    (N : SmallDAGWitnessRestrictionNumericDataAt E) :
    SmallDAGWitnessRestrictionCertificateDataAt W where
  r := E.r
  hPolylog := le_trans E.hAliveBound N.hBoundPolylog
  hSmallEnough := N.hSmallEnough
  hQuarter := le_trans E.hAliveBound N.hBoundQuarter
  hStable := E.hStable

/--
Slice-family provider for witness-indexed restriction-level certificate data.
-/
abbrev smallDAGWitnessRestrictionCertificateDataProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessRestrictionCertificateDataAt W

/--
Slice-family provider for numeric side conditions on top of witness-indexed
semantic restriction extractions.
-/
abbrev smallDAGWitnessRestrictionNumericDataProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessRestrictionNumericDataAt (hExtract n β ε W)

/--
Upgrade separate semantic extraction and numeric side-condition providers into
the packaged restriction-data provider.
-/
def smallDAGWitnessRestrictionCertificateDataProviderOnSlices_of_extractionAndNumericProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hNumeric : smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
    smallDAGWitnessRestrictionCertificateDataProviderOnSlices F SizeBound := by
  intro n β ε W
  exact smallDAGWitnessRestrictionCertificateDataAt_of_extractionAndNumeric
    (hExtract n β ε W) (hNumeric n β ε W)

/--
Witness-indexed shrinkage certificate for the general solver induced by one
small DAG witness on a fixed slice.
-/
abbrev SmallDAGWitnessShrinkageCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) : Type :=
  let solver := generalSolverOfSmallDAGWitnessOnSlice W
  Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate
    (p := ThirdPartyFacts.toFactsParamsPartial p)
    (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
    (ThirdPartyFacts.solverDecideFacts (p := p) solver)

/--
Build the witness-indexed shrinkage certificate directly from restriction-level
data via `ShrinkageCertificate.ofRestriction`.
-/
noncomputable def smallDAGWitnessShrinkageCertificateAt_of_restrictionData
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (D : SmallDAGWitnessRestrictionCertificateDataAt W) :
    SmallDAGWitnessShrinkageCertificateAt W := by
  let solver := generalSolverOfSmallDAGWitnessOnSlice W
  exact
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.ofRestriction
      (p := ThirdPartyFacts.toFactsParamsPartial p)
      (general := ThirdPartyFacts.toFactsGeneralSolverPartial solver)
      (generalEval := ThirdPartyFacts.solverDecideFacts (p := p) solver)
      (restriction := D.r)
      D.hPolylog
      D.hSmallEnough
      D.hQuarter
      D.hStable

/--
Slice-family provider for witness-indexed shrinkage certificates on the
general-solver view of small DAG witnesses.
-/
abbrev smallDAGWitnessShrinkageCertificateProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessShrinkageCertificateAt W

/--
Restriction-data provider reduction to shrinkage certificates on slice DAG
witnesses.
-/
noncomputable def smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hData : smallDAGWitnessRestrictionCertificateDataProviderOnSlices F SizeBound) :
    smallDAGWitnessShrinkageCertificateProviderOnSlices F SizeBound := by
  intro n β ε W
  exact smallDAGWitnessShrinkageCertificateAt_of_restrictionData W (hData n β ε W)

/--
DAG slack package indexed by a concrete small solver witness (instead of a
global `PpolyDAG` witness on a fixed-slice language).
-/
structure DAGStableRestrictionSlackPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  r : Facts.LocalityLift.Restriction (Models.partialInputLen p)
  hSlack :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - r.alive.card)
  hLocal :
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ r.alive, x i = y i) →
        DagCircuit.eval W.C x = DagCircuit.eval W.C y

/--
Semantic restriction extraction plus a half-table alive bound already suffice
for the older encoded-coordinate slack package.

This is a more direct strong-fallback bridge than the shrinkage-certificate
route: once DAG semantics yields a stabilizing restriction with
`|alive| ≤ tableLen/2`, the remaining contradiction plumbing is immediate.
-/
noncomputable def dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (E : SmallDAGWitnessRestrictionExtractionAt W)
    (hHalfAliveBound : E.aliveBound ≤ Models.Partial.tableLen p.n / 2) :
    DAGStableRestrictionSlackPackageAt W := by
  classical
  let solver : Magnification.SmallGeneralCircuitSolver_Partial p :=
    generalSolverOfSmallDAGWitnessOnSlice W
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let r : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen E.r
  have hAliveHalf : r.alive.card ≤ Models.Partial.tableLen p.n / 2 := by
    calc
      r.alive.card = E.r.alive.card := by
        simpa [r] using ThirdPartyFacts.castRestriction_alive_card hlen E.r
      _ ≤ E.aliveBound := E.hAliveBound
      _ ≤ Models.Partial.tableLen p.n / 2 := hHalfAliveBound
  have hStable :
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x := by
    let hstable_cast :
        ∀ x0 : Core.BitVec (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          solver.decide (ThirdPartyFacts.castBitVec hlen (E.r.apply x0)) =
            solver.decide (ThirdPartyFacts.castBitVec hlen x0) := by
      intro x0
      simpa [solver, generalSolverOfSmallDAGWitnessOnSlice,
        Magnification.SmallGeneralCircuitSolver_Partial.decide,
        ThirdPartyFacts.solverDecideFacts, hlen] using E.hStable x0
    simpa [r] using
      (ThirdPartyFacts.stable_of_stable_cast
        (h := hlen) (decide := solver.decide) (r := E.r) hstable_cast)
  refine
    { r := r
      hSlack := ?_
      hLocal := ?_ }
  · have hExpMono :
        Models.Partial.tableLen p.n / 2 ≤
          Models.Partial.tableLen p.n - r.alive.card := by
      omega
    exact lt_of_lt_of_le p.circuit_bound_ok
      (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono)
  · intro x y hAgree
    simpa [solver, generalSolverOfSmallDAGWitnessOnSlice,
      Magnification.SmallGeneralCircuitSolver_Partial.decide] using
      (Facts.LocalityLift.Restriction.localizedOn_of_stable
        (r := r) (f := solver.decide) hStable) x y hAgree

/--
Support-size restricted models immediately feed the strong fallback route.

Once the output support of the DAG is at most half the truth-table length, the
support-based extraction closes the encoded-coordinate slack package with no
additional shrinkage layer.
-/
noncomputable def dagStableRestrictionSlackPackageAt_of_supportHalfBound
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2) :
    DAGStableRestrictionSlackPackageAt W := by
  let E : SmallDAGWitnessRestrictionExtractionAt W :=
    smallDAGWitnessRestrictionExtractionAt_of_support W
  have hHalfAliveBound : E.aliveBound ≤ Models.Partial.tableLen p.n / 2 := by
    simpa [E, smallDAGWitnessRestrictionExtractionAt_of_support] using hSupportHalf
  exact dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound
    E hHalfAliveBound

/--
Existing numeric side data already imply the half-table alive bound needed by
`dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound`.
-/
noncomputable def dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (E : SmallDAGWitnessRestrictionExtractionAt W)
    (N : SmallDAGWitnessRestrictionNumericDataAt E) :
    DAGStableRestrictionSlackPackageAt W := by
  have hQuarter :
      E.aliveBound ≤ Models.partialInputLen p / 4 := by
    simpa [ThirdPartyFacts.inputLen_toFactsPartial p] using N.hBoundQuarter
  have hHalfAliveBound :
      E.aliveBound ≤ Models.Partial.tableLen p.n / 2 :=
    ThirdPartyFacts.quarterAlive_to_decideLocal_bound (p := p) hQuarter
  exact dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound
    E hHalfAliveBound

/--
Any shrinkage certificate for the DAG-induced general solver yields the older
encoded-coordinate slack package on the same slice.

This theorem does not solve the new one-sided/value-centered blocker directly,
but it packages the full stronger fallback route behind one precise remaining
source-side obligation: a witness-indexed shrinkage certificate for the
DAG-derived general solver.
-/
noncomputable def dagStableRestrictionSlackPackageAt_of_shrinkageCertificate
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : SmallDAGWitnessShrinkageCertificateAt W) :
    DAGStableRestrictionSlackPackageAt W := by
  classical
  let solver : Magnification.SmallGeneralCircuitSolver_Partial p :=
    generalSolverOfSmallDAGWitnessOnSlice W
  letI :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (ThirdPartyFacts.solverDecideFacts (p := p) solver) := ⟨cert⟩
  have hHalf :
      ThirdPartyFacts.HalfTableCertificateBound (p := p) solver :=
    inferInstance
  let stableData :=
    ThirdPartyFacts.stableRestriction_of_certificate
      (p := p) solver hHalf.half_bound
  let r := Classical.choose stableData
  have hAliveHalf :
      r.alive.card ≤ Models.Partial.tableLen p.n / 2 :=
    (Classical.choose_spec stableData).1
  have hStable :
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x :=
    (Classical.choose_spec stableData).2
  refine
    { r := r
      hSlack := ?_
      hLocal := ?_ }
  · have hExpMono :
        Models.Partial.tableLen p.n / 2 ≤
          Models.Partial.tableLen p.n - Models.Partial.tableLen p.n / 2 := by
      omega
    have hExpMono' :
        Models.Partial.tableLen p.n / 2 ≤
          Models.Partial.tableLen p.n - r.alive.card := by
      exact le_trans hExpMono
        (Nat.sub_le_sub_left hAliveHalf (Models.Partial.tableLen p.n))
    exact lt_of_lt_of_le p.circuit_bound_ok
      (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono')
  · intro x y hAgree
    simpa [solver, generalSolverOfSmallDAGWitnessOnSlice,
      Magnification.SmallGeneralCircuitSolver_Partial.decide] using
      (Facts.LocalityLift.Restriction.localizedOn_of_stable
        (r := r) (f := solver.decide) hStable) x y hAgree

/--
Slice-family provider for witness-indexed DAG slack packages.
-/
abbrev dagStableRestrictionSlackPackageAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      DAGStableRestrictionSlackPackageAt W

/--
Certificate-provider reduction to the stronger encoded-coordinate slack route.
-/
noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : smallDAGWitnessShrinkageCertificateProviderOnSlices F SizeBound) :
    dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact dagStableRestrictionSlackPackageAt_of_shrinkageCertificate W (hCert n β ε W)

/--
Direct provider reduction from semantic restriction extraction plus numeric
side-data to the older encoded-coordinate slack package.
-/
noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_restrictionExtractionAndNumericProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hNumeric : smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
    dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric
    (hExtract n β ε W) (hNumeric n β ε W)

/--
Witness-indexed source package for the new promise/value locality route.

Unlike `DAGStableRestrictionSlackPackageAt`, this package is phrased directly
in the consumer-facing shape:

1. semantic value coordinates `S`,
2. direct counting slack on `S`,
3. locality only on valid encodings and only across the promise YES/NO domain.

This is intended to be the canonical source-side API for the weaker
theorem-minimal route; the older encoded-coordinate packages remain as stronger
fallbacks and audit surfaces.
-/
structure PromiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- Semantic truth-table value coordinates used by the locality witness. -/
  S : ValueCoordinateSet p
  /-- Direct counting slack on the semantic coordinates. -/
  hSlack :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - S.card)
  /--
  Promise/value locality for the current small solver.

  The package deliberately avoids quantifying over arbitrary encoded bitstrings:
  only canonical valid encodings on the YES/NO promise domain matter.
  -/
  hLocal :
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      x ∈ (GapPartialMCSPPromise p).Yes →
      y ∈ (GapPartialMCSPPromise p).No →
      ValidEncoding p x →
      ValidEncoding p y →
      AgreeOnValues (p := p) S x y →
        DagCircuit.eval W.C x = DagCircuit.eval W.C y

/--
Slice-family provider for witness-indexed promise/value locality packages.
-/
abbrev promiseValueLocalityPackageAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      PromiseValueLocalityPackageAt W

/--
If the stronger encoded-coordinate restriction package happens to keep only
semantic value positions alive, then it already yields the weaker
promise/value locality package on the induced semantic coordinate set.

This theorem does not solve the general weak-route blocker.  Instead, it
isolates a more precise source-side gap: the strong fallback route would feed
the current mainline automatically once the surviving alive set can be shown to
sit entirely on value coordinates.
-/
noncomputable def promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : DAGStableRestrictionSlackPackageAt W)
    (hValueAlive :
      ∀ i ∈ cert.r.alive,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    PromiseValueLocalityPackageAt W := by
  classical
  let S : ValueCoordinateSet p :=
    Finset.univ.filter (fun j => tableValPos j ∈ cert.r.alive)
  have hSCard :
      S.card ≤ cert.r.alive.card := by
    have hImgSub : Finset.image tableValPos S ⊆ cert.r.alive := by
      intro i hi
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact hj
    have hCardImage :
        S.card = (Finset.image tableValPos S).card := by
      rw [Finset.card_image_of_injective S tableValPos_injective]
    calc
      S.card = (Finset.image tableValPos S).card := hCardImage
      _ ≤ cert.r.alive.card := Finset.card_le_card hImgSub
  refine
    { S := S
      hSlack := ?_
      hLocal := ?_ }
  · have hExpMono :
        Models.Partial.tableLen p.n - cert.r.alive.card ≤
          Models.Partial.tableLen p.n - S.card := by
      exact Nat.sub_le_sub_left hSCard (Models.Partial.tableLen p.n)
    exact lt_of_lt_of_le cert.hSlack
      (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono)
  · intro x y _hxYes _hyNo _hxValid _hyValid hAgree
    apply cert.hLocal x y
    intro i hi
    obtain ⟨j, rfl⟩ := hValueAlive i hi
    exact hAgree j (by simp [S, hi])

/--
Primary weak-route consumer at one fixed slice witness.

This is the theorem-minimal accepted-family endpoint: a finite family of total
truth tables, larger than the counting capacity of all circuits of size
`≤ sNO - 1`, all accepted by the current small DAG solver.
-/
abbrev AcceptedFamilyCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) : Type :=
  LowerBounds.AcceptedFamilyCertificate
    (p := p)
    (DagCircuit.eval W.C)

/--
Slice-family provider for witness-indexed accepted-family certificates.
-/
abbrev acceptedFamilyCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      AcceptedFamilyCertificateAt W

/--
Direct contradiction from the generic accepted-family weak endpoint.
-/
theorem no_small_dag_solver_of_acceptedFamilyCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : AcceptedFamilyCertificateAt W) :
    False := by
  have hCorrectPromise : SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval W.C) := by
    constructor
    · intro x hx
      exact W.hCorrect.1 x (by simpa [gapSliceOfParams] using hx)
    · intro x hx
      exact W.hCorrect.2 x (by simpa [gapSliceOfParams] using hx)
  exact
    LowerBounds.no_function_solves_mcsp_of_acceptedFamilyCertificate
      (p := p)
      (f := DagCircuit.eval W.C)
      cert
      hCorrectPromise

/--
The stronger encoded-coordinate slack package already feeds the generic
accepted-family weak endpoint.

The accepted family is chosen inside total truth-table encodings.  Then all
mask coordinates are automatically fixed to `true`, so the strong locality
witness on the full alive set only needs value agreement on those alive
coordinates that lie in the value half.
-/
noncomputable def acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : DAGStableRestrictionSlackPackageAt W) :
    AcceptedFamilyCertificateAt W := by
  classical
  let yYes : Core.BitVec (Models.partialInputLen p) :=
    encodeTotalAsPartial (fun _ => false)
  have hYes : yYes ∈ (GapPartialMCSPPromise p).Yes := by
    apply gapPartialMCSP_yes_of_small
    rw [show decodePartial yYes = totalTableToPartial (fun _ => false) from by
      simp [yYes, decodePartial_encodeTotal]]
    refine ⟨Circuit.const false, ?_, ?_⟩
    · simp [Circuit.size]
      exact p.sYES_pos
    · apply const_false_consistent_of_vals_false
      intro j
      right
      simp [totalTableToPartial]
  let S : ValueCoordinateSet p :=
    Finset.univ.filter (fun j => tableValPos j ∈ cert.r.alive)
  let family : Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    Counting.consistentFinset
      (Counting.prescribedPartial S (Partial.valPart yYes))
  refine
    { family := family
      hLarge := ?_
      hAccept := ?_ }
  · have hSCard :
        S.card ≤ cert.r.alive.card := by
      have hImgSub : Finset.image tableValPos S ⊆ cert.r.alive := by
        intro i hi
        simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        exact hj
      have hCardImage :
          S.card = (Finset.image tableValPos S).card := by
        rw [Finset.card_image_of_injective S tableValPos_injective]
      calc
        S.card = (Finset.image tableValPos S).card := hCardImage
        _ ≤ cert.r.alive.card := Finset.card_le_card hImgSub
    have hSlackS :
        Models.circuitCountBound p.n (p.sNO - 1) <
          2 ^ (Models.Partial.tableLen p.n - S.card) := by
      have hExpMono :
          Models.Partial.tableLen p.n - cert.r.alive.card ≤
            Models.Partial.tableLen p.n - S.card := by
        exact Nat.sub_le_sub_left hSCard (Models.Partial.tableLen p.n)
      exact lt_of_lt_of_le cert.hSlack
        (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono)
    have hCard :
        family.card = 2 ^ (Models.Partial.tableLen p.n - S.card) := by
      dsimp [family]
      calc
        (Counting.consistentFinset
          (Counting.prescribedPartial S (Partial.valPart yYes))).card
            = 2 ^ undefinedCount
                (Counting.prescribedPartial S (Partial.valPart yYes)) := by
                  simpa using Counting.card_consistentFinset
                    (Counting.prescribedPartial S (Partial.valPart yYes))
        _ = 2 ^ (Models.Partial.tableLen p.n - S.card) := by
              simpa using Counting.undefinedCount_prescribedPartial
                S (Partial.valPart yYes)
    exact lt_of_lt_of_eq hSlackS hCard.symm
  · intro g hg
    have hgCons :
        consistentTotal
          (Counting.prescribedPartial S (Partial.valPart yYes)) g := by
      dsimp [family] at hg
      simpa [Counting.consistentFinset] using hg
    let z : Core.BitVec (Models.partialInputLen p) := encodeTotalAsPartial g
    have hAgreeAlive : ∀ i ∈ cert.r.alive, yYes i = z i := by
      intro i hi
      by_cases h_lt : (i : Nat) < Models.Partial.tableLen p.n
      · have hMaskYes : yYes i = true := by
          simp [yYes, encodeTotalAsPartial, encodePartial, totalTableToPartial, h_lt]
        have hMaskZ : z i = true := by
          simp [z, encodeTotalAsPartial, encodePartial, totalTableToPartial, h_lt]
        exact hMaskYes.trans hMaskZ.symm
      · have h_i_lt : (i : Nat) < Models.partialInputLen p := i.2
        have h_j_lt :
            (i : Nat) - Models.Partial.tableLen p.n < Models.Partial.tableLen p.n := by
          have : (i : Nat) <
              Models.Partial.tableLen p.n + Models.Partial.tableLen p.n := by
            simpa [Models.Partial.inputLen, two_mul, Models.partialInputLen] using h_i_lt
          omega
        let j : Fin (Models.Partial.tableLen p.n) :=
          ⟨(i : Nat) - Models.Partial.tableLen p.n, h_j_lt⟩
        have hValPos : tableValPos j = i := by
          apply Fin.ext
          change
            Models.Partial.tableLen p.n +
                ((i : Nat) - Models.Partial.tableLen p.n) =
              (i : Nat)
          omega
        have hjS : j ∈ S := by
          simp [S, hValPos, hi]
        have hgEq : g j = Partial.valPart yYes j := by
          simpa using
            (Counting.consistentTotal_prescribedPartial_eq hgCons j hjS)
        have hzVal : Partial.valPart z j = g j := by
          simp [z, encodeTotalAsPartial, totalTableToPartial,
            Partial.valPart, encodePartial, Partial.valIndex]
        have hValEq : Partial.valPart yYes j = Partial.valPart z j := by
          exact hgEq.symm.trans hzVal.symm
        have hAtValPos : yYes (tableValPos j) = z (tableValPos j) := by
          simpa [Partial.valPart] using hValEq
        simpa [hValPos] using hAtValPos
    have hEq : DagCircuit.eval W.C yYes = DagCircuit.eval W.C z :=
      cert.hLocal yYes z hAgreeAlive
    have hYesEval : DagCircuit.eval W.C yYes = true :=
      W.hCorrect.1 yYes (by simpa [gapSliceOfParams] using hYes)
    exact hEq.symm.trans hYesEval

/--
Direct contradiction from the stronger encoded-coordinate slack package, now
routed through the generic accepted-family weak consumer.
-/
theorem no_small_dag_solver_of_dagStableRestrictionSlackPackageAt_via_acceptedFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : DAGStableRestrictionSlackPackageAt W) :
    False := by
  exact no_small_dag_solver_of_acceptedFamilyCertificateAt W
    (acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt cert)

/--
Restricted-model closure: half-sized DAG output support already contradicts
correctness on the fixed Gap-MCSP slice through the strong accepted-family
route.
-/
theorem no_small_dag_solver_of_supportHalfBound_via_acceptedFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2) :
    False := by
  exact no_small_dag_solver_of_dagStableRestrictionSlackPackageAt_via_acceptedFamily
    W (dagStableRestrictionSlackPackageAt_of_supportHalfBound W hSupportHalf)

/--
Bridge from witness-indexed accepted-family certificates to the canonical
accepted-family version of Layer B in `AsymptoticDAGBarrier`.
-/
theorem smallDAGAcceptedFamilyStatement_of_certificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : acceptedFamilyCertificateAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  intro n β ε C hSize hCorrect
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact ⟨hCert n β ε W⟩

/--
Provider reduction: the stronger encoded-coordinate slack package already
yields the generic accepted-family weak endpoint on every slice witness.
-/
noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound) :
    acceptedFamilyCertificateAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt
    (hPkg n β ε W)

/--
Compiled strong-fallback bridge from witness-indexed encoded-coordinate slack
packages directly to the canonical accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_certificateProvider F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider
      F SizeBound hPkg)

/--
Compiled strong-fallback bridge from witness-indexed shrinkage certificates to
the canonical accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_shrinkageCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : smallDAGWitnessShrinkageCertificateProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider
    F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider
      F SizeBound hCert)

/--
Compiled strong-fallback bridge from witness-indexed restriction data to the
canonical accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_restrictionDataProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hData : smallDAGWitnessRestrictionCertificateDataProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_shrinkageCertificateProvider F SizeBound
    (smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider
      F SizeBound hData)

/--
Compiled strong-fallback bridge from semantic restriction extraction plus
numeric side-data directly to the canonical accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hNumeric : smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider
    F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_restrictionExtractionAndNumericProvider
      F SizeBound hExtract hNumeric)

/--
Candidate YES-certificate-complexity mechanism for the current weak mainline.

This is not a new endpoint.  It records the more operational source-side fact
one would really like to prove from DAG semantics:

1. choose one valid YES center `yYes`,
2. choose semantic value coordinates `S`,
3. show that on valid promise inputs, agreeing with `yYes` on `S` already
   forces the solver decision.

Once the center itself is known to be accepted, this immediately yields the
weaker acceptance-only invariant `PromiseYesAcceptanceInvariantAt`.
-/
structure PromiseYesDecisionCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- One concrete valid YES-center. -/
  yYes : Core.BitVec (Models.partialInputLen p)
  hYes : yYes ∈ (GapPartialMCSPPromise p).Yes
  hValidYes : ValidEncoding p yYes
  /-- Semantic truth-table value coordinates controlling the certificate. -/
  S : ValueCoordinateSet p
  /--
  On the promise partition, agreement with the YES center on `S` determines
  the solver output.
  -/
  hDecide :
    ∀ z : Core.BitVec (Models.partialInputLen p),
      (z ∈ (GapPartialMCSPPromise p).Yes ∨ z ∈ (GapPartialMCSPPromise p).No) →
      ValidEncoding p z →
      AgreeOnValues (p := p) S yYes z →
        DagCircuit.eval W.C z = DagCircuit.eval W.C yYes

/--
The bare YES-decision certificate is too weak to be a meaningful blocker on its
own: every correct small DAG witness already has such a certificate by choosing
an easy all-false YES center and taking `S` to be *all* semantic value
coordinates.

This theorem is a guard-rail: it shows that the real remaining difficulty is
quantitative, namely extracting such a certificate with sufficiently small
`S` (or directly with counting slack), not merely proving existence of some
one-sided decision certificate.
-/
def promiseYesDecisionCertificateAt_fullValueCoordinates
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    PromiseYesDecisionCertificateAt W := by
  let yYes : Core.BitVec (Models.partialInputLen p) :=
    Models.encodeTotalAsPartial (fun _ => false)
  have hyValid : ValidEncoding p yYes := by
    simpa [yYes] using
      validEncoding_encodeTotalAsPartial p (fun _ => false)
  have hyYes : yYes ∈ (GapPartialMCSPPromise p).Yes := by
    show gapPartialMCSP_Language p (partialInputLen p) yYes = true
    rw [gapPartialMCSP_language_true_iff_yes]
    rw [show decodePartial yYes = totalTableToPartial (fun _ => false) from by
      simpa [yYes, decodePartial_encodeTotal]]
    refine ⟨Circuit.const false, ?_, ?_⟩
    · simp [Circuit.size]
      exact p.sYES_pos
    · apply const_false_consistent_of_vals_false
      intro j
      right
      simp [totalTableToPartial]
  refine
    { yYes := yYes
      hYes := hyYes
      hValidYes := hyValid
      S := Finset.univ
      hDecide := ?_ }
  intro z hzPromise _hzValid hAgree
  have hyEval : DagCircuit.eval W.C yYes = true :=
    W.hCorrect.1 yYes (by simpa [gapSliceOfParams] using hyYes)
  have hzValsFalse : ∀ i : Fin (Models.Partial.tableLen p.n), Partial.valPart z i = false := by
    intro i
    have hEq := hAgree i (by simp)
    simpa [yYes, encodeTotalAsPartial, totalTableToPartial,
      Partial.valPart, encodePartial, Partial.valIndex] using hEq.symm
  have hzYes : z ∈ (GapPartialMCSPPromise p).Yes := by
    show gapPartialMCSP_Language p (partialInputLen p) z = true
    rw [gapPartialMCSP_language_true_iff_yes]
    refine ⟨Circuit.const false, ?_, ?_⟩
    · simp [Circuit.size]
      exact p.sYES_pos
    · apply const_false_consistent_of_vals_false
      intro j
      by_cases hm : Partial.maskPart z j = true
      · right
        simp [decodePartial, hm, hzValsFalse j]
      · left
        simp [decodePartial, hm]
  cases hzPromise with
  | inl hzYesPromise =>
      have hzEval : DagCircuit.eval W.C z = true :=
        W.hCorrect.1 z (by simpa [gapSliceOfParams] using hzYesPromise)
      exact hzEval.trans hyEval.symm
  | inr hzNoPromise =>
      have hzEvalTrue : DagCircuit.eval W.C z = true :=
        W.hCorrect.1 z (by simpa [gapSliceOfParams] using hzYes)
      have hzEvalFalse : DagCircuit.eval W.C z = false :=
        W.hCorrect.2 z (by simpa [gapSliceOfParams] using hzNoPromise)
      exact False.elim (Bool.false_ne_true (hzEvalFalse.symm.trans hzEvalTrue))

/--
Candidate source-side semantic invariant for the YES-centered weak route.

This is intentionally not another terminal endpoint.  It isolates only the
semantic heart of the current mainline theorem target:

1. one concrete valid YES center,
2. one semantic value-coordinate set `S`,
3. acceptance of every valid promise-relevant completion agreeing with that
   center on `S`.

Counting slack is kept external so the remaining DAG-side search can focus on
the semantic invariant first and only then discharge the numeric upgrade to
`PromiseYesSubcubeCertificateAt`.
-/
structure PromiseYesAcceptanceInvariantAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- One concrete valid YES-center. -/
  yYes : Core.BitVec (Models.partialInputLen p)
  hYes : yYes ∈ (GapPartialMCSPPromise p).Yes
  hValidYes : ValidEncoding p yYes
  /-- Semantic truth-table value coordinates controlling the stable region. -/
  S : ValueCoordinateSet p
  /--
  One-sided promise acceptance on the semantic region around `yYes`.
  -/
  hAccept :
    ∀ z : Core.BitVec (Models.partialInputLen p),
      (z ∈ (GapPartialMCSPPromise p).Yes ∨ z ∈ (GapPartialMCSPPromise p).No) →
      ValidEncoding p z →
      AgreeOnValues (p := p) S yYes z →
        DagCircuit.eval W.C z = true

/--
One-sided YES-centered promise/value source certificate.

This is the closest theorem target to the current counting contradiction:
choose one valid YES center plus semantic value coordinates `S`, and show that
every valid promise-relevant completion agreeing with the center on `S` is
accepted.

Compared with the stronger `YesSubcubeCertificateAt` below, this interface does
not insist on acceptance of all valid completions or on direct reduction to the
generic accepted-family consumer. It is the more realistic immediate source-side
goal for the YES-centered weak route.
-/
structure PromiseYesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- One concrete valid YES-center. -/
  yYes : Core.BitVec (Models.partialInputLen p)
  hYes : yYes ∈ (GapPartialMCSPPromise p).Yes
  hValidYes : ValidEncoding p yYes
  /-- Semantic truth-table value coordinates controlling the stable region. -/
  S : ValueCoordinateSet p
  /-- Direct counting slack on `S`. -/
  hSlack :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - S.card)
  /--
  One-sided promise acceptance: every valid YES/NO completion agreeing with
  `yYes` on `S` is accepted by the solver.
  -/
  hAccept :
    ∀ z : Core.BitVec (Models.partialInputLen p),
      (z ∈ (GapPartialMCSPPromise p).Yes ∨ z ∈ (GapPartialMCSPPromise p).No) →
      ValidEncoding p z →
      AgreeOnValues (p := p) S yYes z →
        DagCircuit.eval W.C z = true

/--
Numeric upgrade from the semantic YES-centered invariant to the actual
promise-aware weak-route certificate used by the counting contradiction.
-/
def promiseYesSubcubeCertificateAt_of_acceptanceInvariant
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (inv : PromiseYesAcceptanceInvariantAt W)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - inv.S.card)) :
    PromiseYesSubcubeCertificateAt W where
  yYes := inv.yYes
  hYes := inv.hYes
  hValidYes := inv.hValidYes
  S := inv.S
  hSlack := hSlack
  hAccept := inv.hAccept

/--
Forget the slack field of a promise-aware YES-centered weak-route certificate,
leaving just the semantic invariant.
-/
def promiseYesAcceptanceInvariantAt_of_promiseYesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseYesSubcubeCertificateAt W) :
    PromiseYesAcceptanceInvariantAt W where
  yYes := cert.yYes
  hYes := cert.hYes
  hValidYes := cert.hValidYes
  S := cert.S
  hAccept := cert.hAccept

/--
The existing pairwise promise/value locality package already yields the more
operational YES-certificate-complexity mechanism underlying the current
mainline.
-/
noncomputable def promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    PromiseYesDecisionCertificateAt W := by
  classical
  let x_yes := Classical.choose
    (exists_yes_no_agreeing_on_values_of_countingSlack p cert.S cert.hSlack)
  have hYesSpec := Classical.choose_spec
    (exists_yes_no_agreeing_on_values_of_countingSlack p cert.S cert.hSlack)
  have hData := Classical.choose_spec hYesSpec
  have hValidYes : ValidEncoding p x_yes := hData.2.1
  have hInYes : x_yes ∈ (GapPartialMCSPPromise p).Yes := hData.2.2.2.1
  refine
    { yYes := x_yes
      hYes := hInYes
      hValidYes := hValidYes
      S := cert.S
      hDecide := ?_ }
  intro z hzPromise hzValid hAgree
  cases hzPromise with
  | inl hzYes =>
      have hzEval : DagCircuit.eval W.C z = true :=
        W.hCorrect.1 z (by simpa [gapSliceOfParams] using hzYes)
      have hYesEval : DagCircuit.eval W.C x_yes = true :=
        W.hCorrect.1 x_yes (by simpa [gapSliceOfParams] using hInYes)
      exact hzEval.trans hYesEval.symm
  | inr hzNo =>
      have hEq :
          DagCircuit.eval W.C x_yes = DagCircuit.eval W.C z :=
        cert.hLocal x_yes z hInYes hzNo hValidYes hzValid hAgree
      exact hEq.symm

/--
Reduce the candidate YES-certificate-complexity mechanism to the acceptance-only
invariant used by the current mainline theorem target.
-/
def promiseYesAcceptanceInvariantAt_of_decisionCertificate
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseYesDecisionCertificateAt W) :
    PromiseYesAcceptanceInvariantAt W := by
  refine
    { yYes := cert.yYes
      hYes := cert.hYes
      hValidYes := cert.hValidYes
      S := cert.S
      hAccept := ?_ }
  intro z hzPromise hzValid hAgree
  have hEq : DagCircuit.eval W.C z = DagCircuit.eval W.C cert.yYes :=
    cert.hDecide z hzPromise hzValid hAgree
  have hYesEval : DagCircuit.eval W.C cert.yYes = true :=
    W.hCorrect.1 cert.yYes (by simpa [gapSliceOfParams] using cert.hYes)
  exact hEq.trans hYesEval

/--
Operational quantitative form of the current weak-route blocker.

If a YES-centered decision certificate comes with a counting-slack bound on the
same semantic coordinate set `S`, then it already upgrades to the actual
promise-aware one-sided certificate consumed downstream.
-/
def promiseYesSubcubeCertificateAt_of_decisionCertificate
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseYesDecisionCertificateAt W)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - cert.S.card)) :
    PromiseYesSubcubeCertificateAt W :=
  promiseYesSubcubeCertificateAt_of_acceptanceInvariant
    (promiseYesAcceptanceInvariantAt_of_decisionCertificate cert)
    hSlack

/--
The existing pairwise promise/value locality package already yields the
acceptance-only semantic invariant via the more operational YES-decision
certificate.
-/
noncomputable def promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    PromiseYesAcceptanceInvariantAt W := by
  exact promiseYesAcceptanceInvariantAt_of_decisionCertificate
    (promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt cert)

/--
Any pairwise promise/value locality package already yields the weaker
promise-aware one-sided YES-centered route.

This is the key reason the YES-centered path is currently the more realistic
mainline theorem target: the existing pairwise package surface is strong enough
to manufacture one good YES center on the same semantic coordinate set `S`.
-/
noncomputable def promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    PromiseYesSubcubeCertificateAt W := by
  let inv : PromiseYesAcceptanceInvariantAt W :=
    promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt cert
  exact promiseYesSubcubeCertificateAt_of_acceptanceInvariant inv cert.hSlack

/--
Value-supported encoded-coordinate restriction packages already imply the
current one-sided YES-centered weak-route certificate.
-/
noncomputable def promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : DAGStableRestrictionSlackPackageAt W)
    (hValueAlive :
      ∀ i ∈ cert.r.alive,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    PromiseYesSubcubeCertificateAt W := by
  exact promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt
    (promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported
      cert hValueAlive)

/--
Direct contradiction from the promise-aware one-sided YES-centered weak route.
-/
theorem no_small_dag_solver_of_promiseYesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : PromiseYesSubcubeCertificateAt W) :
    False := by
  have hCorrectPromise : SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval W.C) := by
    constructor
    · intro x hx
      exact W.hCorrect.1 x (by simpa [gapSliceOfParams] using hx)
    · intro x hx
      exact W.hCorrect.2 x (by simpa [gapSliceOfParams] using hx)
  exact
    LowerBounds.no_one_sided_value_local_function_solves_mcsp_of_countingSlack
      (p := p)
      (f := DagCircuit.eval W.C)
      cert.yYes
      cert.S
      cert.hYes
      cert.hValidYes
      cert.hSlack
      cert.hAccept
      hCorrectPromise

/--
Slice-family provider for promise-aware one-sided YES-subcube certificates.
-/
abbrev promiseYesSubcubeCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      PromiseYesSubcubeCertificateAt W

/--
Provider-level reduction from the existing pairwise promise/value package route
to the weaker promise-aware YES-centered route.
-/
noncomputable def promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt (hPkg n β ε W)

/--
Closure from a promise-aware one-sided YES-subcube provider.
-/
theorem noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact no_small_dag_solver_of_promiseYesSubcubeCertificateAt W (hCert n β ε W)

/--
Direct closure from the existing pairwise promise/value package route through
the nearer-term promise-aware YES-centered source theorem target.
-/
theorem noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound
    (promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider
      F SizeBound hPkg)

/--
One-sided YES-centered source certificate for the weaker promise/value route.

This is now a structured producer target for the generic accepted-family weak
consumer: one valid YES center plus value coordinates `S` on which acceptance
is stable across all valid completions.
-/
structure YesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- One concrete valid YES-center. -/
  yYes : Core.BitVec (Models.partialInputLen p)
  hYes : yYes ∈ (GapPartialMCSPPromise p).Yes
  hValidYes : ValidEncoding p yYes
  /-- Semantic truth-table value coordinates controlling the stable subcube. -/
  S : ValueCoordinateSet p
  /-- Direct counting slack on `S`. -/
  hSlack :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - S.card)
  /--
  One-sided acceptance: every valid completion agreeing with `yYes` on `S`
  is accepted by the solver.
  -/
  hAccept :
    ∀ z : Core.BitVec (Models.partialInputLen p),
      ValidEncoding p z →
      AgreeOnValues (p := p) S yYes z →
        DagCircuit.eval W.C z = true

/--
Turn a YES-centered value-subcube certificate into the generic accepted-family
weak endpoint by enumerating all total tables agreeing with the center on `S`.
-/
noncomputable def acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : YesSubcubeCertificateAt W) :
    AcceptedFamilyCertificateAt W := by
  classical
  let family : Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    Counting.consistentFinset
      (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes))
  refine
    { family := family
      hLarge := ?_
      hAccept := ?_ }
  · have hCard :
        family.card = 2 ^ (Models.Partial.tableLen p.n - cert.S.card) := by
      dsimp [family]
      calc
        (Counting.consistentFinset
          (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes))).card
            = 2 ^ undefinedCount
                (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes)) := by
                  simpa using Counting.card_consistentFinset
                    (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes))
        _ = 2 ^ (Models.Partial.tableLen p.n - cert.S.card) := by
              simpa using Counting.undefinedCount_prescribedPartial
                cert.S (Partial.valPart cert.yYes)
    exact lt_of_lt_of_eq cert.hSlack hCard.symm
  · intro g hg
    have hgCons :
        consistentTotal
          (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes)) g := by
      dsimp [family] at hg
      simpa [Counting.consistentFinset] using hg
    have hAgree :
        AgreeOnValues (p := p) cert.S cert.yYes (encodeTotalAsPartial g) := by
      intro i hi
      have hgEq : g i = Partial.valPart cert.yYes i :=
        Counting.consistentTotal_prescribedPartial_eq hgCons i hi
      have hVal :
          Partial.valPart (encodeTotalAsPartial g) i = g i := by
        simp [encodeTotalAsPartial, totalTableToPartial,
          Partial.valPart, encodePartial, Partial.valIndex]
      calc
        Partial.valPart cert.yYes i = g i := by simpa using hgEq.symm
        _ = Partial.valPart (encodeTotalAsPartial g) i := hVal.symm
    exact cert.hAccept (encodeTotalAsPartial g)
      (validEncoding_encodeTotalAsPartial p g)
      hAgree

/--
Direct contradiction from the YES-centered value-subcube producer, now routed
through the generic accepted-family weak consumer.
-/
theorem no_small_dag_solver_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : YesSubcubeCertificateAt W) :
    False := by
  exact no_small_dag_solver_of_acceptedFamilyCertificateAt W
    (acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt cert)

/--
Slice-family provider for witness-indexed one-sided YES-subcube certificates.
-/
abbrev yesSubcubeCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      YesSubcubeCertificateAt W

/--
Structured-producer reduction: any YES-subcube provider yields the generic
accepted-family weak endpoint.
-/
noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    acceptedFamilyCertificateAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt (hCert n β ε W)

/--
Compiled weak-route bridge from YES-subcube providers to the canonical
accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_yesSubcubeCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_certificateProvider F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
      F SizeBound hCert)

/--
The stronger all-valid YES-subcube producer automatically yields the weaker
promise-aware one-sided source certificate.
-/
def promiseYesSubcubeCertificateAt_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : YesSubcubeCertificateAt W) :
    PromiseYesSubcubeCertificateAt W := by
  refine
    { yYes := cert.yYes
      hYes := cert.hYes
      hValidYes := cert.hValidYes
      S := cert.S
      hSlack := cert.hSlack
      hAccept := ?_ }
  intro z _hzPromise hzValid hAgree
  exact cert.hAccept z hzValid hAgree

/--
Structured-producer reduction from the stronger all-valid YES-subcube provider
to the weaker promise-aware one-sided source route.
-/
def promiseYesSubcubeCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact promiseYesSubcubeCertificateAt_of_yesSubcubeCertificateAt (hCert n β ε W)

/--
Structured accepted-image producer route.

Unlike `YesSubcubeCertificateAt`, this endpoint does not insist on subcube
geometry: it packages one injective generator whose full image is accepted by
the solver and already exceeds the counting capacity threshold.
-/
structure PRGImageAcceptanceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  hInject : Function.Injective gen
  hLarge :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ seedLen
  hAccept :
    ∀ z : Core.BitVec seedLen,
      DagCircuit.eval W.C (encodeTotalAsPartial (gen z)) = true

/--
Slice-family provider for witness-indexed accepted-image certificates.
-/
abbrev prgImageAcceptanceAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      PRGImageAcceptanceAt W

/--
Turn an injective accepted image into the generic accepted-family weak
endpoint.
-/
noncomputable def acceptedFamilyCertificateAt_of_prgImageAcceptanceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PRGImageAcceptanceAt W) :
    AcceptedFamilyCertificateAt W := by
  classical
  let family : Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    (Finset.univ : Finset (Core.BitVec cert.seedLen)).image cert.gen
  refine
    { family := family
      hLarge := ?_
      hAccept := ?_ }
  · have hCard :
        family.card = 2 ^ cert.seedLen := by
      dsimp [family]
      calc
        ((Finset.univ : Finset (Core.BitVec cert.seedLen)).image cert.gen).card
            = (Finset.univ : Finset (Core.BitVec cert.seedLen)).card := by
                exact Finset.card_image_of_injective _ cert.hInject
        _ = Fintype.card (Core.BitVec cert.seedLen) := by simp
        _ = 2 ^ cert.seedLen := Counting.card_bitvec cert.seedLen
    exact lt_of_lt_of_eq cert.hLarge hCard.symm
  · intro g hg
    have hgMem :
        g ∈ (Finset.univ : Finset (Core.BitVec cert.seedLen)).image cert.gen := by
      simpa [family] using hg
    rcases Finset.mem_image.mp hgMem with ⟨z, _, hz⟩
    subst hz
    exact cert.hAccept z

/--
Structured-producer reduction: any accepted-image provider yields the generic
accepted-family weak endpoint.
-/
noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : prgImageAcceptanceAtProviderOnSlices F SizeBound) :
    acceptedFamilyCertificateAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact acceptedFamilyCertificateAt_of_prgImageAcceptanceAt (hCert n β ε W)

/--
Compiled weak-route bridge from PRG-image providers to the canonical
accepted-family version of Layer B.
-/
theorem smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : prgImageAcceptanceAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_certificateProvider F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider
      F SizeBound hCert)

/--
Bridge from witness-indexed DAG slack packages directly to Layer B with small
size condition:

`SmallDAGImpliesCoordinateLocalityStatement F SizeBound`.
-/
theorem smallDAGLocalityStatement_of_dagSlackPackageAtProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  intro n β ε C hSize hCorrect
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let cert := hPkg n β ε W
  refine ⟨cert.r.alive, ?_, ?_⟩
  · calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound (F.paramsOf n β).n (F.Tof n β) := by
              simp [F.hM, F.hIndex]
      _ = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
            simp [F.hT]
      _ < 2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - cert.r.alive.card) := cert.hSlack
  · intro x y hAgree
    exact cert.hLocal x y hAgree

/--
Compiled strong fallback route from witness-indexed shrinkage certificates on
slice DAG witnesses to Layer B encoded-coordinate locality.
-/
theorem smallDAGLocalityStatement_of_shrinkageCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : smallDAGWitnessShrinkageCertificateProviderOnSlices F SizeBound) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  exact smallDAGLocalityStatement_of_dagSlackPackageAtProvider F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider
      F SizeBound hCert)

/--
Compiled strong fallback route from witness-indexed restriction data on slice
DAG witnesses to Layer B encoded-coordinate locality.
-/
theorem smallDAGLocalityStatement_of_restrictionDataProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hData : smallDAGWitnessRestrictionCertificateDataProviderOnSlices F SizeBound) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  exact smallDAGLocalityStatement_of_shrinkageCertificateProvider F SizeBound
    (smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider
      F SizeBound hData)

/--
Compiled strong fallback route from separate semantic extraction and numeric
side-condition providers to Layer B encoded-coordinate locality.
-/
theorem smallDAGLocalityStatement_of_restrictionExtractionAndNumericProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hNumeric : smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  exact smallDAGLocalityStatement_of_restrictionDataProvider F SizeBound
    (smallDAGWitnessRestrictionCertificateDataProviderOnSlices_of_extractionAndNumericProvider
      F SizeBound hExtract hNumeric)

/--
Compiled strong fallback route from semantic surviving-cone certificates plus
numeric side conditions to Layer B encoded-coordinate locality.

This is the new precise abstraction boundary for the stronger route: the
remaining mathematical source theorem can target `SmallDAGWitnessSemanticConeCertificateAt`
instead of jumping directly to full restriction data.
-/
theorem smallDAGLocalityStatement_of_semanticConeAndNumericProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCone : smallDAGWitnessSemanticConeProviderOnSlices F SizeBound)
    (hNumeric :
      smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound
        (smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider
          F SizeBound hCone)) :
    SmallDAGImpliesCoordinateLocalityStatement F SizeBound := by
  exact smallDAGLocalityStatement_of_restrictionExtractionAndNumericProvider
    F SizeBound
    (smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider
      F SizeBound hCone)
    hNumeric

/--
Bridge from witness-indexed promise/value packages directly to the new
promise/value version of Layer B:

`SmallDAGImpliesPromiseValueLocalityStatement F SizeBound`.
-/
theorem smallDAGPromiseValueLocalityStatement_of_packageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesPromiseValueLocalityStatement F SizeBound := by
  intro n β ε C hSize hCorrect
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let cert := hPkg n β ε W
  refine ⟨cert.S, ?_, ?_⟩
  · calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound (F.paramsOf n β).n (F.Tof n β) := by
              simp [F.hM, F.hIndex]
      _ = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
            simp [F.hT]
      _ < 2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - cert.S.card) := cert.hSlack
  · intro x y hxYes hyNo hxValid hyValid hAgree
    exact cert.hLocal x y
      (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hxYes)
      (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hyNo)
      hxValid
      hyValid
      hAgree

/--
Bridge from witness-indexed promise-aware YES-centered source certificates
directly to the matching barrier-level one-sided endpoint.
-/
theorem smallDAGPromiseYesSubcubeStatement_of_certificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound := by
  intro n β ε C hSize hCorrect
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let cert := hCert n β ε W
  refine ⟨cert.yYes, ?_, cert.hValidYes, cert.S, ?_, ?_⟩
  · simpa [gapSliceOfParams, GapPartialMCSPPromise] using cert.hYes
  · calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound (F.paramsOf n β).n (F.Tof n β) := by
              simp [F.hM, F.hIndex]
      _ = Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) := by
            simp [F.hT]
      _ < 2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - cert.S.card) := cert.hSlack
  · intro z hzPromise hzValid hAgree
    exact cert.hAccept z
      ((by
        cases hzPromise with
        | inl hzYes =>
            exact Or.inl (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hzYes)
        | inr hzNo =>
            exact Or.inr (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hzNo)))
      hzValid
      hAgree

/--
Compiled route from the existing pairwise promise/value package provider to the
nearer-term one-sided YES-centered barrier endpoint.
-/
theorem smallDAGPromiseYesSubcubeStatement_of_packageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound := by
  exact smallDAGPromiseYesSubcubeStatement_of_certificateProvider F SizeBound
    (promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider
      F SizeBound hPkg)

/--
Compiled route from the stronger all-valid YES-subcube producer to the
nearer-term promise-aware YES-centered barrier endpoint.
-/
theorem smallDAGPromiseYesSubcubeStatement_of_yesSubcubeCertificateProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound := by
  exact smallDAGPromiseYesSubcubeStatement_of_certificateProvider F SizeBound
    (promiseYesSubcubeCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
      F SizeBound hCert)

/--
Direct weak-route closure from a generic accepted-family certificate provider.
-/
theorem noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : acceptedFamilyCertificateAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact no_small_dag_solver_of_acceptedFamilyCertificateAt W (hCert n β ε W)

/--
Direct closure from the stronger encoded-coordinate slack-package provider,
now routed through the generic accepted-family weak endpoint.
-/
theorem noSmallDAG_of_dagStableRestrictionSlackPackageAtProviderOnSlices_via_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider
      F SizeBound hPkg)

/--
Direct closure from the compiled shrinkage-certificate strong fallback route,
now routed through the generic accepted-family weak endpoint.
-/
theorem noSmallDAG_of_shrinkageCertificateProviderOnSlices_via_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : smallDAGWitnessShrinkageCertificateProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_dagStableRestrictionSlackPackageAtProviderOnSlices_via_acceptedFamily
    F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider
      F SizeBound hCert)

/--
Direct closure from the compiled restriction-data strong fallback route,
now routed through the generic accepted-family weak endpoint.
-/
theorem noSmallDAG_of_restrictionDataProviderOnSlices_via_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hData : smallDAGWitnessRestrictionCertificateDataProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_shrinkageCertificateProviderOnSlices_via_acceptedFamily
    F SizeBound
    (smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider
      F SizeBound hData)

/--
Direct closure from semantic restriction extraction plus numeric side-data,
now routed through the generic accepted-family weak endpoint.
-/
theorem noSmallDAG_of_restrictionExtractionAndNumericProviderOnSlices_via_acceptedFamily
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hNumeric : smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_dagStableRestrictionSlackPackageAtProviderOnSlices_via_acceptedFamily
    F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_restrictionExtractionAndNumericProvider
      F SizeBound hExtract hNumeric)

/--
Direct weak-route closure from an accepted-image certificate provider.
-/
theorem noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : prgImageAcceptanceAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider
      F SizeBound hCert)

/--
Direct weak-route closure from a one-sided YES-subcube certificate provider.

This now factors through the generic accepted-family weak endpoint.
-/
theorem noSmallDAG_of_yesSubcubeCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices F SizeBound
    (acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
      F SizeBound hCert)

end LowerBounds
end Pnp3
