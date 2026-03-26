import Complexity.Promise
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
One-sided YES-centered source certificate for the weaker promise/value route.

This is the intended theorem-minimal surface: one valid YES center plus value
coordinates `S` on which acceptance is stable across valid promise-relevant
completions.
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
  One-sided stability: every valid promise-relevant completion agreeing with
  `yYes` on `S` is accepted by the solver.
  -/
  hStable :
    ∀ z : Core.BitVec (Models.partialInputLen p),
      (z ∈ (GapPartialMCSPPromise p).Yes ∨ z ∈ (GapPartialMCSPPromise p).No) →
      ValidEncoding p z →
      AgreeOnValues (p := p) S yYes z →
        DagCircuit.eval W.C z = true

/--
Direct contradiction from the one-sided YES-subcube certificate.
-/
theorem no_small_dag_solver_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (cert : YesSubcubeCertificateAt W) :
    False := by
  have hCorrectPromise : SolvesPromise (GapPartialMCSPPromise p) (DagCircuit.eval W.C) := by
    constructor
    · intro x hx
      exact W.hCorrect.1 x (by simpa [gapSliceOfParams] using hx)
    · intro x hx
      exact W.hCorrect.2 x (by simpa [gapSliceOfParams] using hx)
  exact
    no_one_sided_value_local_function_solves_mcsp_of_countingSlack
      (p := p)
      (f := DagCircuit.eval W.C)
      (x_yes := cert.yYes)
      (S := cert.S)
      cert.hYes
      cert.hValidYes
      cert.hSlack
      cert.hStable
      hCorrectPromise

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
Direct weak-route closure from a one-sided YES-subcube certificate provider.

This bypasses the stronger pairwise locality interface and lands immediately at
the no-small-solver conclusion.
-/
theorem noSmallDAG_of_yesSubcubeCertificateAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : yesSubcubeCertificateAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact no_small_dag_solver_of_yesSubcubeCertificateAt W (hCert n β ε W)

end LowerBounds
end Pnp3
