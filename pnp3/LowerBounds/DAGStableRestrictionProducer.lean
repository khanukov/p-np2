import Mathlib.Data.Fintype.EquivFin
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
Gate-G1 (Route B / item 3) in its exact canonical shape.

This theorem is intentionally simple: it records that a uniform DAG-side
certificate provider is *exactly* what is needed to close

`∀ hDag, stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)`.

Keeping this theorem explicit avoids roadmap drift: any future source-side work
can target `dagStableRestrictionCertificateProvider` directly and immediately
land in the formal G1.3 statement without introducing new wrappers.
-/
theorem gateG1_routeB_stableRestrictionGoal_of_certificateProvider
    {p : GapPartialMCSPParams}
    (hCert : dagStableRestrictionCertificateProvider p) :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag) := by
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
Route-B source constructor from a concrete strict DAG witness plus a direct
half-support bound on the witness circuit at the canonical input length.

This is a **source-side theorem step** (not new endpoint plumbing):
it packages the mathematically direct argument that if the DAG output depends on
at most half of coordinates (`DagCircuit.support` bound), then the fixed gap
target is invariant under overwriting non-support coordinates.

The construction is intentionally in terms of `InPpolyDAG` so that the concrete
circuit family and correctness equation are available without extra unpacking.
-/
theorem gapPartialMCSP_eq_of_inPpolyDAG_eq_on_support
    {p : GapPartialMCSPParams}
    (w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p))
    {x y : Core.BitVec (Models.partialInputLen p)}
    (hAgree :
      ∀ i ∈ DagCircuit.support (w.family (Models.partialInputLen p)), x i = y i) :
    Models.gapPartialMCSP_Language p (Models.partialInputLen p) x =
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) y := by
  let C : DagCircuit (Models.partialInputLen p) := w.family (Models.partialInputLen p)
  have hEval : DagCircuit.eval C x = DagCircuit.eval C y := by
    simpa [C] using (DagCircuit.eval_eq_of_eq_on_support (C := C) (x := x) (y := y) hAgree)
  calc
    Models.gapPartialMCSP_Language p (Models.partialInputLen p) x
        = DagCircuit.eval C x := by
            simpa [C] using (w.correct (Models.partialInputLen p) x).symm
    _ = DagCircuit.eval C y := hEval
    _ = Models.gapPartialMCSP_Language p (Models.partialInputLen p) y := by
          simpa [C] using (w.correct (Models.partialInputLen p) y)

/--
Canonical overwrite-stability for one strict DAG witness along the complement
of its syntactic support at `partialInputLen p`.

This is the exact sensitivity-to-locality conversion used by Route-B: once we
freeze all non-support coordinates via `Restriction.ofVector`, the target
language value does not change.
-/
theorem gapPartialMCSP_stable_under_supportRestriction_of_inPpolyDAG
    {p : GapPartialMCSPParams}
    (w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p)) :
    let alive := DagCircuit.support (w.family (Models.partialInputLen p))
    let r : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
      Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
    ∀ x : Core.BitVec (Models.partialInputLen p),
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) (r.apply x) =
        Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := by
  intro alive r x
  apply gapPartialMCSP_eq_of_inPpolyDAG_eq_on_support (w := w)
  intro i hi
  simpa [r, alive] using Facts.LocalityLift.Restriction.apply_alive r x hi

/--
Exact remaining Route-B source obligation for closing
`dagStableRestrictionInvariantProvider p` without extra wrappers.
-/
abbrev gapPartialMCSP_supportHalfObligation (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    (DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
      Models.Partial.tableLen p.n / 2

noncomputable def dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf
    {p : GapPartialMCSPParams}
    (w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p))
    (hHalf :
      (DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
        Models.Partial.tableLen p.n / 2) :
    DAGStableRestrictionInvariantPackage
      (show ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) from ⟨w, trivial⟩) := by
  classical
  let C : DagCircuit (Models.partialInputLen p) := w.family (Models.partialInputLen p)
  let alive : Finset (Fin (Models.partialInputLen p)) := DagCircuit.support C
  let r : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
  refine
    { r := r
      hAliveSmall := ?_
      hLocalInvariant := ?_ }
  · simpa [C, alive] using hHalf
  · intro x y hAgree
    exact gapPartialMCSP_eq_of_inPpolyDAG_eq_on_support (w := w)
      (x := x) (y := y) (by
        intro i hi
        exact hAgree i (by simpa [r, alive] using hi))

/--
Task-1 reduction theorem (Route-B mainline):

If every strict DAG witness for `gapPartialMCSP_Language p` satisfies a
canonical half-support bound at input length `partialInputLen p`, then the full
Route-B source target `dagStableRestrictionInvariantProvider p` is closed.

This is not endpoint plumbing: it isolates exactly the remaining structural
source obligation to one uniform statement on concrete DAG witnesses.
-/
noncomputable def dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf
    {p : GapPartialMCSPParams}
    (hSupportHalf : gapPartialMCSP_supportHalfObligation p) :
    dagStableRestrictionInvariantProvider p := by
  classical
  intro hDag
  let w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p) :=
    Classical.choose hDag
  let hDag' : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := ⟨w, trivial⟩
  have hEq : hDag' = hDag := Subsingleton.elim _ _
  have inv : DAGStableRestrictionInvariantPackage hDag' :=
    dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf
      (p := p) w (hSupportHalf w)
  simpa [hEq] using inv

/--
Route-B closure in its final "no-extra-wrappers" form: once the canonical
support-half obligation is proved for `gapPartialMCSP_Language p`, the target
provider is obtained mechanically.
-/
noncomputable def dagStableRestrictionInvariantProvider_of_supportHalfObligation
    {p : GapPartialMCSPParams}
    (hSupportHalf : gapPartialMCSP_supportHalfObligation p) :
    dagStableRestrictionInvariantProvider p :=
  dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf
    (p := p) hSupportHalf

/--
Certificate-level Route-B closure from the same uniform strict-witness
half-support hypothesis.

This theorem lands directly in the source object consumed by
`gateG1_routeB_stableRestrictionGoal_of_certificateProvider`.
-/
noncomputable def dagStableRestrictionCertificateProvider_of_inPpolyDAG_supportHalf
    {p : GapPartialMCSPParams}
    (hSupportHalf :
      ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
        (DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
          Models.Partial.tableLen p.n / 2) :
    dagStableRestrictionCertificateProvider p := by
  intro hDag
  exact dagStableRestrictionCertificate_of_localInvariant hDag
    ((dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf
      (p := p) hSupportHalf) hDag)

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
Canonical extraction provider obtained directly from DAG support.

This is the mainline extraction choice for Route-A2 in the current sprint:
it needs no additional source theorem beyond the DAG witness itself.
-/
noncomputable def smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound := by
  intro n β ε W
  exact smallDAGWitnessRestrictionExtractionAt_of_support W

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
Numeric side-data family specialized to the support-based extraction mainline.

This isolates the only remaining Route-A2 source obligation once extraction is
fixed as `smallDAGWitnessRestrictionExtractionAt_of_support`.
-/
abbrev smallDAGWitnessSupportNumericDataProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      SmallDAGWitnessRestrictionNumericDataAt
        (smallDAGWitnessRestrictionExtractionAt_of_support W)

/--
Route-A2 component (Polylog): source-side bound specialized to the support
extraction.
-/
abbrev supportAliveBoundPolylogProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen
            (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)))

/--
Route-A2 component (Quarter): source-side quarter-input bound specialized to the
support extraction.
-/
abbrev supportAliveBoundQuarterProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4

/--
Route-A2 component (SmallEnough): source-side local-parameter smallness bound
specialized to the support extraction.
-/
abbrev supportSmallEnoughProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen
            (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β))
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
              (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card.succ
        , ℓ := (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth }

/--
Arithmetic form of the Route-A2 SmallEnough component stated directly via
`DagCircuit.support`.

This is equivalent in strength to `supportSmallEnoughProviderOnSlices`, but
often easier to target from source-side size/depth estimates before rewriting
through `smallDAGWitnessRestrictionExtractionAt_of_support`.
-/
abbrev supportSmallEnoughArithmeticProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      (DagCircuit.support W.C).card *
        (Nat.log2
            ((ThirdPartyFacts.toFactsGeneralSolverPartial
                (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
              ((DagCircuit.support W.C).card.succ) + 2) +
          (ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1)
        ≤
        Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2

/--
Canonical family-level factor bound on `ppolyDAGSizeBoundOnSlices`.

For witnesses constrained by the canonical `ppolyDAG` size surface, the local
factor

`log₂(M + 2) + depth + 1`

is bounded by replacing witness size with the corresponding canonical
`polyBound` (and using `depth = 0` for DAG witnesses in
`generalSolverOfSmallDAGWitnessOnSlice`).
-/
theorem factorBound_onCanonicalPpolySizeSurface
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : SmallDAGWitnessOnSlice
        (F.paramsOf n β)
        (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
        Nat.log2
            ((ThirdPartyFacts.toFactsGeneralSolverPartial
                (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
              ((DagCircuit.support W.C).card.succ) + 2) +
          (ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1
          ≤
        Nat.log2
            ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
              ((DagCircuit.support W.C).card.succ) + 2) + 1 := by
  intro n β ε W
  have hSize :
      DagCircuit.size W.C ≤ (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) := by
    simpa [ppolyDAGSizeBoundOnSlices] using W.hSize
  have hMul :
      DagCircuit.size W.C * (DagCircuit.support W.C).card.succ ≤
        (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
          (DagCircuit.support W.C).card.succ := by
    exact Nat.mul_le_mul_right _ hSize
  have hAdd :
      DagCircuit.size W.C * (DagCircuit.support W.C).card.succ + 2 ≤
        (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
          (DagCircuit.support W.C).card.succ + 2 := by
    exact Nat.add_le_add_right hMul 2
  have hLogNat :
      Nat.log 2 (DagCircuit.size W.C * (DagCircuit.support W.C).card.succ + 2) ≤
        Nat.log 2
          ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
            (DagCircuit.support W.C).card.succ + 2) := by
    exact Nat.log_monotone hAdd
  have hLog :
      Nat.log2 (DagCircuit.size W.C * (DagCircuit.support W.C).card.succ + 2) ≤
        Nat.log2
          ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
            (DagCircuit.support W.C).card.succ + 2) := by
    simpa [Nat.log2_eq_log_two] using hLogNat
  simpa [generalSolverOfSmallDAGWitnessOnSlice, ThirdPartyFacts.toFactsGeneralSolverPartial]
    using Nat.add_le_add_right hLog 1

/--
Canonical family-budget inequality for `ppolyDAGSizeBoundOnSlices`.

This theorem closes the exact witness-indexed budget premise consumed by
`supportSmallEnoughArithmeticProviderOnSlices_onCanonicalBound_of_factorBudget`:

`support.card * (canonical-factor) ≤ inputLen/2`.

It isolates the arithmetic target on the canonical size surface in one place:
if source-side work can establish

1. a support half-bound, and
2. the canonical factor cap `≤ 1`,

then the required canonical budget inequality follows uniformly for every
witness on `ppolyDAGSizeBoundOnSlices`.
-/
theorem canonicalFactorBudget_onPpolyDAGSizeBoundOnSlices_of_supportHalf_and_factorOne
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (hSupportHalf :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2)
    (hCanonicalFactorOne :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          Nat.log2
              ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                ((DagCircuit.support W.C).card.succ) + 2) + 1
            ≤ 1) :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : SmallDAGWitnessOnSlice
        (F.paramsOf n β)
        (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card *
            (Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1)
            ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2 := by
  intro n β ε W
  have hMul :
      (DagCircuit.support W.C).card *
          (Nat.log2
              ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                ((DagCircuit.support W.C).card.succ) + 2) + 1)
        ≤
      (DagCircuit.support W.C).card := by
    have hMul' := Nat.mul_le_mul_left (DagCircuit.support W.C).card
      (hCanonicalFactorOne n β ε W)
    simpa using hMul'
  exact le_trans hMul (hSupportHalf n β ε W)

/--
Sanity lower bound for the canonical factor term.

This formalizes an important arithmetic obstruction: on natural numbers the
canonical factor

`log2 (polyBound * (support.card.succ) + 2) + 1`

is always at least `2` (because the inner argument is `≥ 2`), so a hypothesis
of the form `... ≤ 1` is inconsistent.
-/
theorem canonicalFactor_two_le_onPpolyDAGSizeBoundOnSlices
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : SmallDAGWitnessOnSlice
        (F.paramsOf n β)
        (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          2 ≤ Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1 := by
  intro n β ε W
  let x :=
    (hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
      ((DagCircuit.support W.C).card.succ) + 2
  have hx_ne_zero : x ≠ 0 := by
    dsimp [x]
    omega
  have hx_two_le : 2 ≤ x := by
    dsimp [x]
    omega
  have hlog_one_le : 1 ≤ Nat.log2 x := by
    exact (Nat.le_log2 hx_ne_zero).2 (by simpa using hx_two_le)
  have htwo_le : 1 + 1 ≤ Nat.log2 x + 1 := Nat.add_le_add_right hlog_one_le 1
  simpa [x] using htwo_le

/--
Consistency corollary: the canonical factor cannot satisfy `≤ 1`.
-/
theorem not_canonicalFactorOne_onPpolyDAGSizeBoundOnSlices
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β))) :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : SmallDAGWitnessOnSlice
        (F.paramsOf n β)
        (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          ¬ (Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1
                ≤ 1) := by
  intro n β ε W hFactorOne
  have hTwoLe :=
    canonicalFactor_two_le_onPpolyDAGSizeBoundOnSlices F hInDag n β ε W
  exact Nat.not_succ_le_self 1 (le_trans hTwoLe hFactorOne)

/--
Arithmetic Route-A2 closure on canonical `ppolyDAG` size surface.

This theorem isolates the exact remaining source-side arithmetic target:
prove a budget inequality against the canonical factor expression built from
`polyBound`, then `supportSmallEnoughArithmeticProviderOnSlices` follows for all
canonical-family witnesses.
-/
theorem supportSmallEnoughArithmeticProviderOnSlices_onCanonicalBound_of_factorBudget
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (hBudget :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card *
            (Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1)
            ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2) :
    supportSmallEnoughArithmeticProviderOnSlices F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro n β ε W
  have hFactor :
      Nat.log2
          ((ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
            ((DagCircuit.support W.C).card.succ) + 2) +
        (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1
        ≤
      Nat.log2
          ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
            ((DagCircuit.support W.C).card.succ) + 2) + 1 :=
    factorBound_onCanonicalPpolySizeSurface F hInDag n β ε W
  have hMul :
      (DagCircuit.support W.C).card *
          (Nat.log2
              ((ThirdPartyFacts.toFactsGeneralSolverPartial
                  (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
                ((DagCircuit.support W.C).card.succ) + 2) +
            (ThirdPartyFacts.toFactsGeneralSolverPartial
                (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1)
        ≤
      (DagCircuit.support W.C).card *
          (Nat.log2
              ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                ((DagCircuit.support W.C).card.succ) + 2) + 1) := by
    exact Nat.mul_le_mul_left _ hFactor
  exact le_trans hMul (hBudget n β ε W)

/--
Convert the direct arithmetic SmallEnough statement on support to the canonical
`supportSmallEnoughProviderOnSlices` form.
-/
theorem supportSmallEnoughProviderOnSlices_of_supportArithmetic
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hArith : supportSmallEnoughArithmeticProviderOnSlices F SizeBound) :
    supportSmallEnoughProviderOnSlices F SizeBound := by
  intro n β ε W
  simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
    smallDAGWitnessRestrictionExtractionAt_of_support] using hArith n β ε W

/--
Convenient sufficient condition for `supportSmallEnoughProviderOnSlices`.

If source-side proofs give:
1. a quarter bound on support cardinality, and
2. a uniform bound `log₂(M+2) + depth + 1 ≤ 1`,
then SmallEnough follows immediately (`ℓ * factor ≤ ℓ ≤ n/4 ≤ n/2`).
-/
theorem supportSmallEnoughProviderOnSlices_of_supportQuarter_and_factorOne
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hQuarter : supportAliveBoundQuarterProviderOnSlices F SizeBound)
    (hFactorOne :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          Nat.log2
              ((ThirdPartyFacts.toFactsGeneralSolverPartial
                  (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
                ((DagCircuit.support W.C).card.succ) + 2) +
            (ThirdPartyFacts.toFactsGeneralSolverPartial
                (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1
            ≤ 1) :
    supportSmallEnoughProviderOnSlices F SizeBound := by
  refine supportSmallEnoughProviderOnSlices_of_supportArithmetic F SizeBound ?_
  intro n β ε W
  have hq : (DagCircuit.support W.C).card ≤
      Facts.LocalityLift.inputLen
        (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4 := by
    simpa [smallDAGWitnessRestrictionExtractionAt_of_support] using hQuarter n β ε W
  have hf := hFactorOne n β ε W
  have hMul : (DagCircuit.support W.C).card *
      (Nat.log2
          ((ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
            ((DagCircuit.support W.C).card.succ) + 2) +
        (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1)
      ≤ (DagCircuit.support W.C).card := by
    have hMul' := Nat.mul_le_mul_left (DagCircuit.support W.C).card hf
    simpa using hMul'
  have hQuarterHalf :
      Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4
        ≤
      Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2 := by
    omega
  exact le_trans hMul (le_trans hq hQuarterHalf)

/--
Build support-based numeric side data from the three component obligations.

This theorem is the "one-by-one closure" point for the chosen Route-A2 mainline:
once Polylog, Quarter, and SmallEnough are each proved separately, they combine
into the exact numeric object consumed downstream.
-/
theorem smallDAGWitnessSupportNumericDataAt_of_components
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hPolylog :
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)))
    (hQuarter :
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4)
    (hSmallEnough :
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
              (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card.succ
        , ℓ := (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth }) :
    SmallDAGWitnessRestrictionNumericDataAt
      (smallDAGWitnessRestrictionExtractionAt_of_support W) := by
  exact
    { hBoundPolylog := hPolylog
      hBoundQuarter := hQuarter
      hSmallEnough := hSmallEnough }

/--
Assemble the support-numeric family from the three component families.
-/
theorem smallDAGWitnessSupportNumericDataProviderOnSlices_of_components
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPolylog : supportAliveBoundPolylogProviderOnSlices F SizeBound)
    (hQuarter : supportAliveBoundQuarterProviderOnSlices F SizeBound)
    (hSmallEnough : supportSmallEnoughProviderOnSlices F SizeBound) :
    smallDAGWitnessSupportNumericDataProviderOnSlices F SizeBound := by
  intro n β ε W
  exact smallDAGWitnessSupportNumericDataAt_of_components W
    (hPolylog n β ε W)
    (hQuarter n β ε W)
    (hSmallEnough n β ε W)

/--
Polylog component from a direct bound on DAG output-support cardinality.
-/
theorem supportAliveBoundPolylogProviderOnSlices_of_supportCardPolylog
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSupportPolylog :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.polylogBudget
              (Facts.LocalityLift.inputLen
                (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)))) :
    supportAliveBoundPolylogProviderOnSlices F SizeBound := by
  intro n β ε W
  simpa [smallDAGWitnessRestrictionExtractionAt_of_support] using hSupportPolylog n β ε W

/--
Quarter component from a direct bound on DAG output-support cardinality.
-/
theorem supportAliveBoundQuarterProviderOnSlices_of_supportCardQuarter
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSupportQuarter :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4) :
    supportAliveBoundQuarterProviderOnSlices F SizeBound := by
  intro n β ε W
  simpa [smallDAGWitnessRestrictionExtractionAt_of_support] using hSupportQuarter n β ε W

/--
Canonical Route-A2 small-enough closure from the two arithmetic source inputs.

This is the direct composition requested by the current sprint:

`supportHalf + canonicalFactor≤1` ⇒ budget inequality
⇒ arithmetic SmallEnough provider
⇒ `supportSmallEnoughProviderOnSlices`.
-/
theorem supportSmallEnoughProviderOnSlices_onCanonicalBound_of_supportHalf_and_factorOne
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (hSupportHalf :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2)
    (hCanonicalFactorOne :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          Nat.log2
              ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                ((DagCircuit.support W.C).card.succ) + 2) + 1
            ≤ 1) :
    supportSmallEnoughProviderOnSlices F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  have hBudget :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card *
            (Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1)
            ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2 :=
    canonicalFactorBudget_onPpolyDAGSizeBoundOnSlices_of_supportHalf_and_factorOne
      F hInDag hSupportHalf hCanonicalFactorOne
  have hArith :
      supportSmallEnoughArithmeticProviderOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag) :=
    supportSmallEnoughArithmeticProviderOnSlices_onCanonicalBound_of_factorBudget
      F hInDag hBudget
  exact supportSmallEnoughProviderOnSlices_of_supportArithmetic
    F (ppolyDAGSizeBoundOnSlices F hInDag) hArith

/--
Canonical support-numeric provider assembly from support bounds plus the
`supportHalf + canonicalFactor≤1` arithmetic closure.

This theorem closes the next remaining Route-A2 node in one step:
it first derives `supportSmallEnoughProviderOnSlices` by the canonical arithmetic
path above, then combines it with support-card Polylog/Quarter bounds into the
full `smallDAGWitnessSupportNumericDataProviderOnSlices`.
-/
theorem smallDAGWitnessSupportNumericDataProviderOnSlices_onCanonicalBound_of_supportBounds_and_factorOne
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (hSupportPolylog :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.polylogBudget
              (Facts.LocalityLift.inputLen
                (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β))))
    (hSupportQuarter :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4)
    (hSupportHalf :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          (DagCircuit.support W.C).card ≤
            Facts.LocalityLift.inputLen
              (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2)
    (hCanonicalFactorOne :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β)
          (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
          Nat.log2
              ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                ((DagCircuit.support W.C).card.succ) + 2) + 1
            ≤ 1) :
    smallDAGWitnessSupportNumericDataProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  have hPolylog :
      supportAliveBoundPolylogProviderOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag) :=
    supportAliveBoundPolylogProviderOnSlices_of_supportCardPolylog
      F (ppolyDAGSizeBoundOnSlices F hInDag) hSupportPolylog
  have hQuarter :
      supportAliveBoundQuarterProviderOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag) :=
    supportAliveBoundQuarterProviderOnSlices_of_supportCardQuarter
      F (ppolyDAGSizeBoundOnSlices F hInDag) hSupportQuarter
  have hSmallEnough :
      supportSmallEnoughProviderOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag) :=
    supportSmallEnoughProviderOnSlices_onCanonicalBound_of_supportHalf_and_factorOne
      F hInDag hSupportHalf hCanonicalFactorOne
  exact smallDAGWitnessSupportNumericDataProviderOnSlices_of_components
    F (ppolyDAGSizeBoundOnSlices F hInDag) hPolylog hQuarter hSmallEnough

/--
Convert support-specialized numeric side data into the generic numeric-provider
interface expected by the Route-A2 extraction+numeric compiler.
-/
theorem smallDAGWitnessRestrictionNumericDataProviderOnSlices_of_supportNumeric
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hNumeric : smallDAGWitnessSupportNumericDataProviderOnSlices F SizeBound) :
    smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound
      (smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support F SizeBound) := by
  intro n β ε W
  simpa [smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support] using
    (hNumeric n β ε W)

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
Provider lift of the support-half strong fallback.

This is the family-level version of
`dagStableRestrictionSlackPackageAt_of_supportHalfBound`: if every slice witness
has support at most half the truth-table length, we obtain a full provider of
encoded-coordinate slack packages.
-/
noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_supportHalfBound
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSupportHalf :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (DagCircuit.support W.C).card ≤ Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    dagStableRestrictionSlackPackageAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact dagStableRestrictionSlackPackageAt_of_supportHalfBound W (hSupportHalf n β ε W)

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
Arithmetic-only target budget for Q2-style counting slack.

`requiredComplementBudget p` is the **least** natural number `b` such that
`circuitCountBound p.n (p.sNO - 1) < 2^b`.

Why this helps:
* semantic arguments only need to produce lower bounds on `tableLen - |S|`;
* counting arithmetic is centralized in one reusable threshold;
* "enough complement" becomes a concrete inequality target:
  `requiredComplementBudget p ≤ tableLen - |S|`.
-/
theorem exists_countingSlack_budget (p : GapPartialMCSPParams) :
    ∃ b : Nat, Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ b := by
  let c := Models.circuitCountBound p.n (p.sNO - 1)
  refine ⟨c + 1, ?_⟩
  have hbase : c < 2 ^ c := by
    simpa using (Nat.lt_two_pow_self (n := c))
  have hmono : 2 ^ c ≤ 2 ^ (c + 1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ c)
  exact lt_of_lt_of_le hbase hmono

/--
Least complement budget sufficient for counting slack.
-/
noncomputable def requiredComplementBudget (p : GapPartialMCSPParams) : Nat :=
  Nat.find (exists_countingSlack_budget p)

/--
By construction, `requiredComplementBudget p` already satisfies the counting
inequality.
-/
theorem countingSlack_at_requiredComplementBudget (p : GapPartialMCSPParams) :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ requiredComplementBudget p :=
  Nat.find_spec (exists_countingSlack_budget p)

/--
Generic arithmetic bridge: any complement budget at least the required threshold
implies counting slack.

This theorem is intentionally semantic-agnostic: it only talks about cardinal
arithmetic (`tableLen - |S|`) and the precomputed threshold.
-/
theorem countingSlack_of_complementBudget_ge
    {p : GapPartialMCSPParams}
    (S : ValueCoordinateSet p)
    (hBudget : requiredComplementBudget p ≤ Models.Partial.tableLen p.n - S.card) :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (Models.Partial.tableLen p.n - S.card) := by
  have hReq : Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ requiredComplementBudget p :=
    countingSlack_at_requiredComplementBudget p
  have hMono :
      2 ^ requiredComplementBudget p ≤ 2 ^ (Models.Partial.tableLen p.n - S.card) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hBudget
  exact lt_of_lt_of_le hReq hMono

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
Restricted-model quantitative foothold (value-supported alive set):
the induced semantic set from the strong restriction package already has
enough complement budget for the arithmetic threshold
`requiredComplementBudget p`.
-/
theorem requiredComplementBudget_le_of_dagStableRestrictionSlackPackageAt_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : DAGStableRestrictionSlackPackageAt W)
    (hValueAlive :
      ∀ i ∈ cert.r.alive,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    requiredComplementBudget p ≤
      Models.Partial.tableLen p.n -
        (promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported
          cert hValueAlive).S.card := by
  exact Nat.find_min' (exists_countingSlack_budget p)
    (promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported
      cert hValueAlive).hSlack

/--
Restricted-model weak-route foothold: if the DAG output support is both
value-supported and at most half the truth-table length, then it already
yields the promise/value locality package.

This is stronger than the accepted-family contradiction produced by the strong
support sprint: it lands directly in the chosen weak-route producer API.
-/
noncomputable def promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2)
    (hValueSupport :
      ∀ i ∈ DagCircuit.support W.C,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    PromiseValueLocalityPackageAt W := by
  classical
  let S : ValueCoordinateSet p :=
    Finset.univ.filter (fun j => tableValPos j ∈ DagCircuit.support W.C)
  have hSCard :
      S.card ≤ (DagCircuit.support W.C).card := by
    have hImgSub : Finset.image tableValPos S ⊆ DagCircuit.support W.C := by
      intro i hi
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact hj
    have hCardImage :
        S.card = (Finset.image tableValPos S).card := by
      rw [Finset.card_image_of_injective S tableValPos_injective]
    calc
      S.card = (Finset.image tableValPos S).card := hCardImage
      _ ≤ (DagCircuit.support W.C).card := Finset.card_le_card hImgSub
  refine
    { S := S
      hSlack := ?_
      hLocal := ?_ }
  · have hExpMono :
        Models.Partial.tableLen p.n / 2 ≤ Models.Partial.tableLen p.n - S.card := by
      omega
    exact lt_of_lt_of_le p.circuit_bound_ok
      (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono)
  · intro x y _hxYes _hyNo _hxValid _hyValid hAgree
    apply DagCircuit.eval_eq_of_eq_on_support
    intro i hi
    obtain ⟨j, rfl⟩ := hValueSupport i hi
    exact hAgree j (by simp [S, hi])

/--
Restricted-model quantitative foothold (support-half + value-supported):
the semantic set produced by this route already satisfies the stronger target
`requiredComplementBudget p ≤ tableLen - |S|`.
-/
theorem requiredComplementBudget_le_of_supportHalfBound_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2)
    (hValueSupport :
      ∀ i ∈ DagCircuit.support W.C,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    requiredComplementBudget p ≤
      Models.Partial.tableLen p.n -
        (promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported
          W hSupportHalf hValueSupport).S.card := by
  exact Nat.find_min' (exists_countingSlack_budget p)
    (promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported
      W hSupportHalf hValueSupport).hSlack

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
One-hop strong-fallback compiler from support-half bounds.

This theorem is the direct positive node currently available in this file:

`supportHalf family`
`→ dagStableRestrictionSlackPackageAtProviderOnSlices`
`→ SmallDAGImpliesAcceptedFamilyStatement`.
-/
theorem smallDAGAcceptedFamilyStatement_of_supportHalfBound
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSupportHalf :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (DagCircuit.support W.C).card ≤ Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    SmallDAGImpliesAcceptedFamilyStatement F SizeBound := by
  exact smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider
    F SizeBound
    (dagStableRestrictionSlackPackageAtProviderOnSlices_of_supportHalfBound
      F SizeBound hSupportHalf)

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
Branch-A strengthening target for Q1:

`PromiseYesAcceptanceInvariantAt` plus an explicit nontriviality witness
`S ≠ Finset.univ`.

This is the exact formal shape needed to avoid the strict-Q1 full-set collapse
diagnosed by `no_sameSetSlack_of_strictDAGSemantics`.
-/
structure PromiseYesAcceptanceInvariantAtNontrivialS
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  inv : PromiseYesAcceptanceInvariantAt W
  hS_nontrivial : inv.S ≠ Finset.univ

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
Arithmetic-to-Q2 compiler at fixed witness:
if the semantic invariant `inv` already has enough complement budget with
respect to `requiredComplementBudget p`, then counting slack on the same `S`
follows automatically.
-/
theorem slack_on_acceptanceInvariant_of_requiredComplementBudget
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (inv : PromiseYesAcceptanceInvariantAt W)
    (hBudget :
      requiredComplementBudget p ≤ Models.Partial.tableLen p.n - inv.S.card) :
    Models.circuitCountBound p.n (p.sNO - 1) <
      2 ^ (Models.Partial.tableLen p.n - inv.S.card) :=
  countingSlack_of_complementBudget_ge inv.S hBudget

/--
Compile semantic Q1 + required-budget inequality directly to the operational
promise-YES certificate.
-/
def promiseYesSubcubeCertificateAt_of_acceptanceInvariant_and_requiredComplementBudget
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (inv : PromiseYesAcceptanceInvariantAt W)
    (hBudget :
      requiredComplementBudget p ≤ Models.Partial.tableLen p.n - inv.S.card) :
    PromiseYesSubcubeCertificateAt W :=
  promiseYesSubcubeCertificateAt_of_acceptanceInvariant
    (W := W)
    inv
    (slack_on_acceptanceInvariant_of_requiredComplementBudget inv hBudget)

/--
Split form of the current mainline source objective at one witness:

1. semantic one-sided YES-centered forcing (`inv`);
2. quantitative slack on the **same** semantic coordinate set (`hSlackOnInvS`).

This packages the Q1/Q2 theorem-sprint decomposition explicitly in the API so
source-side proofs can target each half independently and still compose
mechanically to `PromiseYesSubcubeCertificateAt`.
-/
structure PromiseYesSourceDecompositionAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  /-- Semantic one-sided forcing component (Q1 target). -/
  inv : PromiseYesAcceptanceInvariantAt W
  /-- Quantitative slack on the same semantic coordinates (Q2 target). -/
  hSlackOnInvS :
    Models.circuitCountBound p.n (p.sNO - 1) <
      2 ^ (Models.Partial.tableLen p.n - inv.S.card)

/--
Mechanical compilation from the split Q1/Q2 source package to the operational
promise-YES weak-route certificate used by counting closure.
-/
def promiseYesSubcubeCertificateAt_of_sourceDecomposition
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (src : PromiseYesSourceDecompositionAt W) :
    PromiseYesSubcubeCertificateAt W :=
  promiseYesSubcubeCertificateAt_of_acceptanceInvariant
    (W := W)
    src.inv
    src.hSlackOnInvS

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
Slice-family provider for semantic one-sided YES-centered forcing certificates
(Q1-level provider target).
-/
abbrev promiseYesAcceptanceInvariantAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      PromiseYesAcceptanceInvariantAt W

/--
Branch-A provider target: semantic acceptance invariants with an explicit
nontrivial coordinate set (`S ≠ Finset.univ`) on every slice witness.
-/
abbrev promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      PromiseYesAcceptanceInvariantAtNontrivialS W

/--
Alternative positive-source route package (non-full-`S` branch) with explicit
formula-track export hooks.

This object is intentionally "bridge-shaped":

1. it carries a nontrivial-`S` source provider on slices (the new positive
   branch target);
2. it also carries a formula support-bounds witness so this route can be wired
   directly into the existing formula-side magnification API.

The second field is not derived automatically from the first one in current
theory; we keep both fields explicit so future source theorems can populate this
package without changing downstream signatures.
-/
structure NontrivialSAlternativeProducerRoute where
  /-- Non-full-`S` source-side provider on slices. -/
  nontrivialSProvider :
    ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices F SizeBound
  /-- Formula-track export hook for current magnification entrypoints. -/
  supportBounds : Magnification.FormulaSupportRestrictionBoundsPartial

/--
Projection: export the route package to the existing formula support-bounds API.
-/
def formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute
    (route : NontrivialSAlternativeProducerRoute) :
    Magnification.FormulaSupportRestrictionBoundsPartial :=
  route.supportBounds

/--
Projection: export the same route package to
`FormulaRestrictionCertificateDataPartial` through the existing constructive
builder.
-/
noncomputable def formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute
    (route : NontrivialSAlternativeProducerRoute) :
    Magnification.FormulaRestrictionCertificateDataPartial :=
  Magnification.formulaRestrictionCertificateData_of_supportBounds route.supportBounds

/--
Strict DAG-semantics Q1 provider on slices.

Family-level lift of `promiseYesAcceptanceInvariantAt_of_strictDAGSemantics`:
no additional source-side package assumptions are required beyond the witness
semantics already carried by `SmallDAGWitnessOnSlice`.
-/
def promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound := by
  intro n β ε W
  let cert : PromiseYesDecisionCertificateAt W :=
    promiseYesDecisionCertificateAt_fullValueCoordinates W
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
Slice-family provider for quantitative slack on the same semantic coordinate set
produced by a semantic provider (Q2-level provider target).
-/
abbrev promiseYesSlackOnInvariantProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) <
        2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - (hInv n β ε W).S.card)

/--
Provider-level quantitative target in threshold form:
the semantic provider's coordinate set has complement budget at least
`requiredComplementBudget` on each witness.
-/
abbrev promiseYesRequiredBudgetOnInvariantProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      requiredComplementBudget (F.paramsOf n β) ≤
        Models.Partial.tableLen (F.paramsOf n β).n - (hInv n β ε W).S.card

/--
Arithmetic compiler from threshold-budget provider to same-set slack provider.
-/
theorem promiseYesSlackOnInvariantProviderOnSlices_of_requiredBudgetProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound)
    (hBudget : promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound hInv) :
    promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv := by
  intro n β ε W
  exact countingSlack_of_complementBudget_ge (hInv n β ε W).S (hBudget n β ε W)

/--
Compile separate semantic and quantitative source providers into the existing
provider surface `promiseYesSubcubeCertificateAtProviderOnSlices`.
-/
def promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound)
    (hSlack : promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv) :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
        PromiseYesSubcubeCertificateAt W := by
  intro n β ε W
  exact promiseYesSubcubeCertificateAt_of_sourceDecomposition
    { inv := hInv n β ε W
      hSlackOnInvS := hSlack n β ε W }

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
Strict DAG-semantics Q1 closure at one witness.

From only a correct small-DAG witness on one slice, we can construct the
acceptance-only invariant `PromiseYesAcceptanceInvariantAt`.

This closes the semantic-existence target (N1/Q1).  The construction is
intentionally semantic-only and uses the full value-coordinate set via
`promiseYesDecisionCertificateAt_fullValueCoordinates`; quantitative small-set
slack remains a separate N2/Q2 task.
-/
def promiseYesAcceptanceInvariantAt_of_strictDAGSemantics
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    PromiseYesAcceptanceInvariantAt W := by
  exact promiseYesAcceptanceInvariantAt_of_decisionCertificate
    (promiseYesDecisionCertificateAt_fullValueCoordinates W)

/--
Arithmetic helper: for valid gap parameters, the counting upper bound at
threshold `sNO - 1` is at least `2`.

This is used to make the N2 status precise for the current strict-semantics Q1
construction: with `S = Finset.univ`, the slack RHS is exactly `1`, so the
required strict inequality cannot hold.
-/
theorem circuitCountBound_two_le_of_gapParams
    (p : GapPartialMCSPParams) :
    2 ≤ Models.circuitCountBound p.n (p.sNO - 1) := by
  have hsYES1 : 2 ≤ p.sYES + 1 := by
    exact Nat.succ_le_succ p.sYES_pos
  have hsNO2 : 2 ≤ p.sNO := le_trans hsYES1 p.gap_ok
  have hsPredPos : 0 < p.sNO - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hsNO2)
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsPredPos) with ⟨k, hk⟩
  rw [hk, Models.circuitCountBound]
  -- `f (k+1) = A + 2` for a nonnegative `A`.
  exact Nat.le_add_left 2 (2 * (Models.circuitCountBound p.n k) ^ 2 + 2 * Models.circuitCountBound p.n k + p.n)

/--
`requiredComplementBudget` is strictly positive for valid gap parameters.

Intuition: `circuitCountBound p.n (p.sNO - 1)` is always at least `2`, while by
definition of `requiredComplementBudget` we have strict inequality

`circuitCountBound ... < 2 ^ requiredComplementBudget`.

So budget `0` (RHS `= 1`) is impossible.
-/
theorem requiredComplementBudget_pos (p : GapPartialMCSPParams) :
    1 ≤ requiredComplementBudget p := by
  have hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ requiredComplementBudget p :=
    countingSlack_at_requiredComplementBudget p
  have hCountGeTwo : 2 ≤ Models.circuitCountBound p.n (p.sNO - 1) :=
    circuitCountBound_two_le_of_gapParams p
  have hNeZero : requiredComplementBudget p ≠ 0 := by
    intro hZero
    have hlt1 : Models.circuitCountBound p.n (p.sNO - 1) < 1 := by
      simpa [hZero] using hSlack
    exact Nat.not_lt_of_ge (le_trans (by decide : 1 ≤ 2) hCountGeTwo) hlt1
  exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hNeZero)

/--
For the strict-semantics Q1 invariant, the chosen semantic coordinate set is
exactly the full value-coordinate set.
-/
private lemma strictDAGSemantics_S_eq_univ_private
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S = Finset.univ := by
  rfl

/--
Public Branch-A diagnostic: the current strict-Q1 constructor always chooses
`S = Finset.univ`.
-/
theorem strictDAGSemantics_S_eq_univ
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S = Finset.univ := by
  exact strictDAGSemantics_S_eq_univ_private W

/--
Corollary: the strict-Q1 constructor cannot satisfy a nontrivial-set predicate
on its own semantic coordinate set.
-/
theorem strictDAGSemantics_nontrivialS_false
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    ((promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S ≠ Finset.univ) → False := by
  intro hNontrivial
  exact hNontrivial (strictDAGSemantics_S_eq_univ W)

/--
N2 impossibility theorem for the current strict-semantics Q1 construction.

The semantic invariant from `promiseYesAcceptanceInvariantAt_of_strictDAGSemantics`
uses `S = Finset.univ`, so the quantitative RHS becomes `2^0 = 1`.  But
`circuitCountBound p.n (p.sNO - 1) ≥ 2` for valid gap parameters, hence strict
slack cannot hold on this same set.
-/
theorem no_sameSetSlack_of_strictDAGSemantics
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    ¬ Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card) := by
  have hS : (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card =
      Models.Partial.tableLen p.n := by
    simpa [strictDAGSemantics_S_eq_univ_private W]
  have hRhs : 2 ^ (Models.Partial.tableLen p.n -
      (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card) = 1 := by
    simpa [hS]
  intro hSlack
  have hge2 : 2 ≤ Models.circuitCountBound p.n (p.sNO - 1) :=
    circuitCountBound_two_le_of_gapParams p
  have hlt1 : Models.circuitCountBound p.n (p.sNO - 1) < 1 := by
    simpa [hRhs] using hSlack
  exact Nat.not_lt_of_ge (le_trans (by decide : 1 ≤ 2) hge2) hlt1

/--
Pointwise negation of the strict-mainline required-budget target on any witness.

For `promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W` we have
`S = univ`, hence `tableLen - S.card = 0`. But
`requiredComplementBudget` is strictly positive, so the inequality

`requiredComplementBudget ≤ tableLen - S.card`

cannot hold at this witness.
-/
theorem not_requiredBudget_on_strictDAGSemantics_atWitness
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    ¬ (requiredComplementBudget p ≤
        Models.Partial.tableLen p.n -
          (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card) := by
  have hS :
      (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card =
        Models.Partial.tableLen p.n := by
    simpa [strictDAGSemantics_S_eq_univ_private W]
  intro hBudget
  have hReqPos : 1 ≤ requiredComplementBudget p := requiredComplementBudget_pos p
  have hReqZero : requiredComplementBudget p ≤ 0 := by
    simpa [hS] using hBudget
  exact Nat.not_succ_le_zero 0 (le_trans hReqPos hReqZero)

/--
Canonical-surface specialization of
`not_requiredBudget_on_strictDAGSemantics_atWitness`.

This is the exact pointwise failure mode for the requested family target:
at any concrete canonical witness, the strict-semantics `S` is full, so the
required-budget inequality cannot hold.
-/
theorem not_requiredBudget_on_strictProvider_onCanonicalBound_atWitness
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (n : Nat) (β ε : Rat)
    (W : SmallDAGWitnessOnSlice
      (F.paramsOf n β)
      (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε) :
    ¬ (requiredComplementBudget (F.paramsOf n β) ≤
        Models.Partial.tableLen (F.paramsOf n β).n -
          ((promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
              F (ppolyDAGSizeBoundOnSlices F hInDag)) n β ε W).S.card) := by
  simpa using not_requiredBudget_on_strictDAGSemantics_atWitness (W := W)

/--
Operational strict-mainline blocker on the canonical DAG-size surface.

If a concrete small-DAG solver witness exists at `(n, β, ε)`, then the strict
semantic provider cannot satisfy the required-budget target at this same index.

This packages the witness-level impossibility
`not_requiredBudget_on_strictProvider_onCanonicalBound_atWitness` in the exact
shape used by source-side route checks.
-/
theorem not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (n : Nat) (β ε : Rat)
    (hSolver : SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ¬ promiseYesRequiredBudgetOnInvariantProviderOnSlices
        F
        (ppolyDAGSizeBoundOnSlices F hInDag)
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F (ppolyDAGSizeBoundOnSlices F hInDag)) := by
  intro hBudget
  rcases hSolver with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice
      (F.paramsOf n β)
      (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact
    (not_requiredBudget_on_strictProvider_onCanonicalBound_atWitness
      F hInDag n β ε W)
      (hBudget n β ε W)

/--
Pointwise contradiction wrapper for the strict canonical Route-A1 budget target.

This is the direct operational form used in roadmap checks: at a fixed index,
you cannot simultaneously have

1. a concrete small-DAG solver witness, and
2. the strict-semantics required-budget provider assumption.
-/
theorem false_of_smallDAGSolver_and_strictRequiredBudgetProvider_onCanonicalBound
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)))
    (n : Nat) (β ε : Rat)
    (hSolver : SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε)
    (hBudget :
      promiseYesRequiredBudgetOnInvariantProviderOnSlices
        F
        (ppolyDAGSizeBoundOnSlices F hInDag)
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F (ppolyDAGSizeBoundOnSlices F hInDag))) :
    False := by
  exact
    (not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver
      F hInDag n β ε hSolver)
      hBudget

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
Package the decision-certificate route directly in the split Q1/Q2 form:
semantic forcing plus slack on the same `S`.
-/
def promiseYesSourceDecompositionAt_of_decisionCertificate
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseYesDecisionCertificateAt W)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Models.Partial.tableLen p.n - cert.S.card)) :
    PromiseYesSourceDecompositionAt W where
  inv := promiseYesAcceptanceInvariantAt_of_decisionCertificate cert
  hSlackOnInvS := by
    simpa [promiseYesAcceptanceInvariantAt_of_decisionCertificate] using hSlack

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
Any promise/value package already forces the underlying semantic coordinate set
to be non-full.

Reason: `hSlack` would become `circuitCountBound ... < 1` at `S = Finset.univ`,
while `circuitCountBound_two_le_of_gapParams` gives a lower bound `≥ 2`.
-/
theorem nontrivialS_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    cert.S ≠ Finset.univ := by
  intro hUniv
  have hSCard : cert.S.card = Models.Partial.tableLen p.n := by
    simpa [hUniv]
  have hRhs : 2 ^ (Models.Partial.tableLen p.n - cert.S.card) = 1 := by
    simpa [hSCard]
  have hlt1 : Models.circuitCountBound p.n (p.sNO - 1) < 1 := by
    simpa [hRhs] using cert.hSlack
  have hge2 : 2 ≤ Models.circuitCountBound p.n (p.sNO - 1) :=
    circuitCountBound_two_le_of_gapParams p
  exact Nat.not_lt_of_ge (le_trans (by decide : 1 ≤ 2) hge2) hlt1

/--
From any package witness we can extract the genuinely useful quantitative target:
the complement budget is at least `requiredComplementBudget p`.
-/
theorem requiredComplementBudget_le_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    requiredComplementBudget p ≤ Models.Partial.tableLen p.n - cert.S.card := by
  exact Nat.find_min' (exists_countingSlack_budget p) cert.hSlack

/--
Branch-C quantitative strengthening: package-route slack already implies that
the complement of `S` is nonempty.

This is stronger than `S ≠ Finset.univ` and is directly aligned with future Q2
goals (a positive complement budget).
-/
theorem complementPos_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    0 < Models.Partial.tableLen p.n - cert.S.card := by
  have hge2 : 2 ≤ Models.circuitCountBound p.n (p.sNO - 1) :=
    circuitCountBound_two_le_of_gapParams p
  have hPowGt1 : 1 < 2 ^ (Models.Partial.tableLen p.n - cert.S.card) := by
    have hCountGt1 : 1 < Models.circuitCountBound p.n (p.sNO - 1) :=
      lt_of_lt_of_le (by decide : 1 < 2) hge2
    exact lt_trans hCountGt1 cert.hSlack
  by_contra hNotPos
  have hZero : Models.Partial.tableLen p.n - cert.S.card = 0 :=
    Nat.eq_zero_of_not_pos hNotPos
  have hNotPowGt1 : ¬ 1 < 2 ^ (Models.Partial.tableLen p.n - cert.S.card) := by
    simpa [hZero]
  exact hNotPowGt1 hPowGt1

/--
Equivalent cardinal form of `complementPos_of_promiseValueLocalityPackageAt`:
the semantic set is strictly smaller than the full value-coordinate space.
-/
theorem scard_lt_tableLen_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    cert.S.card < Models.Partial.tableLen p.n := by
  by_contra hNotLt
  have hLe : Models.Partial.tableLen p.n ≤ cert.S.card := le_of_not_gt hNotLt
  have hZero : Models.Partial.tableLen p.n - cert.S.card = 0 := Nat.sub_eq_zero_of_le hLe
  have hPos : 0 < Models.Partial.tableLen p.n - cert.S.card :=
    complementPos_of_promiseValueLocalityPackageAt cert
  exact (Nat.lt_irrefl 0) (hZero ▸ hPos)

/--
Provider-level quantitative Branch-C probe:
every witness produced by the package provider has positive complement budget.
-/
abbrev promiseValueComplementPosProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      0 < Models.Partial.tableLen (F.paramsOf n β).n - (hPkg n β ε W).S.card

/--
The package provider automatically satisfies the quantitative Branch-C probe.
-/
theorem promiseValueComplementPosProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseValueComplementPosProviderOnSlices F SizeBound hPkg := by
  intro n β ε W
  exact complementPos_of_promiseValueLocalityPackageAt (hPkg n β ε W)

/--
Provider-level quantitative target for "enough complement":
every produced witness has complement budget at least the required threshold.
-/
abbrev promiseValueRequiredBudgetProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      requiredComplementBudget (F.paramsOf n β) ≤
        Models.Partial.tableLen (F.paramsOf n β).n - (hPkg n β ε W).S.card

/--
The package provider automatically satisfies the stronger required-budget target.
-/
theorem promiseValueRequiredBudgetProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseValueRequiredBudgetProviderOnSlices F SizeBound hPkg := by
  intro n β ε W
  exact requiredComplementBudget_le_of_promiseValueLocalityPackageAt (hPkg n β ε W)

/--
Branch-C constructive bridge:

from a promise/value package we can produce not only Q1 semantic acceptance, but
also a witness that the semantic set is nontrivial (`S ≠ Finset.univ`).
-/
noncomputable def promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    PromiseYesAcceptanceInvariantAtNontrivialS W := by
  refine
    { inv := promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt cert
      hS_nontrivial := ?_ }
  intro hInvUniv
  have hCertUniv : cert.S = Finset.univ := by
    simpa [promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt,
      promiseYesAcceptanceInvariantAt_of_decisionCertificate,
      promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt] using hInvUniv
  exact nontrivialS_of_promiseValueLocalityPackageAt cert hCertUniv

/--
Provider-level Branch-C bridge:

`promiseValueLocalityPackageAtProviderOnSlices` already implies
`promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices`.
-/
noncomputable def
    promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices F SizeBound := by
  intro n β ε W
  exact promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt
    (hPkg n β ε W)

/--
First concrete inhabitant builder for `NontrivialSAlternativeProducerRoute`.

This uses an already available non-full-`S` source constructor
(`promiseValueLocalityPackageAtProviderOnSlices` -> nontrivial-`S` provider) and
combines it with an explicit formula support-bounds witness.
-/
noncomputable def nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds
    (hPkg :
      ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
        promiseValueLocalityPackageAtProviderOnSlices F SizeBound)
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    NontrivialSAlternativeProducerRoute where
  nontrivialSProvider := by
    intro F SizeBound
    exact
      promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider
        F SizeBound (hPkg F SizeBound)
  supportBounds := hBounds

/--
Class-shaped theorem requested by the current execution order:

non-full-`S` slice source + formula-track witness -> `FormulaSupportRestrictionBoundsPartial`.

Implemented via the first concrete route inhabitant to keep the dependency path
explicit and auditable.
-/
theorem formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andSupportBounds
    (hPkg :
      ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
        promiseValueLocalityPackageAtProviderOnSlices F SizeBound)
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    Magnification.FormulaSupportRestrictionBoundsPartial := by
  exact
    formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute
      (nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds
        hPkg hBounds)

/--
I-2 ladder step exported directly from the same class-shaped theorem:
`... -> FormulaSupportRestrictionBoundsPartial -> hasDefaultStructuredLocalityProviderPartial`.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andSupportBounds
    (hPkg :
      ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
        promiseValueLocalityPackageAtProviderOnSlices F SizeBound)
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    Magnification.hasDefaultStructuredLocalityProviderPartial := by
  exact
    Magnification.hasDefaultStructuredLocalityProviderPartial_of_supportBounds
      (formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andSupportBounds
        hPkg hBounds)

/--
Concrete closure of the external support-bounds witness through the existing
multi-switching contract route.

This theorem keeps the non-full-`S` slice source explicit in the signature while
using the already-internalized magnification theorem
`formula_support_bounds_from_multiswitching` to discharge `hBounds`.
-/
theorem formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching
    (hPkg :
      ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
        promiseValueLocalityPackageAtProviderOnSlices F SizeBound)
    (hMS : Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    Magnification.FormulaSupportRestrictionBoundsPartial := by
  classical
  let _ := hPkg
  intro p hFormula
  exact Magnification.formula_support_bounds_from_multiswitching (hMS := hMS) (p := p) hFormula

/--
I-2 ladder endpoint from non-full-`S` slice source plus multi-switching
contract, without an external `hBounds` argument.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching
    (hPkg :
      ∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
        promiseValueLocalityPackageAtProviderOnSlices F SizeBound)
    (hMS : Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    Magnification.hasDefaultStructuredLocalityProviderPartial := by
  exact
    Magnification.hasDefaultStructuredLocalityProviderPartial_of_supportBounds
      (formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching
        hPkg hMS)

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
Package the pairwise promise/value route directly in the split Q1/Q2 form.
-/
noncomputable def promiseYesSourceDecompositionAt_of_promiseValueLocalityPackageAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PromiseValueLocalityPackageAt W) :
    PromiseYesSourceDecompositionAt W := by
  refine
    { inv := promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt cert
      hSlackOnInvS := ?_ }
  simpa [promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt] using cert.hSlack

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
Restricted-model quantitative weak-route closure:
small value-supported output support already yields the chosen one-sided
`PromiseYesSubcubeCertificateAt`.
-/
noncomputable def promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2)
    (hValueSupport :
      ∀ i ∈ DagCircuit.support W.C,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    PromiseYesSubcubeCertificateAt W := by
  exact promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt
    (promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported
      W hSupportHalf hValueSupport)

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
Restricted-model contradiction on the weak mainline:
if the DAG output depends only on at most half of the value coordinates, then
the chosen quantitative YES-centered route already rules out correctness.
-/
theorem no_small_dag_solver_of_supportHalfBound_valueSupported
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε)
    (hSupportHalf :
      (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2)
    (hValueSupport :
      ∀ i ∈ DagCircuit.support W.C,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i) :
    False := by
  exact no_small_dag_solver_of_promiseYesSubcubeCertificateAt W
    (promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported
      W hSupportHalf hValueSupport)

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
Provider reduction: pairwise promise/value packages already supply the semantic
Q1 half (`PromiseYesAcceptanceInvariantAt`) on every slice.
-/
noncomputable def promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound := by
  intro n β ε W
  exact promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt (hPkg n β ε W)

/--
Provider reduction: pairwise promise/value packages also supply the Q2 half,
namely counting slack on the same semantic set chosen by the Q1 provider above.
-/
theorem promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseYesSlackOnInvariantProviderOnSlices
      F SizeBound
      (promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
        F SizeBound hPkg) := by
  intro n β ε W
  simpa [promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider,
    promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt] using (hPkg n β ε W).hSlack

/--
Provider reduction from pairwise promise/value packages to the split Q1/Q2 API.
-/
noncomputable def promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider_viaSemanticAndSlack
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound :=
  promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider
    F SizeBound
    (promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
      F SizeBound hPkg)
    (promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider
      F SizeBound hPkg)

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
Compiled closure from the explicit Q1/Q2 split provider interface:

1. semantic one-sided forcing provider (`hInv`);
2. quantitative slack-on-the-same-`S` provider (`hSlack`).

This theorem is the direct provider-level counterpart of the decomposition
package `PromiseYesSourceDecompositionAt`.
-/
theorem noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound)
    (hSlack : promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound
    (promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider
      F SizeBound hInv hSlack)

/--
Direct closure from the threshold-budget quantitative provider target.

This is the exact "Q1 + required-budget" composition requested by the active
plan: once semantic one-sided forcing is available (`hInv`) and the same-set
complement budget reaches `requiredComplementBudget`, we compile to slack
arithmetically and close `¬ SmallDAGSolver` via the existing promise-YES route.
-/
theorem noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound)
    (hBudget : promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound hInv) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices F SizeBound
    hInv
    (promiseYesSlackOnInvariantProviderOnSlices_of_requiredBudgetProvider
      F SizeBound hInv hBudget)

/--
Strict-semantics specialization of
`noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices`.

This theorem isolates the only remaining source-side quantitative obligation on
the strict mainline:

`promiseYesRequiredBudgetOnInvariantProviderOnSlices` for the strict semantic
provider.
-/
theorem noSmallDAG_of_strictSemanticsAndRequiredBudgetProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hBudget :
      promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F SizeBound)) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices F SizeBound
    (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
      F SizeBound)
    hBudget

/--
Provider-level strict-mainline compiler:

if strict DAG semantics supplies the semantic Q1 half (already canonical in
`promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics`) and the
source theorem provides the required complement-budget inequality on the same
semantic set, then we obtain the operational witness-indexed source endpoint
`PromiseYesSubcubeCertificateAt`.
-/
def promiseYesSubcubeCertificateAtProviderOnSlices_of_strictSemanticsAndRequiredBudgetProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hBudget :
      promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F SizeBound)) :
    promiseYesSubcubeCertificateAtProviderOnSlices F SizeBound := by
  let hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound :=
    promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics F SizeBound
  let hSlack : promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv :=
    promiseYesSlackOnInvariantProviderOnSlices_of_requiredBudgetProvider
      F SizeBound hInv hBudget
  exact promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider
    F SizeBound hInv hSlack

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
Same closure as `noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices`, but
factored explicitly through the split Q1/Q2 provider interface.
-/
theorem noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices F SizeBound
    (promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
      F SizeBound hPkg)
    (promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider
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
Canonical total-table family induced by a YES-centered value-subcube
certificate.
-/
noncomputable def yesSubcubeFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : YesSubcubeCertificateAt W) :
    Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
  Counting.consistentFinset
    (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes))

/--
Exact cardinality of the canonical YES-subcube family.
-/
theorem card_yesSubcubeFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : YesSubcubeCertificateAt W) :
    (yesSubcubeFamily cert).card = 2 ^ (Models.Partial.tableLen p.n - cert.S.card) := by
  dsimp [yesSubcubeFamily]
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

/--
Every table in `yesSubcubeFamily cert` is accepted by the witness circuit.
-/
theorem dagEval_true_on_yesSubcubeFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : YesSubcubeCertificateAt W) :
    ∀ g ∈ yesSubcubeFamily cert,
      DagCircuit.eval W.C (encodeTotalAsPartial g) = true := by
  intro g hg
  have hgCons :
      consistentTotal
        (Counting.prescribedPartial cert.S (Partial.valPart cert.yYes)) g := by
    dsimp [yesSubcubeFamily] at hg
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
Finite acceptance ratio of a Boolean predicate over a finite support set.
-/
noncomputable def acceptanceRatioOnFinset
    {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → Bool) : Rat :=
  if _hS : S.card = 0 then
    0
  else
    ((S.filter (fun x => f x = true)).card : Rat) / (S.card : Rat)

/--
Canonical evaluator on total truth tables induced by a fixed DAG circuit.

This is the source-level (DAG-only) evaluator used by distributional
statements that should quantify over *all* small DAGs.
-/
def dagAcceptsTotalTableOfCircuit
    (p : GapPartialMCSPParams)
    (D : DagCircuit (Models.partialInputLen p)) :
    Core.BitVec (Models.Partial.tableLen p.n) → Bool :=
  fun t => DagCircuit.eval D (encodeTotalAsPartial t)

/--
Uniform acceptance probability on total truth tables for a fixed DAG circuit.
-/
noncomputable def dagUniformAcceptanceProbOnTotalsOfCircuit
    (p : GapPartialMCSPParams)
    (D : DagCircuit (Models.partialInputLen p)) : Rat :=
  acceptanceRatioOnFinset
    (S := (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))))
    (dagAcceptsTotalTableOfCircuit p D)

/--
If uniform acceptance on total tables is strictly below `1`, then at least one
total table is rejected.
-/
theorem exists_reject_of_uniformAcceptanceProbOnTotals_lt_one
    {p : GapPartialMCSPParams}
    (D : DagCircuit (Models.partialInputLen p))
    (hLtOne : dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1) :
    ∃ t : Core.BitVec (Models.Partial.tableLen p.n),
      dagAcceptsTotalTableOfCircuit p D t = false := by
  classical
  by_contra hNo
  have hAllAccept :
      ∀ t : Core.BitVec (Models.Partial.tableLen p.n),
        dagAcceptsTotalTableOfCircuit p D t = true := by
    intro t
    by_cases hFalse : dagAcceptsTotalTableOfCircuit p D t = false
    · exact False.elim (hNo ⟨t, hFalse⟩)
    · cases hVal : dagAcceptsTotalTableOfCircuit p D t <;> simp [hVal] at hFalse ⊢
  have hFilter :
      (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).filter
          (fun t => dagAcceptsTotalTableOfCircuit p D t = true)
        = (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))) := by
    ext t
    simp [hAllAccept t]
  have hProbEqOne : dagUniformAcceptanceProbOnTotalsOfCircuit p D = 1 := by
    unfold dagUniformAcceptanceProbOnTotalsOfCircuit acceptanceRatioOnFinset
    simp [hFilter]
  linarith [hLtOne, hProbEqOne]

/--
Acceptance probability on generator image under uniform seed for a fixed DAG
circuit.
-/
noncomputable def dagSeedAcceptanceProbOnTotalsOfCircuit
    (p : GapPartialMCSPParams)
    {seedLen : Nat}
    (gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n))
    (D : DagCircuit (Models.partialInputLen p)) : Rat :=
  acceptanceRatioOnFinset
    (S := (Finset.univ : Finset (Core.BitVec seedLen)))
    (fun z => dagAcceptsTotalTableOfCircuit p D (gen z))

/--
If a fixed circuit accepts every seed image pointwise, then its seed-image
acceptance probability is exactly `1`.
-/
theorem dagSeedAcceptanceProbOnTotalsOfCircuit_eq_one_of_forall_accept
    {p : GapPartialMCSPParams}
    {seedLen : Nat}
    {gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)}
    {D : DagCircuit (Models.partialInputLen p)}
    (hAccept :
      ∀ z : Core.BitVec seedLen,
        dagAcceptsTotalTableOfCircuit p D (gen z) = true) :
    dagSeedAcceptanceProbOnTotalsOfCircuit p gen D = 1 := by
  classical
  have hFilter :
      (Finset.univ : Finset (Core.BitVec seedLen)).filter
          (fun z => dagAcceptsTotalTableOfCircuit p D (gen z) = true)
        = (Finset.univ : Finset (Core.BitVec seedLen)) := by
    ext z
    simp [hAccept z]
  simpa [dagSeedAcceptanceProbOnTotalsOfCircuit, acceptanceRatioOnFinset, hFilter]

/--
If a fixed circuit rejects every seed image pointwise, then its seed-image
acceptance probability is exactly `0`.
-/
theorem dagSeedAcceptanceProbOnTotalsOfCircuit_eq_zero_of_forall_reject
    {p : GapPartialMCSPParams}
    {seedLen : Nat}
    {gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)}
    {D : DagCircuit (Models.partialInputLen p)}
    (hReject :
      ∀ z : Core.BitVec seedLen,
        dagAcceptsTotalTableOfCircuit p D (gen z) = false) :
    dagSeedAcceptanceProbOnTotalsOfCircuit p gen D = 0 := by
  classical
  have hFilter :
      (Finset.univ : Finset (Core.BitVec seedLen)).filter
          (fun z => dagAcceptsTotalTableOfCircuit p D (gen z) = true)
        = (∅ : Finset (Core.BitVec seedLen)) := by
    ext z
    simp [hReject z]
  simpa [dagSeedAcceptanceProbOnTotalsOfCircuit, acceptanceRatioOnFinset, hFilter]

/--
Canonical evaluator on total truth tables induced by a fixed witness.

Distributional declarations below must use this form.
-/
abbrev witnessAcceptsTotalTable
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    Core.BitVec (Models.Partial.tableLen p.n) → Bool :=
  dagAcceptsTotalTableOfCircuit p W.C

/-- Uniform acceptance probability on total truth tables for one witness. -/
noncomputable def dagUniformAcceptanceProbOnTotals
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) : Rat :=
  dagUniformAcceptanceProbOnTotalsOfCircuit p W.C

/--
Lower bound on uniform acceptance from any explicitly accepted finite family.
-/
theorem dagUniformAcceptanceProbOnTotals_ge_cardRatio_of_family
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (A : Finset (Core.BitVec (Models.Partial.tableLen p.n)))
    (hAccept : ∀ g ∈ A, witnessAcceptsTotalTable W g = true) :
    ((A.card : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat)) ≤
      dagUniformAcceptanceProbOnTotals W := by
  classical
  let accepted :
      Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).filter
      (fun g => witnessAcceptsTotalTable W g = true)
  have hSub : A ⊆ accepted := by
    intro g hg
    simp [accepted, hAccept g hg]
  have hCardLeNat : A.card ≤ accepted.card := Finset.card_le_card hSub
  have hCardLeRat : (A.card : Rat) ≤ (accepted.card : Rat) := by exact_mod_cast hCardLeNat
  have hDenPos : (0 : Rat) < (2 ^ (Models.Partial.tableLen p.n) : Rat) := by positivity
  have hDiv :
      (A.card : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
        (accepted.card : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) :=
    div_le_div_of_nonneg_right hCardLeRat (le_of_lt hDenPos)
  have hProb :
      dagUniformAcceptanceProbOnTotals W =
        ((accepted.card : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat)) := by
    simp [dagUniformAcceptanceProbOnTotals, dagUniformAcceptanceProbOnTotalsOfCircuit,
      acceptanceRatioOnFinset, accepted, witnessAcceptsTotalTable]
  simpa [hProb] using hDiv

/--
Quantitative uniform-acceptance lower bound induced by a YES-centered
value-subcube certificate.

This is a concrete source-side estimate:
the accepted canonical subcube has exactly
`2^(tableLen - S.card)` members, so its density lower-bounds uniform acceptance.
-/
theorem dagUniformAcceptanceProbOnTotals_ge_subcubeRatio_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : YesSubcubeCertificateAt W) :
    ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat)) ≤
        dagUniformAcceptanceProbOnTotals W := by
  have hBase :
      ((yesSubcubeFamily cert).card : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
          dagUniformAcceptanceProbOnTotals W :=
    dagUniformAcceptanceProbOnTotals_ge_cardRatio_of_family
      W (yesSubcubeFamily cert) (by
        intro g hg
        simpa [witnessAcceptsTotalTable] using
          dagEval_true_on_yesSubcubeFamily cert g hg)
  simpa [card_yesSubcubeFamily cert] using hBase

/-- Acceptance probability on generator image under uniform seed. -/
noncomputable def dagSeedAcceptanceProbOnTotals
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {seedLen : Nat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)) : Rat :=
  dagSeedAcceptanceProbOnTotalsOfCircuit p gen W.C

/--
Source-level easy-image pseudorandomness object against all DAGs satisfying a
size predicate.

Unlike `EasyImagePRGAt W` (consumer-side, witness-indexed), this object is
producer-side and quantifies directly over DAG circuits.
-/
structure SmallDAGEasyImageFoolingSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  hInject : Function.Injective gen
  hLarge :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ seedLen
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hSupportEasy :
    ∀ z : Core.BitVec seedLen,
      PartialMCSP_YES p (totalTableToPartial (gen z))
  hFoolsSmall :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      |dagUniformAcceptanceProbOnTotalsOfCircuit p D -
        dagSeedAcceptanceProbOnTotalsOfCircuit p gen D| ≤ epsilon

/--
Minimal canonical distributional source target for unrestricted-DAG route.

This intentionally drops injective/large-image fields: the counting-closed
distributional contradiction route only needs:
1. easy support,
2. quarter-scale epsilon bound, and
3. fooling against all small DAGs.
-/
structure SmallDAGEasyDistSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hSupportEasy :
    ∀ z : Core.BitVec seedLen,
      PartialMCSP_YES p (totalTableToPartial (gen z))
  hFoolsSmall :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      |dagUniformAcceptanceProbOnTotalsOfCircuit p D -
        dagSeedAcceptanceProbOnTotalsOfCircuit p gen D| ≤ epsilon

/--
Upstream average-case / semantic-sampling flavored source object.

Design note:
- This interface is intentionally aligned with the current canonical
  distributional consumer (`SmallDAGEasyDistSourceAt`) so that future
  mathematical work can focus on proving this object and then compile
  mechanically into the downstream contradiction pipeline.
- We keep field names close to the distributional route to make the compiler
  completely transparent.
-/
structure SmallDAGAverageCaseHardnessSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hSupportEasy :
    ∀ z : Core.BitVec seedLen,
      PartialMCSP_YES p (totalTableToPartial (gen z))
  hFoolsSmall :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      |dagUniformAcceptanceProbOnTotalsOfCircuit p D -
        dagSeedAcceptanceProbOnTotalsOfCircuit p gen D| ≤ epsilon

/--
One-sided easy hitting-set style source object.

Interpretation:
- if a small DAG has noticeably low acceptance under uniform total tables, then
  at least one easy seed image point is rejected.
-/
structure SmallDAGEasyHSGSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hSupportEasy :
    ∀ z : Core.BitVec seedLen,
      PartialMCSP_YES p (totalTableToPartial (gen z))
  hHitsLargeRejectingSets :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1 - epsilon →
      ∃ z : Core.BitVec seedLen,
        dagAcceptsTotalTableOfCircuit p D (gen z) = false

/--
Canonical seed length for the fixed easy sampler.

Current implementation keeps the sampler intentionally minimal and canonical:
there is exactly one seed (`BitVec 0`), so all remaining hardness debt is
concentrated in the one-sided hitting property itself (no free `gen` choice).
-/
def canonicalEasySamplerSeedLen (p : GapPartialMCSPParams) : Nat := 0

/--
Canonical sampler of easy total truth tables.

At this stage it returns the constant-`false` total table for the unique seed.
This is sufficient to remove the remaining existential `gen` degree of freedom
from the canonical final debt statement.
-/
def canonicalEasySampler
    (p : GapPartialMCSPParams) :
    Core.BitVec (canonicalEasySamplerSeedLen p) →
      Core.BitVec (Models.Partial.tableLen p.n) :=
  fun _ _ => false

/--
The canonical easy sampler is supported on YES instances.
-/
theorem canonicalEasySampler_supportEasy
    (p : GapPartialMCSPParams) :
    ∀ z, PartialMCSP_YES p (totalTableToPartial (canonicalEasySampler p z)) := by
  intro z
  refine ⟨Circuit.const false, ?_, ?_⟩
  · simp [Circuit.size]
    exact p.sYES_pos
  · apply const_false_consistent_of_vals_false
    intro j
    right
    simp [canonicalEasySampler, totalTableToPartial]

/--
Canonical family of distinct easy total truth tables.

Important design choice:
- we index directly by truth tables (not by description strings/seeds),
- hence there is no multiplicity bias from many descriptions mapping to one
  table.
-/
noncomputable def canonicalEasyFamilyFinset
    (p : GapPartialMCSPParams) :
    Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
  by
    classical
    exact
      (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).filter
        (fun t => decide (PartialMCSP_YES p (totalTableToPartial t)))

/--
Support lemma: every table in the canonical easy family is easy/YES.
-/
theorem canonicalEasyFamily_supportEasy
    (p : GapPartialMCSPParams) :
    ∀ t ∈ canonicalEasyFamilyFinset p,
      PartialMCSP_YES p (totalTableToPartial t) := by
  classical
  intro t ht
  have hDec : decide (PartialMCSP_YES p (totalTableToPartial t)) = true :=
    (Finset.mem_filter.mp ht).2
  simpa using hDec

/--
Agreement predicate between a total table and a Boolean pattern on a coordinate
set `S`.
-/
def agreesOnPattern
    {p : GapPartialMCSPParams}
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (t : Core.BitVec (Models.Partial.tableLen p.n))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool) : Prop :=
  ∀ i ∈ S, t i = σ i

/--
`canonicalEasyFamilyRealizesPatternOn p S σ` means that canonical easy family
contains at least one table matching pattern `σ` on every coordinate in `S`.
-/
def canonicalEasyFamilyRealizesPatternOn
    (p : GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool) : Prop :=
  ∃ t ∈ canonicalEasyFamilyFinset p, agreesOnPattern S t σ

/--
Coverage contract: canonical easy family realizes all patterns on any
coordinate set of size at most `hardwireBudget`.
-/
def canonicalEasyFamilyRealizesAllPatternsUpTo
    (p : GapPartialMCSPParams)
    (hardwireBudget : Nat) : Prop :=
  ∀ S : Finset (Fin (Models.Partial.tableLen p.n)),
    S.card ≤ hardwireBudget →
      ∀ σ : Fin (Models.Partial.tableLen p.n) → Bool,
        canonicalEasyFamilyRealizesPatternOn p S σ

/--
Coarse explicit size budget for hardwiring an arbitrary Boolean pattern on up to
`k` truth-table coordinates.

The constant is intentionally non-optimized: we only need a simple linear
budget to formulate the coverage theorem used by the normalized bridge.
-/
def hardwireCircuitSize (n k : Nat) : Nat :=
  (6 * n + 10) * k + 1

/--
`assignmentIndex` is injective: the canonical finite encoding of total
assignments is a bijection between `BitVec n` and `Fin (2^n)`.
-/
private theorem assignmentIndex_injective {n : Nat} :
    Function.Injective (@assignmentIndex n) := by
  let e : Core.BitVec n ≃ Fin (Models.Partial.tableLen n) :=
    Fintype.equivFinOfCardEq (by
      simpa [Models.Partial.tableLen] using Counting.card_bitvec n)
  exact (Finite.injective_iff_surjective_of_equiv e).2 assignmentIndex_surjective

/--
Canonical bitvector round-trip through `assignmentIndex`.
-/
private theorem vecOfNat_assignmentIndex {n : Nat} (x : Core.BitVec n) :
    Core.vecOfNat n (assignmentIndex x).val = x := by
  apply assignmentIndex_injective
  simpa using assignmentIndex_vecOfNat_eq (assignmentIndex x)

/-- Input literal selecting either `x_i` or `¬x_i`. -/
private def inputLiteral {n : Nat} (i : Fin n) (b : Bool) : Circuit n :=
  if b then Circuit.input i else Circuit.not (Circuit.input i)

/-- Left-associated conjunction of a list of circuits. -/
private def bigAnd {n : Nat} : List (Circuit n) → Circuit n
  | [] => Circuit.const true
  | c :: cs => Circuit.and c (bigAnd cs)

/-- Left-associated disjunction of a list of circuits. -/
private def bigOr {n : Nat} : List (Circuit n) → Circuit n
  | [] => Circuit.const false
  | c :: cs => Circuit.or c (bigOr cs)

/-- Explicit sum of circuit sizes over a list. -/
private def listCircuitSize {n : Nat} : List (Circuit n) → Nat
  | [] => 0
  | c :: cs => Circuit.size c + listCircuitSize cs

@[simp] private theorem eval_inputLiteral {n : Nat}
    (i : Fin n) (b : Bool) (x : Core.BitVec n) :
    Circuit.eval (inputLiteral i b) x = if x i = b then true else false := by
  cases b <;> simp [inputLiteral, Circuit.eval]

@[simp] private theorem eval_inputLiteral_eq_true_iff {n : Nat}
    (i : Fin n) (b : Bool) (x : Core.BitVec n) :
    Circuit.eval (inputLiteral i b) x = true ↔ x i = b := by
  cases b <;> simp [inputLiteral, Circuit.eval]

@[simp] private theorem eval_bigAnd {n : Nat}
    (cs : List (Circuit n)) (x : Core.BitVec n) :
    Circuit.eval (bigAnd cs) x = List.all cs (fun c => Circuit.eval c x) := by
  induction cs with
  | nil =>
      simp [bigAnd, Circuit.eval]
  | cons c cs ih =>
      simp [bigAnd, ih, Circuit.eval]

@[simp] private theorem eval_bigOr {n : Nat}
    (cs : List (Circuit n)) (x : Core.BitVec n) :
    Circuit.eval (bigOr cs) x = List.any cs (fun c => Circuit.eval c x) := by
  induction cs with
  | nil =>
      simp [bigOr, Circuit.eval]
  | cons c cs ih =>
      simp [bigOr, ih, Circuit.eval]

private theorem bigAnd_size_le {n : Nat} :
    ∀ cs : List (Circuit n),
      Circuit.size (bigAnd cs) ≤ 1 + cs.length + listCircuitSize cs
  | [] => by
      simp [bigAnd, listCircuitSize, Circuit.size]
  | c :: cs => by
      have ih := bigAnd_size_le cs
      simp [bigAnd, listCircuitSize, Circuit.size] at ih ⊢
      omega

private theorem bigOr_size_le {n : Nat} :
    ∀ cs : List (Circuit n),
      Circuit.size (bigOr cs) ≤ 1 + cs.length + listCircuitSize cs
  | [] => by
      simp [bigOr, listCircuitSize, Circuit.size]
  | c :: cs => by
      have ih := bigOr_size_le cs
      simp [bigOr, listCircuitSize, Circuit.size] at ih ⊢
      omega

private theorem inputLiteral_size_le {n : Nat} (i : Fin n) (b : Bool) :
    Circuit.size (inputLiteral i b) ≤ 2 := by
  cases b <;> simp [inputLiteral, Circuit.size]

/--
Selector circuit for one exact truth-table coordinate `j`.
-/
private def pointSelectorCircuit
    (n : Nat)
    (j : Fin (Models.Partial.tableLen n)) : Circuit n :=
  bigAnd ((List.finRange n).map fun i => inputLiteral i (Nat.testBit j.val i.val))

private theorem listCircuitSize_pointSelectors_le
    {n : Nat} :
    ∀ L : List (Fin (Models.Partial.tableLen n)),
      listCircuitSize (L.map (pointSelectorCircuit n)) ≤ (3 * n + 1) * L.length
  | [] => by
      simp [listCircuitSize]
  | j :: L => by
      have ih := listCircuitSize_pointSelectors_le L
      have hLitAux :
          ∀ L : List (Fin n),
            listCircuitSize (L.map fun i => inputLiteral i (Nat.testBit j.val i.val)) ≤
              2 * L.length := by
        intro L
        induction L with
        | nil =>
            simp [listCircuitSize]
        | cons i L ihL =>
            have hi : Circuit.size (inputLiteral i (Nat.testBit j.val i.val)) ≤ 2 :=
              inputLiteral_size_le i (Nat.testBit j.val i.val)
            simp [listCircuitSize] at ihL ⊢
            omega
      have hPoint : Circuit.size (pointSelectorCircuit n j) ≤ 3 * n + 1 := by
        have hBig := bigAnd_size_le
          ((List.finRange n).map fun i => inputLiteral i (Nat.testBit j.val i.val))
        have hLit :
            listCircuitSize
                ((List.finRange n).map fun i => inputLiteral i (Nat.testBit j.val i.val))
              ≤ 2 * n := by
          simpa using hLitAux (List.finRange n)
        calc
          Circuit.size (pointSelectorCircuit n j)
              ≤ 1 + ((List.finRange n).map fun i => inputLiteral i (Nat.testBit j.val i.val)).length +
                  listCircuitSize
                    ((List.finRange n).map fun i => inputLiteral i (Nat.testBit j.val i.val)) :=
            by simpa [pointSelectorCircuit] using hBig
          _ ≤ 1 + n + 2 * n := by
            simp at hLit ⊢
            omega
          _ = 3 * n + 1 := by ring
      calc
        listCircuitSize ((j :: L).map (pointSelectorCircuit n))
            = Circuit.size (pointSelectorCircuit n j) +
                listCircuitSize (L.map (pointSelectorCircuit n)) := by
              simp [listCircuitSize]
        _ ≤ (3 * n + 1) + (3 * n + 1) * L.length := by
              gcongr
        _ = (3 * n + 1) * (L.length + 1) := by ring
        _ = (3 * n + 1) * (List.length (j :: L)) := by simp

private theorem pointSelectorCircuit_eval_true_iff
    {n : Nat}
    (j k : Fin (Models.Partial.tableLen n)) :
    Circuit.eval (pointSelectorCircuit n j) (Core.vecOfNat n k.val) = true ↔ k = j := by
  constructor
  · intro hEval
    have hVecEq : Core.vecOfNat n k.val = Core.vecOfNat n j.val := by
      funext i
      rw [pointSelectorCircuit, eval_bigAnd] at hEval
      have hAll := List.all_eq_true.mp hEval
      have hLit :
          Circuit.eval (inputLiteral i (Nat.testBit j.val i.val))
            (Core.vecOfNat n k.val) = true := by
        apply hAll
        exact List.mem_map.mpr ⟨i, by simp, rfl⟩
      have hBit :
          (Core.vecOfNat n k.val) i = Nat.testBit j.val i.val :=
        (eval_inputLiteral_eq_true_iff
          (i := i) (b := Nat.testBit j.val i.val)
          (x := Core.vecOfNat n k.val)).1 hLit
      simpa [Core.vecOfNat] using hBit
    have hIdx : assignmentIndex (Core.vecOfNat n k.val) =
        assignmentIndex (Core.vecOfNat n j.val) := congrArg assignmentIndex hVecEq
    simpa [assignmentIndex_vecOfNat_eq] using hIdx
  · intro hkj
    subst k
    rw [pointSelectorCircuit, eval_bigAnd]
    apply List.all_eq_true.mpr
    intro c hc
    rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
    exact (eval_inputLiteral_eq_true_iff
      (i := i) (b := Nat.testBit j.val i.val)
      (x := Core.vecOfNat n j.val)).2 (by simp [Core.vecOfNat])

private theorem pointSelectorCircuit_eval_false_of_ne
    {n : Nat}
    {j k : Fin (Models.Partial.tableLen n)}
    (hkj : k ≠ j) :
    Circuit.eval (pointSelectorCircuit n j) (Core.vecOfNat n k.val) = false := by
  cases hEval : Circuit.eval (pointSelectorCircuit n j) (Core.vecOfNat n k.val) with
  | false =>
      exact rfl
  | true =>
      exact (hkj ((pointSelectorCircuit_eval_true_iff j k).1 hEval)).elim

/--
Pattern hardwire circuit: OR of point selectors for those `j ∈ S` with
`σ j = true`.
-/
private noncomputable def patternHardwireCircuit
    (p : GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool) :
    Circuit p.n :=
  bigOr (((S.filter fun j => σ j).toList).map fun j => pointSelectorCircuit p.n j)

private theorem patternHardwireCircuit_correct_on_S
    (p : GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool)
    {j : Fin (Models.Partial.tableLen p.n)}
    (hj : j ∈ S) :
    Circuit.eval (patternHardwireCircuit p S σ) (Core.vecOfNat p.n j.val) = σ j := by
  let P : Finset (Fin (Models.Partial.tableLen p.n)) := S.filter fun k => σ k
  cases hσ : σ j with
  | false =>
      have hAllFalse :
          ∀ k ∈ P.toList,
            ¬ Circuit.eval (pointSelectorCircuit p.n k) (Core.vecOfNat p.n j.val) = true := by
        intro k hk
        have hkP : k ∈ P := by simpa using (Finset.mem_toList.mp hk)
        have hjne : j ≠ k := by
          intro hjk
          subst hjk
          simpa [P, hj, hσ] using hkP
        simpa [pointSelectorCircuit_eval_false_of_ne (j := k) (k := j) hjne]
      have hAny :
          List.any P.toList
              (fun k =>
                Circuit.eval (pointSelectorCircuit p.n k) (Core.vecOfNat p.n j.val)) =
            false :=
        List.any_eq_false.mpr hAllFalse
      simpa [patternHardwireCircuit, P, hσ, List.any_map] using hAny
  | true =>
      have hjP : j ∈ P := by
        simpa [P, hj, hσ]
      have hAny :
          List.any P.toList
              (fun k =>
                Circuit.eval (pointSelectorCircuit p.n k) (Core.vecOfNat p.n j.val)) =
            true := by
        apply List.any_eq_true.mpr
        refine ⟨j, ?_, ?_⟩
        · simpa using (Finset.mem_toList.mpr hjP)
        · exact (pointSelectorCircuit_eval_true_iff j j).2 rfl
      simpa [patternHardwireCircuit, P, hσ, List.any_map] using hAny

private theorem patternHardwireCircuit_size_le
    (p : GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool) :
    Circuit.size (patternHardwireCircuit p S σ) ≤ hardwireCircuitSize p.n S.card := by
  let P : Finset (Fin (Models.Partial.tableLen p.n)) := S.filter fun j => σ j
  have hBig :
      Circuit.size (patternHardwireCircuit p S σ)
        ≤ 1 + P.toList.length +
            listCircuitSize (P.toList.map fun j => pointSelectorCircuit p.n j) := by
    simpa [patternHardwireCircuit, P] using
      bigOr_size_le (P.toList.map fun j => pointSelectorCircuit p.n j)
  have hList :
      listCircuitSize (P.toList.map fun j => pointSelectorCircuit p.n j)
        ≤ (3 * p.n + 1) * P.toList.length := by
    simpa using listCircuitSize_pointSelectors_le (n := p.n) P.toList
  have hCard : P.card ≤ S.card := Finset.card_filter_le _ _
  have hFactorPS :
      1 + P.card + (3 * p.n + 1) * P.card ≤ 1 + S.card + (3 * p.n + 1) * S.card := by
    calc
      1 + P.card + (3 * p.n + 1) * P.card
          = 1 + (3 * p.n + 2) * P.card := by ring
      _ ≤ 1 + (3 * p.n + 2) * S.card :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (3 * p.n + 2) hCard) 1
      _ = 1 + S.card + (3 * p.n + 1) * S.card := by ring
  have hMain :
      1 + S.card + (3 * p.n + 1) * S.card ≤ 1 + (6 * p.n + 10) * S.card := by
    have hCoeff : 3 * p.n + 2 ≤ 6 * p.n + 10 := by omega
    calc
      1 + S.card + (3 * p.n + 1) * S.card
          = 1 + (3 * p.n + 2) * S.card := by ring
      _ ≤ 1 + (6 * p.n + 10) * S.card :=
        Nat.add_le_add_left (Nat.mul_le_mul_right S.card hCoeff) 1
  calc
    Circuit.size (patternHardwireCircuit p S σ)
        ≤ 1 + P.toList.length +
            listCircuitSize (P.toList.map fun j => pointSelectorCircuit p.n j) := hBig
    _ ≤ 1 + P.toList.length + (3 * p.n + 1) * P.toList.length := by omega
    _ = 1 + P.card + (3 * p.n + 1) * P.card := by simp
    _ ≤ 1 + S.card + (3 * p.n + 1) * S.card := hFactorPS
    _ ≤ 1 + (6 * p.n + 10) * S.card := hMain
    _ = hardwireCircuitSize p.n S.card := by
      simp [hardwireCircuitSize, Nat.add_comm, Nat.add_left_comm]

private theorem circuitComputes_circuitToTable {n : Nat} (C : Circuit n) :
    circuitComputes C (Counting.circuitToTable C) := by
  intro x
  let y : Core.BitVec n := (assignmentIndex_surjective (assignmentIndex x)).choose
  have hy : assignmentIndex y = assignmentIndex x :=
    (assignmentIndex_surjective (assignmentIndex x)).choose_spec
  have hyx : y = x := assignmentIndex_injective hy
  change Circuit.eval C x = Counting.circuitToTable C (assignmentIndex x)
  simp [Counting.circuitToTable, y, hyx]

private theorem circuitToTable_apply_eq_eval_vecOfNat
    {n : Nat}
    (C : Circuit n)
    (j : Fin (Models.Partial.tableLen n)) :
    Counting.circuitToTable C j = Circuit.eval C (Core.vecOfNat n j.val) := by
  have hComp := circuitComputes_circuitToTable C (Core.vecOfNat n j.val)
  change Circuit.eval C (Core.vecOfNat n j.val) =
      Counting.circuitToTable C (assignmentIndex (Core.vecOfNat n j.val)) at hComp
  simpa [assignmentIndex_vecOfNat_eq] using hComp.symm

private theorem mem_canonicalEasyFamilyFinset_of_smallCircuit
    (p : GapPartialMCSPParams)
    (C : Circuit p.n)
    (hSize : Circuit.size C ≤ p.sYES) :
    Counting.circuitToTable C ∈ canonicalEasyFamilyFinset p := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply decide_eq_true
  refine ⟨C, hSize, ?_⟩
  exact (is_consistent_total_iff C (Counting.circuitToTable C)).2
    (circuitComputes_circuitToTable C)

private theorem canonicalEasyFamilyRealizesPatternOn_of_hardwire
    (p : GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool)
    (hSize : hardwireCircuitSize p.n S.card < p.sYES) :
    canonicalEasyFamilyRealizesPatternOn p S σ := by
  let C := patternHardwireCircuit p S σ
  let t := Counting.circuitToTable C
  refine ⟨t, ?_, ?_⟩
  · apply mem_canonicalEasyFamilyFinset_of_smallCircuit (p := p) (C := C)
    exact le_of_lt (lt_of_le_of_lt (patternHardwireCircuit_size_le p S σ) hSize)
  · intro j hj
    have hTable : t j = Circuit.eval C (Core.vecOfNat p.n j.val) :=
      circuitToTable_apply_eq_eval_vecOfNat C j
    exact hTable.trans (patternHardwireCircuit_correct_on_S p S σ hj)

/--
Monotonicity of the coarse hardwire budget in the number of constrained
coordinates.
-/
theorem hardwireCircuitSize_le_of_le
    {n k₁ k₂ : Nat}
    (h : k₁ ≤ k₂) :
    hardwireCircuitSize n k₁ ≤ hardwireCircuitSize n k₂ := by
  unfold hardwireCircuitSize
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (6 * n + 10) h) 1

/--
Coverage from explicit hardwire budget.

Intended constructive proof (to be filled with helper circuits):
* build `pointSelectorCircuit` for each coordinate,
* OR selectors corresponding to `σ(j)=true`,
* prove agreement on `S`,
* bound circuit size by `hardwireCircuitSize`.

This theorem is the contract that removes external `hCover` from the bridge.
-/
theorem canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound
    (p : GapPartialMCSPParams)
    (hardwireBudget : Nat)
    (hSize : hardwireCircuitSize p.n hardwireBudget < p.sYES) :
    canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget := by
  intro S hSCard σ
  apply canonicalEasyFamilyRealizesPatternOn_of_hardwire (p := p) (S := S) (σ := σ)
  exact lt_of_le_of_lt (hardwireCircuitSize_le_of_le (n := p.n) hSCard) hSize

/--
Canonical value-only alive coordinate set extracted from a semantic restriction
certificate.

`SmallDAGWitnessRestrictionExtractionAt` stores `alive` in the
`Facts.LocalityLift` input universe.  We first cast it to the native
`Models.partialInputLen p` universe and then keep only value coordinates
`tableValPos j` that survive in that alive set.
-/
def canonicalValueAliveSet
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    Finset (Fin (Models.Partial.tableLen p.n)) :=
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen E.r
  Finset.univ.filter (fun j => tableValPos j ∈ rPartial.alive)

/--
Stability on the extracted canonical value-alive set.

This theorem removes one external bridge hypothesis:
local dependence on `S(W)` now follows canonically from extraction itself.

Proof idea:
1. cast the extraction restriction into `Models.partialInputLen p`,
2. transfer `E.hStable` to this casted restriction,
3. invoke `Restriction.localizedOn_of_stable`,
4. show encoded total inputs agree on all alive coordinates:
   - mask coordinates are always `true` for total encodings,
   - value coordinates are controlled by agreement on `canonicalValueAliveSet E`.
-/
theorem stableOn_canonicalValueAliveSet_of_extraction
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    ∀ x y : Core.BitVec (Models.Partial.tableLen p.n),
      (∀ j ∈ canonicalValueAliveSet E, x j = y j) →
      dagAcceptsTotalTableOfCircuit p W.C y =
        dagAcceptsTotalTableOfCircuit p W.C x := by
  classical
  let solver : Magnification.SmallGeneralCircuitSolver_Partial p :=
    generalSolverOfSmallDAGWitnessOnSlice W
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen E.r
  have hStable :
      ∀ x0 : Core.BitVec (Models.partialInputLen p),
        solver.decide (rPartial.apply x0) = solver.decide x0 := by
    let hstable_cast :
        ∀ xFacts : Facts.LocalityLift.BitVec
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          solver.decide (ThirdPartyFacts.castBitVec hlen (E.r.apply xFacts)) =
            solver.decide (ThirdPartyFacts.castBitVec hlen xFacts) := by
      intro xFacts
      simpa [solver, generalSolverOfSmallDAGWitnessOnSlice,
        Magnification.SmallGeneralCircuitSolver_Partial.decide,
        ThirdPartyFacts.solverDecideFacts, hlen] using E.hStable xFacts
    simpa [rPartial] using
      (ThirdPartyFacts.stable_of_stable_cast
        (h := hlen) (decide := solver.decide) (r := E.r) hstable_cast)
  intro x y hAgreeOnS
  let xPartial : Core.BitVec (Models.partialInputLen p) := encodeTotalAsPartial x
  let yPartial : Core.BitVec (Models.partialInputLen p) := encodeTotalAsPartial y
  have hAgreeAlive : ∀ i ∈ rPartial.alive, xPartial i = yPartial i := by
    intro i hi
    by_cases hMask : (i : Nat) < Models.Partial.tableLen p.n
    · simp [xPartial, yPartial, encodeTotalAsPartial, encodePartial,
        totalTableToPartial, hMask]
    · have hiLt : (i : Nat) < Models.partialInputLen p := i.2
      have hjLt :
          (i : Nat) - Models.Partial.tableLen p.n < Models.Partial.tableLen p.n := by
        have : (i : Nat) <
            Models.Partial.tableLen p.n + Models.Partial.tableLen p.n := by
          simpa [Models.Partial.inputLen, two_mul, Models.partialInputLen] using hiLt
        omega
      let j : Fin (Models.Partial.tableLen p.n) :=
        ⟨(i : Nat) - Models.Partial.tableLen p.n, hjLt⟩
      have hValPos : tableValPos j = i := by
        apply Fin.ext
        change
          Models.Partial.tableLen p.n +
              ((i : Nat) - Models.Partial.tableLen p.n) =
            (i : Nat)
        omega
      have hjMemS : j ∈ canonicalValueAliveSet E := by
        simp [canonicalValueAliveSet, rPartial, hValPos, hi]
      have hxyAtJ : x j = y j := hAgreeOnS j hjMemS
      have hxPart : xPartial (tableValPos j) = x j := by
        have hxAtI : xPartial i = x j := by
          simp [xPartial, encodeTotalAsPartial, encodePartial,
            totalTableToPartial, hMask, j]
        simpa [hValPos] using hxAtI
      have hyPart : yPartial (tableValPos j) = y j := by
        have hyAtI : yPartial i = y j := by
          simp [yPartial, encodeTotalAsPartial, encodePartial,
            totalTableToPartial, hMask, j]
        simpa [hValPos] using hyAtI
      have hPartEqAtValPos : xPartial (tableValPos j) = yPartial (tableValPos j) := by
        exact hxPart.trans (hxyAtJ.trans hyPart.symm)
      simpa [hValPos] using hPartEqAtValPos
  have hLocalized :
      solver.decide yPartial = solver.decide xPartial := by
    exact
      ((Facts.LocalityLift.Restriction.localizedOn_of_stable
        (r := rPartial) (f := solver.decide) hStable) xPartial yPartial hAgreeAlive).symm
  simpa [solver, generalSolverOfSmallDAGWitnessOnSlice,
    Magnification.SmallGeneralCircuitSolver_Partial.decide,
    xPartial, yPartial, dagAcceptsTotalTableOfCircuit]
    using hLocalized

/--
Glue lemma: canonical value-alive set cardinality is bounded by the extraction
alive bound.

This lets any existing bound on `E.aliveBound` feed directly into bridge budget
assumptions without manual repackaging.
-/
theorem canonicalValueAliveSet_card_le_aliveBound
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    (canonicalValueAliveSet E).card ≤ E.aliveBound := by
  classical
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen E.r
  have hSCardAlive :
      (canonicalValueAliveSet E).card ≤ rPartial.alive.card := by
    have hImgSub : Finset.image tableValPos (canonicalValueAliveSet E) ⊆ rPartial.alive := by
      intro i hi
      simp only [canonicalValueAliveSet, hlen, rPartial, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact hj
    have hCardImage :
        (canonicalValueAliveSet E).card =
          (Finset.image tableValPos (canonicalValueAliveSet E)).card := by
      rw [Finset.card_image_of_injective (canonicalValueAliveSet E) tableValPos_injective]
    calc
      (canonicalValueAliveSet E).card =
          (Finset.image tableValPos (canonicalValueAliveSet E)).card := hCardImage
      _ ≤ rPartial.alive.card := Finset.card_le_card hImgSub
  have hAliveEq : rPartial.alive.card = E.r.alive.card := by
    simpa [rPartial] using ThirdPartyFacts.castRestriction_alive_card hlen E.r
  calc
    (canonicalValueAliveSet E).card ≤ rPartial.alive.card := hSCardAlive
    _ = E.r.alive.card := hAliveEq
    _ ≤ E.aliveBound := E.hAliveBound

/--
Reject density on the canonical easy family for a fixed DAG circuit.

This is the primary density observable used by the witness-indexed mainline:
`reject density ≥ δ` under low uniform acceptance.
-/
noncomputable def canonicalEasyRejectProbOnFamilyOfCircuit
    (p : GapPartialMCSPParams)
    (D : DagCircuit (Models.partialInputLen p)) : Rat :=
  acceptanceRatioOnFinset
    (S := canonicalEasyFamilyFinset p)
    (fun t => dagAcceptsTotalTableOfCircuit p D t = false)

/--
Witness-specialized canonical easy-family reject density.
-/
noncomputable def canonicalEasyRejectProbOnFamily
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) : Rat :=
  canonicalEasyRejectProbOnFamilyOfCircuit p W.C

/--
If a fixed circuit accepts every table in the canonical easy family, then the
canonical easy-family reject density is `0`.
-/
theorem canonicalEasyRejectProbOnFamilyOfCircuit_eq_zero_of_forall_accept
    {p : GapPartialMCSPParams}
    (D : DagCircuit (Models.partialInputLen p))
    (hAccept :
      ∀ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p D t = true) :
    canonicalEasyRejectProbOnFamilyOfCircuit p D = 0 := by
  classical
  by_cases hCard : (canonicalEasyFamilyFinset p).card = 0
  · simp [canonicalEasyRejectProbOnFamilyOfCircuit, acceptanceRatioOnFinset, hCard]
  · have hFilter :
        (canonicalEasyFamilyFinset p).filter
            (fun t => dagAcceptsTotalTableOfCircuit p D t = false)
          = (∅ : Finset (Core.BitVec (Models.Partial.tableLen p.n))) := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro t ht
      have htMem : t ∈ canonicalEasyFamilyFinset p := (Finset.mem_filter.mp ht).1
      have htRej : dagAcceptsTotalTableOfCircuit p D t = false := (Finset.mem_filter.mp ht).2
      have htAcc : dagAcceptsTotalTableOfCircuit p D t = true := hAccept t htMem
      exact (by simpa [htAcc] using htRej)
    simp [canonicalEasyRejectProbOnFamilyOfCircuit, acceptanceRatioOnFinset, hCard, hFilter]

/--
If at least one canonical easy-family point is rejected, then canonical-family
reject density is at least `1 / 2^tableLen`.
-/
theorem canonicalEasyRejectProbOnFamilyOfCircuit_ge_one_div_twoPow_of_exists_reject
    {p : GapPartialMCSPParams}
    (D : DagCircuit (Models.partialInputLen p))
    (hReject :
      ∃ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p D t = false) :
    (1 : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
      canonicalEasyRejectProbOnFamilyOfCircuit p D := by
  classical
  let family := canonicalEasyFamilyFinset p
  let rejects : Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    family.filter (fun t => dagAcceptsTotalTableOfCircuit p D t = false)
  rcases hReject with ⟨t0, ht0Fam, ht0Rej⟩
  have ht0RejMem : t0 ∈ rejects := by
    exact Finset.mem_filter.mpr ⟨ht0Fam, ht0Rej⟩
  have hRejectPosNat : 1 ≤ rejects.card := by
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t0, ht0RejMem⟩)
  have hFamPosNat : 0 < family.card := Finset.card_pos.mpr ⟨t0, ht0Fam⟩
  have hFamNeZero : family.card ≠ 0 := Nat.ne_of_gt hFamPosNat
  have hFamLeNat : family.card ≤ (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card :=
    Finset.card_le_card (by
      intro x hx
      exact Finset.mem_univ x)
  have hUnivCard :
      ((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat) =
        (2 ^ (Models.Partial.tableLen p.n) : Rat) := by
    simp
  have hFamLeRat :
      (family.card : Rat) ≤ (2 ^ (Models.Partial.tableLen p.n) : Rat) := by
    calc
      (family.card : Rat) ≤ ((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat) := by
        exact_mod_cast hFamLeNat
      _ = (2 ^ (Models.Partial.tableLen p.n) : Rat) := hUnivCard
  have hFamPosRat : (0 : Rat) < (family.card : Rat) := by exact_mod_cast hFamPosNat
  have hStep1 :
      (1 : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
        (1 : Rat) / (family.card : Rat) :=
    one_div_le_one_div_of_le hFamPosRat hFamLeRat
  have hRejectLe :
      (1 : Rat) / (family.card : Rat) ≤
        (rejects.card : Rat) / (family.card : Rat) := by
    have hRejectPosRat : (1 : Rat) ≤ (rejects.card : Rat) := by
      exact_mod_cast hRejectPosNat
    exact div_le_div_of_nonneg_right hRejectPosRat (le_of_lt hFamPosRat)
  have hMain :
      (1 : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
        (rejects.card : Rat) / (family.card : Rat) :=
    le_trans hStep1 hRejectLe
  have hProb :
      canonicalEasyRejectProbOnFamilyOfCircuit p D =
        (rejects.card : Rat) / (family.card : Rat) := by
    simp [canonicalEasyRejectProbOnFamilyOfCircuit, acceptanceRatioOnFinset,
      family, rejects, hFamNeZero]
  simpa [hProb]
    using hMain

/--
Pattern-coverage bridge:
if witness decision depends only on coordinates in `S`, and canonical family
realizes every pattern on `S`, then any rejected table induces a rejected
canonical-family table.
-/
theorem exists_reject_in_canonicalEasyFamily_of_localDependenceAndCoverage
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (hStableOnS :
      ∀ x y : Core.BitVec (Models.Partial.tableLen p.n),
        (∀ i ∈ S, x i = y i) →
          dagAcceptsTotalTableOfCircuit p W.C y =
            dagAcceptsTotalTableOfCircuit p W.C x)
    (hCover :
      ∀ σ : Fin (Models.Partial.tableLen p.n) → Bool,
        canonicalEasyFamilyRealizesPatternOn p S σ)
    (hReject :
      ∃ x : Core.BitVec (Models.Partial.tableLen p.n),
        dagAcceptsTotalTableOfCircuit p W.C x = false) :
    ∃ t ∈ canonicalEasyFamilyFinset p,
      dagAcceptsTotalTableOfCircuit p W.C t = false := by
  rcases hReject with ⟨x, hxRej⟩
  rcases hCover x with ⟨t, htFam, htAgree⟩
  have hSame :
      dagAcceptsTotalTableOfCircuit p W.C t =
        dagAcceptsTotalTableOfCircuit p W.C x :=
    hStableOnS x t (by
      intro i hi
      exact (htAgree i hi).symm)
  refine ⟨t, htFam, ?_⟩
  simpa [hxRej] using hSame

/--
Canonical easy-density source object (analysis-first target).

Interpretation:
- if a small DAG has noticeably low **uniform** acceptance, then its acceptance
  probability on the canonical easy sampler image is bounded away from `1` by a
  positive constant `delta`.

This is the density/transfer-friendly replacement for treating canonical HSG as
the primary debt.
-/
structure CanonicalSmallDAGEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  epsilon : Rat
  delta : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hDeltaPos : 0 < delta
  hRejectDensity :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1 - epsilon →
      dagSeedAcceptanceProbOnTotalsOfCircuit p (canonicalEasySampler p) D ≤ 1 - delta

/--
Witness-indexed (weaker) canonical easy-density source object.

This variant is intentionally weaker than
`CanonicalSmallDAGEasyDensitySourceAt`: it quantifies only over actual slice
solver witnesses `W`, not all DAG circuits satisfying `SizeBound`.

Motivation:
- this is often closer to what strict-semantics arguments naturally provide;
- yet it is still enough for the weak-route contradiction closure because that
  closure only needs transfer for concrete witness circuits.
-/
structure CanonicalWitnessEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  epsilon : Rat
  delta : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hDeltaPos : 0 < delta
  hRejectDensityWitness :
    ∀ {εslice : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound εslice),
      dagUniformAcceptanceProbOnTotals W < 1 - epsilon →
      delta ≤ canonicalEasyRejectProbOnFamily W

/--
Research-target extraction lemma (single witness form):
from a witness-indexed canonical easy-density source, every low-uniform witness
must have canonical-family reject density at least `delta`.
-/
theorem canonicalWitnessEasyDensity_lowUniform_implies_familyRejectDensity
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound)
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (hUniformLow : dagUniformAcceptanceProbOnTotals W < 1 - src.epsilon) :
    src.delta ≤ canonicalEasyRejectProbOnFamily W :=
  src.hRejectDensityWitness W hUniformLow

/--
Central bridge constructor (research template):

`restriction/local dependence + canonical family coverage + low-uniform witness
counterexample`  ⟹  witness-indexed canonical family-density source.

This isolates the exact remaining source debt: provide
- small coordinate sets `S(W)`,
- local dependence of witness acceptance on `S(W)`,
- canonical family coverage on these sets,
- and the low-uniform ⇒ existence-of-reject witness.
-/
def canonicalWitnessEasyDensitySourceAt_of_restrictionExtractionAndCoverage
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (SOf :
      ∀ {εslice : Rat},
        SmallDAGWitnessOnSlice p SizeBound εslice →
          Finset (Fin (Models.Partial.tableLen p.n)))
    (hBudget :
      ∀ {εslice : Rat}
        (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (SOf W).card ≤ hardwireBudget)
    (hCover :
      canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget)
    (hStableOnS :
      ∀ {εslice : Rat}
        (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        ∀ x y : Core.BitVec (Models.Partial.tableLen p.n),
          (∀ i ∈ SOf W, x i = y i) →
            dagAcceptsTotalTableOfCircuit p W.C y =
              dagAcceptsTotalTableOfCircuit p W.C x)
    : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound := by
  refine
    { epsilon := epsilon
      delta := (1 : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat)
      hEpsQuarter := hEpsQuarter
      hDeltaPos := by
        have : (0 : Rat) < (2 ^ (Models.Partial.tableLen p.n) : Rat) := by positivity
        positivity
      hRejectDensityWitness := ?_ }
  intro εslice W hUniformLow
  have hUniformLtOne : dagUniformAcceptanceProbOnTotals W < 1 := by
    have hOneSubLeOne : 1 - epsilon ≤ (1 : Rat) := by linarith
    exact lt_of_lt_of_le hUniformLow hOneSubLeOne
  have hReject :
      ∃ x : Core.BitVec (Models.Partial.tableLen p.n),
        dagAcceptsTotalTableOfCircuit p W.C x = false :=
    exists_reject_of_uniformAcceptanceProbOnTotals_lt_one W.C
      (by simpa [dagUniformAcceptanceProbOnTotals] using hUniformLtOne)
  have hCoverS :
      ∀ σ : Fin (Models.Partial.tableLen p.n) → Bool,
        canonicalEasyFamilyRealizesPatternOn p (SOf W) σ := by
    intro σ
    exact hCover (SOf W) (hBudget W) σ
  have hFamReject :
      ∃ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p W.C t = false :=
    exists_reject_in_canonicalEasyFamily_of_localDependenceAndCoverage
      (W := W) (S := SOf W) (hStableOnS := hStableOnS W) hCoverS hReject
  simpa [canonicalEasyRejectProbOnFamily] using
    canonicalEasyRejectProbOnFamilyOfCircuit_ge_one_div_twoPow_of_exists_reject
      (p := p) (D := W.C) hFamReject

/--
Normalized bridge constructor:

* extraction is provided witness-wise,
* coordinate set is fixed canonically (`canonicalValueAliveSet`),
* locality on this set is *derived* (not assumed) via
  `stableOn_canonicalValueAliveSet_of_extraction`,
* coverage is still passed as the remaining external contract.

So this removes `hStableOnS` from the external debt surface.
-/
def canonicalWitnessEasyDensitySourceAt_of_extractionBudgetAndCoverage
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hExtract :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        SmallDAGWitnessRestrictionExtractionAt W)
    (hBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (canonicalValueAliveSet (hExtract W)).card ≤ hardwireBudget)
    (hCover :
      canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_restrictionExtractionAndCoverage
    (p := p) (SizeBound := SizeBound)
    epsilon hEpsQuarter hEpsNonneg hardwireBudget
    (fun {εslice} W => canonicalValueAliveSet (hExtract W))
    (fun {εslice} W => hBudget W)
    hCover
    (fun {εslice} W => stableOn_canonicalValueAliveSet_of_extraction (hExtract W))

/--
Final normalized bridge form:
only extraction, extracted-set budget, and arithmetic hardwire budget are
external. Coverage is now discharged from `hCoverBudget`.
-/
def canonicalWitnessEasyDensitySourceAt_of_extractionBudget
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hCoverBudget :
      hardwireCircuitSize p.n hardwireBudget < p.sYES)
    (hExtract :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        SmallDAGWitnessRestrictionExtractionAt W)
    (hBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (canonicalValueAliveSet (hExtract W)).card ≤ hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_extractionBudgetAndCoverage
    (p := p) (SizeBound := SizeBound)
    epsilon hEpsQuarter hEpsNonneg hardwireBudget hExtract hBudget
    (canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound
      p hardwireBudget hCoverBudget)

/--
Support-specialized normalized bridge.

This is the fastest restricted-model sanity instantiation of the new density
mainline:
* extraction is taken from syntactic support,
* `hBudget` is discharged from support cardinality via
  `canonicalValueAliveSet_card_le_aliveBound`.
-/
noncomputable def canonicalWitnessEasyDensitySourceAt_of_supportBudget
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hCoverBudget : hardwireCircuitSize p.n hardwireBudget < p.sYES)
    (hSupportBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (DagCircuit.support W.C).card ≤ hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound := by
  refine canonicalWitnessEasyDensitySourceAt_of_extractionBudget
    (p := p) (SizeBound := SizeBound)
    epsilon hEpsQuarter hEpsNonneg hardwireBudget hCoverBudget
    (hExtract := fun {εslice} W => smallDAGWitnessRestrictionExtractionAt_of_support W)
    (hBudget := ?_)
  intro εslice W
  have hSLeAlive :
      (canonicalValueAliveSet (smallDAGWitnessRestrictionExtractionAt_of_support W)).card ≤
        (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound :=
    canonicalValueAliveSet_card_le_aliveBound
      (smallDAGWitnessRestrictionExtractionAt_of_support W)
  calc
    (canonicalValueAliveSet (smallDAGWitnessRestrictionExtractionAt_of_support W)).card ≤
        (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound := hSLeAlive
    _ ≤ (DagCircuit.support W.C).card := by
      simpa [smallDAGWitnessRestrictionExtractionAt_of_support]
    _ ≤ hardwireBudget := hSupportBudget W

/--
Witness-indexed uniform-lower source object.

This is a strictly stronger, often easier-to-target contract than
`CanonicalWitnessEasyDensitySourceAt`: instead of proving a seed-density
implication, it postulates the desired uniform lower bound directly for every
witness.

The density object is then recovered with a trivial contradiction argument
(`uniform < 1 - ε` is impossible).
-/
structure WitnessUniformLowerSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hUniformLower :
    ∀ {εslice : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound εslice),
      1 - epsilon ≤ dagUniformAcceptanceProbOnTotals W

/--
Canonical one-sided easy-HSG source object.

Difference from `SmallDAGEasyHSGSourceAt`:
- drops free fields `seedLen`, `gen`, and `hSupportEasy`;
- bakes in the fixed sampler `canonicalEasySampler`.
-/
structure CanonicalSmallDAGEasyHSGSourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  epsilon : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hHitsLargeRejectingSets :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1 - epsilon →
      ∃ z : Core.BitVec (canonicalEasySamplerSeedLen p),
        dagAcceptsTotalTableOfCircuit p D (canonicalEasySampler p z) = false

/--
Compiler from canonical one-sided easy-HSG source object to the generic source
interface used by downstream route combinators.
-/
def smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound) :
    SmallDAGEasyHSGSourceAt (p := p) SizeBound := by
  refine
    { seedLen := canonicalEasySamplerSeedLen p
      gen := canonicalEasySampler p
      epsilon := src.epsilon
      hEpsQuarter := src.hEpsQuarter
      hSupportEasy := canonicalEasySampler_supportEasy p
      hHitsLargeRejectingSets := ?_ }
  intro εslice D hSize hUniformLow
  simpa using src.hHitsLargeRejectingSets D hSize hUniformLow

/--
Compiler from canonical easy-density source to canonical one-sided easy-HSG
source.

Key point: if every canonical easy seed were accepted, then seed acceptance
probability would be `1`, contradicting `hRejectDensity` together with
`delta > 0`.
-/
def canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound) :
    CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound := by
  refine
    { epsilon := src.epsilon
      hEpsQuarter := src.hEpsQuarter
      hHitsLargeRejectingSets := ?_ }
  intro εslice D hSize hUniformLow
  by_contra hNoReject
  have hAllAccept :
      ∀ z : Core.BitVec (canonicalEasySamplerSeedLen p),
        dagAcceptsTotalTableOfCircuit p D (canonicalEasySampler p z) = true := by
    intro z
    by_cases hFalse : dagAcceptsTotalTableOfCircuit p D (canonicalEasySampler p z) = false
    · exact False.elim (hNoReject ⟨z, hFalse⟩)
    · cases hVal : dagAcceptsTotalTableOfCircuit p D (canonicalEasySampler p z) <;> simp [hVal] at hFalse ⊢
  have hSeedOne :
      dagSeedAcceptanceProbOnTotalsOfCircuit p (canonicalEasySampler p) D = 1 :=
    dagSeedAcceptanceProbOnTotalsOfCircuit_eq_one_of_forall_accept hAllAccept
  have hDensity :
      dagSeedAcceptanceProbOnTotalsOfCircuit p (canonicalEasySampler p) D ≤ 1 - src.delta :=
    src.hRejectDensity D hSize hUniformLow
  rw [hSeedOne] at hDensity
  have : ¬(1 ≤ 1 - src.delta) := by
    linarith [src.hDeltaPos]
  exact this hDensity

/--
Compiler in the opposite direction (current singleton canonical sampler):
canonical one-sided easy-HSG source -> canonical easy-density source.

Because `canonicalEasySamplerSeedLen = 0`, an existential rejecting seed forces
the unique seed to reject, hence seed acceptance probability is exactly `0`.
So the density inequality holds with `delta := 1`.
-/
def canonicalEasyDensitySourceAt_of_canonicalEasyHSGSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound) :
    CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound := by
  refine
    { epsilon := src.epsilon
      delta := 1
      hEpsQuarter := src.hEpsQuarter
      hDeltaPos := by norm_num
      hRejectDensity := ?_ }
  intro εslice D hSize hUniformLow
  rcases src.hHitsLargeRejectingSets D hSize hUniformLow with ⟨z0, hz0⟩
  have hAllReject :
      ∀ z : Core.BitVec (canonicalEasySamplerSeedLen p),
        dagAcceptsTotalTableOfCircuit p D (canonicalEasySampler p z) = false := by
    intro z
    have hzEq : z = z0 := by
      have hSub :
          Subsingleton (Core.BitVec (canonicalEasySamplerSeedLen p)) := by
        simpa [canonicalEasySamplerSeedLen] using
          (inferInstance : Subsingleton (Core.BitVec 0))
      exact hSub.elim z z0
    simpa [hzEq] using hz0
  have hSeedZero :
      dagSeedAcceptanceProbOnTotalsOfCircuit p (canonicalEasySampler p) D = 0 :=
    dagSeedAcceptanceProbOnTotalsOfCircuit_eq_zero_of_forall_reject hAllReject
  simpa [hSeedZero]

/--
Compiler: average-case / semantic-sampling source object to canonical
distributional easy-image source object.
-/
def smallDAGEasyDistSourceAt_of_averageCaseHardnessSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : SmallDAGAverageCaseHardnessSourceAt (p := p) SizeBound) :
    SmallDAGEasyDistSourceAt (p := p) SizeBound := by
  refine
    { seedLen := src.seedLen
      gen := src.gen
      epsilon := src.epsilon
      hEpsQuarter := src.hEpsQuarter
      hSupportEasy := src.hSupportEasy
      hFoolsSmall := src.hFoolsSmall }

/--
Compiler from the stronger symmetric-fooling average-case source to the weaker
one-sided easy-HSG source.
-/
def smallDAGEasyHSGSourceAt_of_averageCaseHardnessSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : SmallDAGAverageCaseHardnessSourceAt (p := p) SizeBound) :
    SmallDAGEasyHSGSourceAt (p := p) SizeBound := by
  refine
    { seedLen := src.seedLen
      gen := src.gen
      epsilon := src.epsilon
      hEpsQuarter := src.hEpsQuarter
      hSupportEasy := src.hSupportEasy
      hHitsLargeRejectingSets := ?_ }
  intro εslice D hSize hUniformLow
  by_contra hNoReject
  have hAllAccept :
      ∀ z : Core.BitVec src.seedLen,
        dagAcceptsTotalTableOfCircuit p D (src.gen z) = true := by
    intro z
    by_cases hFalse : dagAcceptsTotalTableOfCircuit p D (src.gen z) = false
    · exact False.elim (hNoReject ⟨z, hFalse⟩)
    · cases hVal : dagAcceptsTotalTableOfCircuit p D (src.gen z) <;> simp [hVal] at hFalse ⊢
  have hSeedOne :
      dagSeedAcceptanceProbOnTotalsOfCircuit p src.gen D = 1 :=
    dagSeedAcceptanceProbOnTotalsOfCircuit_eq_one_of_forall_accept hAllAccept
  have hFool :
      |dagUniformAcceptanceProbOnTotalsOfCircuit p D -
        dagSeedAcceptanceProbOnTotalsOfCircuit p src.gen D| ≤ src.epsilon :=
    src.hFoolsSmall D hSize
  rw [hSeedOne] at hFool
  have hLeft : -src.epsilon ≤ dagUniformAcceptanceProbOnTotalsOfCircuit p D - 1 :=
    (abs_le.mp hFool).1
  linarith

/--
Minimal witness-level transfer endpoint needed by counting-closed contradiction.
-/
structure EasyImageTransferAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  epsilon : Rat
  hUniformLower : 1 - epsilon ≤ dagUniformAcceptanceProbOnTotals W

/--
Compiler from one-sided easy-HSG source to minimal transfer endpoint.
-/
def easyImageTransferAt_of_smallDAGEasyHSGSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyHSGSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W := by
  have hAllSeedAccept :
      ∀ z : Core.BitVec source.seedLen,
        dagAcceptsTotalTableOfCircuit p W.C (source.gen z) = true := by
    intro z
    have hYesMem : encodeTotalAsPartial (source.gen z) ∈ (gapSliceOfParams p).Yes := by
      simpa [gapSliceOfParams] using
        (gapPartialMCSP_yes_of_small p (encodeTotalAsPartial (source.gen z))
          (by simpa [decodePartial_encodeTotal] using source.hSupportEasy z))
    exact W.hCorrect.1 _ hYesMem
  have hUniformLower : 1 - source.epsilon ≤ dagUniformAcceptanceProbOnTotals W := by
    by_contra hNotLower
    have hUniformLow : dagUniformAcceptanceProbOnTotalsOfCircuit p W.C < 1 - source.epsilon := by
      simpa [dagUniformAcceptanceProbOnTotals] using (lt_of_not_ge hNotLower)
    rcases source.hHitsLargeRejectingSets W.C W.hSize hUniformLow with ⟨z, hzReject⟩
    have hzAccept : dagAcceptsTotalTableOfCircuit p W.C (source.gen z) = true := hAllSeedAccept z
    have : False := by simpa [hzAccept] using hzReject
    exact this
  exact
    { seedLen := source.seedLen
      gen := source.gen
      epsilon := source.epsilon
      hUniformLower := hUniformLower }

/--
Direct compiler from canonical easy-density source to witness-level transfer.

This is the density-first mainline compiler:

`canonical density source -> canonical HSG source -> generic HSG source -> transfer`.
-/
def easyImageTransferAt_of_canonicalEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W :=
  easyImageTransferAt_of_smallDAGEasyHSGSourceAt
    (source :=
      smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt
        (canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt source))
    W

/--
Direct compiler from the weaker witness-indexed canonical easy-density source
to witness-level transfer.
-/
def easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W := by
  have hAllFamilyAccept :
      ∀ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p W.C t = true := by
    intro t ht
    have hYesMem :
        encodeTotalAsPartial t ∈ (gapSliceOfParams p).Yes := by
      simpa [gapSliceOfParams] using
        (gapPartialMCSP_yes_of_small p (encodeTotalAsPartial t)
          (by
            simpa [decodePartial_encodeTotal] using
              canonicalEasyFamily_supportEasy p t ht))
    exact W.hCorrect.1 _ hYesMem
  have hUniformLower : 1 - source.epsilon ≤ dagUniformAcceptanceProbOnTotals W := by
    by_contra hNotLower
    have hUniformLow : dagUniformAcceptanceProbOnTotals W < 1 - source.epsilon :=
      lt_of_not_ge hNotLower
    have hDensity :
        source.delta ≤ canonicalEasyRejectProbOnFamily W :=
      source.hRejectDensityWitness W hUniformLow
    have hRejectZero : canonicalEasyRejectProbOnFamily W = 0 := by
      simpa [canonicalEasyRejectProbOnFamily] using
        canonicalEasyRejectProbOnFamilyOfCircuit_eq_zero_of_forall_accept
          (p := p) (D := W.C) hAllFamilyAccept
    rw [hRejectZero] at hDensity
    have : ¬ (source.delta ≤ 0) := by
      linarith [source.hDeltaPos]
    exact this hDensity
  exact
    { seedLen := canonicalEasySamplerSeedLen p
      gen := canonicalEasySampler p
      epsilon := source.epsilon
      hUniformLower := hUniformLower }

/--
Compile witness-uniform-lower sources into witness-indexed canonical
easy-density sources.

Construction:
- keep the same `epsilon`,
- use `delta := 1`,
- prove reject-density implication by contradiction with `hUniformLower`.
-/
def canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : WitnessUniformLowerSourceAt (p := p) SizeBound) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound := by
  refine
    { epsilon := src.epsilon
      delta := 1
      hEpsQuarter := src.hEpsQuarter
      hDeltaPos := by norm_num
      hRejectDensityWitness := ?_ }
  intro εslice W hUniformLow
  have hLower : 1 - src.epsilon ≤ dagUniformAcceptanceProbOnTotals W :=
    src.hUniformLower W
  have : False := not_lt_of_ge hLower hUniformLow
  exact False.elim this

/--
Extract witness-uniform-lower bounds from witness-indexed canonical
easy-density sources.

Key observation:
- canonical sampler outputs are always YES-instances (`canonicalEasySampler_supportEasy`);
- hence every witness accepts all canonical seeds by correctness;
- therefore seed acceptance probability is `1`, and the density implication
  forces `uniform < 1 - ε` to be impossible.
-/
def witnessUniformLowerSourceAt_of_canonicalWitnessEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound) :
    WitnessUniformLowerSourceAt (p := p) SizeBound := by
  refine
    { epsilon := src.epsilon
      hEpsQuarter := src.hEpsQuarter
      hUniformLower := ?_ }
  intro εslice W
  by_contra hNotLower
  have hUniformLow : dagUniformAcceptanceProbOnTotals W < 1 - src.epsilon :=
    lt_of_not_ge hNotLower
  have hDensity :
      src.delta ≤ canonicalEasyRejectProbOnFamily W :=
    src.hRejectDensityWitness W hUniformLow
  have hAllFamilyAccept :
      ∀ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p W.C t = true := by
    intro t ht
    have hYesMem :
        encodeTotalAsPartial t ∈ (gapSliceOfParams p).Yes := by
      simpa [gapSliceOfParams] using
        (gapPartialMCSP_yes_of_small p (encodeTotalAsPartial t)
          (by
            simpa [decodePartial_encodeTotal] using
              canonicalEasyFamily_supportEasy p t ht))
    exact W.hCorrect.1 _ hYesMem
  have hRejectZero : canonicalEasyRejectProbOnFamily W = 0 := by
    simpa [canonicalEasyRejectProbOnFamily] using
      canonicalEasyRejectProbOnFamilyOfCircuit_eq_zero_of_forall_accept
        (p := p) (D := W.C) hAllFamilyAccept
  rw [hRejectZero] at hDensity
  have : ¬ (src.delta ≤ 0) := by
    linarith [src.hDeltaPos]
  exact this hDensity

/--
At one slice, witness-indexed canonical easy-density and witness-uniform-lower
contracts are equivalent.
-/
theorem canonicalWitnessEasyDensitySourceAt_iff_witnessUniformLowerSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Nonempty (CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound) ↔
      Nonempty (WitnessUniformLowerSourceAt (p := p) SizeBound) := by
  constructor
  · intro h
    rcases h with ⟨src⟩
    exact ⟨witnessUniformLowerSourceAt_of_canonicalWitnessEasyDensitySourceAt src⟩
  · intro h
    rcases h with ⟨src⟩
    exact ⟨canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt src⟩

/--
Shared \"image + easiness\" core between acceptance-only and full
distributional PRG certificates.
-/
structure EasyImageCoreAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  hInject : Function.Injective gen
  hLarge :
    Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ seedLen
  hAcceptSeeds :
    ∀ z : Core.BitVec seedLen,
      witnessAcceptsTotalTable W (gen z) = true

/--
Image-acceptance certificates are a strict weakening of the new distributional
endpoint: they provide no pseudorandomness transfer by themselves.

This constructor records only the common part (`seedLen`, `gen`, injectivity,
and accepted/easy support).
-/
def easyImageCore_of_prgImageAcceptanceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε}
    (cert : PRGImageAcceptanceAt W) :
    EasyImageCoreAt W := by
  refine
    { seedLen := cert.seedLen
      gen := cert.gen
      hInject := cert.hInject
      hLarge := cert.hLarge
      hAcceptSeeds := ?_ }
  intro z
  simpa [witnessAcceptsTotalTable] using cert.hAccept z

/--
If all seeds are accepted pointwise, seed acceptance probability equals `1`.
-/
theorem dagSeedAcceptanceProbOnTotals_eq_one_of_forall_accept
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {seedLen : Nat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    {gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)}
    (hAccept : ∀ z, witnessAcceptsTotalTable W (gen z) = true) :
    dagSeedAcceptanceProbOnTotals W gen = 1 := by
  classical
  have hFilter :
      (Finset.univ : Finset (Core.BitVec seedLen)).filter
          (fun z => witnessAcceptsTotalTable W (gen z) = true)
        = (Finset.univ : Finset (Core.BitVec seedLen)) := by
    ext z
    simp [hAccept z]
  have hCardNeNat :
      ((Finset.univ : Finset (Core.BitVec seedLen)).card) ≠ 0 := by
    simp
  simpa [dagSeedAcceptanceProbOnTotals, dagSeedAcceptanceProbOnTotalsOfCircuit,
    acceptanceRatioOnFinset, hFilter]

/--
Specialization of
`dagSeedAcceptanceProbOnTotals_eq_one_of_forall_accept` to `EasyImageCoreAt`.
-/
theorem dagSeedAcceptanceProbOnTotals_eq_one_of_easyImageCoreAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (core : EasyImageCoreAt W) :
    dagSeedAcceptanceProbOnTotals W core.gen = 1 := by
  exact dagSeedAcceptanceProbOnTotals_eq_one_of_forall_accept core.hAcceptSeeds

/--
Distributional easy-image endpoint (consumer-side).

Important: this is the minimal endpoint required by the counting-closed
distributional contradiction route. In particular, injectivity / large-image
fields are intentionally *not* part of this structure.
-/
structure EasyImagePRGAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) where
  seedLen : Nat
  gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n)
  hSupportEasy :
    ∀ z : Core.BitVec seedLen,
      PartialMCSP_YES p (totalTableToPartial (gen z))
  epsilon : Rat
  hEpsNonneg : 0 ≤ epsilon
  hFoolingAtWitness :
    |dagUniformAcceptanceProbOnTotals W -
      dagSeedAcceptanceProbOnTotals W gen| ≤ epsilon

/--
Lower-transfer lemma extracted from `EasyImagePRGAt`.
-/
theorem dagUniformAcceptanceProbOnTotals_ge_one_sub_epsilon_of_easyImagePRGAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (cert : EasyImagePRGAt W) :
    1 - cert.epsilon ≤ dagUniformAcceptanceProbOnTotals W := by
  have hAcceptSeeds :
      ∀ z : Core.BitVec cert.seedLen,
        witnessAcceptsTotalTable W (cert.gen z) = true := by
    intro z
    have hYesMem : encodeTotalAsPartial (cert.gen z) ∈ (gapSliceOfParams p).Yes := by
      simpa [gapSliceOfParams] using
        (gapPartialMCSP_yes_of_small p (encodeTotalAsPartial (cert.gen z))
          (by simpa [decodePartial_encodeTotal] using cert.hSupportEasy z))
    have hEvalTrue : DagCircuit.eval W.C (encodeTotalAsPartial (cert.gen z)) = true :=
      W.hCorrect.1 _ hYesMem
    simpa [witnessAcceptsTotalTable] using hEvalTrue
  have hSeedOne :
      dagSeedAcceptanceProbOnTotals W cert.gen = 1 :=
    dagSeedAcceptanceProbOnTotals_eq_one_of_forall_accept hAcceptSeeds
  have hAbs :
      |dagUniformAcceptanceProbOnTotals W -
        dagSeedAcceptanceProbOnTotals W cert.gen| ≤ cert.epsilon :=
    cert.hFoolingAtWitness
  rw [hSeedOne] at hAbs
  have hLeft :
      -cert.epsilon ≤ dagUniformAcceptanceProbOnTotals W - 1 :=
    (abs_le.mp hAbs).1
  linarith

/--
One-shot contradiction from a distributional easy-image PRG certificate and a
strict upper bound on uniform acceptance at the witness.
-/
theorem no_small_dag_solver_of_easyImagePRGAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : EasyImagePRGAt W)
    (hUpper :
      dagUniformAcceptanceProbOnTotals W < 1 - cert.epsilon) :
    False := by
  have hLower :
      1 - cert.epsilon ≤ dagUniformAcceptanceProbOnTotals W :=
    dagUniformAcceptanceProbOnTotals_ge_one_sub_epsilon_of_easyImagePRGAt cert
  exact (not_lt_of_ge hLower) hUpper

/--
Counting upper bound on witness acceptance probability over uniform total
tables.

Any accepted total table cannot be a NO-instance (by correctness on NO). Hence
the accepted set has cardinality at most `circuitCountBound`, and dividing by
the full table count yields the ratio bound.
-/
theorem dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    dagUniformAcceptanceProbOnTotals W ≤
      (Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat) := by
  classical
  let accepted : Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
    (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).filter
      (fun t => witnessAcceptsTotalTable W t = true)
  have hCardLe : accepted.card ≤ Models.circuitCountBound p.n (p.sNO - 1) := by
    by_contra hNotLe
    have hLarge : Models.circuitCountBound p.n (p.sNO - 1) < accepted.card :=
      lt_of_not_ge hNotLe
    rcases Counting.exists_hard_function_of_large_family p accepted hLarge with
      ⟨g, hgAcc, hNo⟩
    have hEvalTrue : witnessAcceptsTotalTable W g = true := by
      have hMemFilter :
          g ∈ (Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).filter
              (fun t => witnessAcceptsTotalTable W t = true) := by
        simpa [accepted] using hgAcc
      exact (Finset.mem_filter.mp hMemFilter).2
    have hNoDecode :
        PartialMCSP_NO p (decodePartial (encodeTotalAsPartial g)) := by
      simpa [decodePartial_encodeTotal] using hNo
    have hNoMem : encodeTotalAsPartial g ∈ (gapSliceOfParams p).No := by
      simpa [gapSliceOfParams] using
        (gapPartialMCSP_no_of_large p (encodeTotalAsPartial g) hNoDecode)
    have hEvalFalse : DagCircuit.eval W.C (encodeTotalAsPartial g) = false :=
      W.hCorrect.2 _ hNoMem
    have : DagCircuit.eval W.C (encodeTotalAsPartial g) = true := by
      simpa [witnessAcceptsTotalTable] using hEvalTrue
    have hContra : true = false := this.symm.trans hEvalFalse
    cases hContra
  have hDenCard :
      (((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat) =
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) := by
    simp
  unfold dagUniformAcceptanceProbOnTotals
  simp [acceptanceRatioOnFinset]
  have hNumRat :
      ((accepted.card : Rat) ≤ (Models.circuitCountBound p.n (p.sNO - 1) : Rat)) := by
    exact_mod_cast hCardLe
  have hDenNonneg :
      (0 : Rat) ≤
        (((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat)) := by
    positivity
  have hDiv :
      ((accepted.card : Rat) /
          ((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat)) ≤
        ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
          ((Finset.univ : Finset (Core.BitVec (Models.Partial.tableLen p.n))).card : Rat)) :=
    div_le_div_of_nonneg_right hNumRat hDenNonneg
  simpa [dagUniformAcceptanceProbOnTotals, dagUniformAcceptanceProbOnTotalsOfCircuit,
    acceptanceRatioOnFinset, hDenCard] using hDiv

/--
Numeric separation forced by a YES-subcube certificate:
the canonical subcube density is strictly larger than the counting upper ratio
`circuitCountBound / 2^tableLen`.

This is the pure quantitative core extracted from `cert.hSlack`.
-/
theorem subcubeRatio_gt_countRatio_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : YesSubcubeCertificateAt W) :
    ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
    ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat)) := by
  have hNum :
      (Models.circuitCountBound p.n (p.sNO - 1) : Rat) <
        (2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) := by
    exact_mod_cast cert.hSlack
  have hDenPos : (0 : Rat) < (2 ^ (Models.Partial.tableLen p.n) : Rat) := by
    positivity
  exact div_lt_div_of_pos_right hNum hDenPos

/--
Quantitative upgrade: a YES-subcube certificate forces uniform acceptance to be
strictly above the counting ratio.
-/
theorem dagUniformAcceptanceProbOnTotals_gt_countRatio_of_yesSubcubeCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : YesSubcubeCertificateAt W) :
    ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
      dagUniformAcceptanceProbOnTotals W := by
  have hCountLtSubcube :
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
      ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) :=
    subcubeRatio_gt_countRatio_of_yesSubcubeCertificateAt W cert
  have hSubcubeLeUniform :
      ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) ≤
          dagUniformAcceptanceProbOnTotals W :=
    dagUniformAcceptanceProbOnTotals_ge_subcubeRatio_of_yesSubcubeCertificateAt W cert
  exact lt_of_lt_of_le hCountLtSubcube hSubcubeLeUniform

/--
Direct contradiction route using only quantitative bounds:
YES-subcube gives a strict lower bound, while correctness gives a matching
counting upper bound.
-/
theorem no_small_dag_solver_of_yesSubcubeCertificateAt_via_uniform_counting
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : YesSubcubeCertificateAt W) :
    False := by
  have hLower :
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
        dagUniformAcceptanceProbOnTotals W :=
    dagUniformAcceptanceProbOnTotals_gt_countRatio_of_yesSubcubeCertificateAt W cert
  have hUpper :
      dagUniformAcceptanceProbOnTotals W ≤
        (Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat) :=
    dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness W
  exact (not_lt_of_ge hUpper) hLower

/--
Closing form of the one-shot contradiction where the required `hUpper` is
internalized by counting.
-/
theorem no_small_dag_solver_of_easyImagePRGAt_of_counting
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : EasyImagePRGAt W)
    (hEpsSmall :
      cert.epsilon <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat))) :
    False := by
  have hCountUpper :
      dagUniformAcceptanceProbOnTotals W ≤
        (Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
          (2 ^ (Models.Partial.tableLen p.n) : Rat) :=
    dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness W
  have hUpper :
      dagUniformAcceptanceProbOnTotals W < 1 - cert.epsilon := by
    have hRatioLt :
        ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
          (2 ^ (Models.Partial.tableLen p.n) : Rat)) < 1 - cert.epsilon := by
      linarith
    exact lt_of_le_of_lt hCountUpper hRatioLt
  exact no_small_dag_solver_of_easyImagePRGAt W cert hUpper

/--
Counting-closed contradiction from the minimal transfer endpoint.
-/
theorem no_small_dag_solver_of_easyImageTransferAt_of_counting
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (tr : EasyImageTransferAt W)
    (hEpsSmall :
      tr.epsilon <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat))) :
    False := by
  have hCountUpper :
      dagUniformAcceptanceProbOnTotals W ≤
        (Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
          (2 ^ (Models.Partial.tableLen p.n) : Rat) :=
    dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness W
  have hUpper : dagUniformAcceptanceProbOnTotals W < 1 - tr.epsilon := by
    have hRatioLt :
        ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
          (2 ^ (Models.Partial.tableLen p.n) : Rat)) < 1 - tr.epsilon := by
      linarith
    exact lt_of_le_of_lt hCountUpper hRatioLt
  exact (not_lt_of_ge tr.hUniformLower) hUpper

/--
Helper constructor from source-style assumptions to `EasyImagePRGAt`.

Pointwise seed acceptance is derived automatically from easy support and
witness correctness.
-/
def easyImagePRGAt_of_supportEasy_and_fooling
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (seedLen : Nat)
    (gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n))
    (hSupportEasy :
      ∀ z : Core.BitVec seedLen,
        PartialMCSP_YES p (totalTableToPartial (gen z)))
    (epsilon : Rat)
    (hEpsNonneg : 0 ≤ epsilon)
    (hFoolingAtWitness :
      |dagUniformAcceptanceProbOnTotals W -
        dagSeedAcceptanceProbOnTotals W gen| ≤ epsilon) :
    EasyImagePRGAt W := by
  refine
    { seedLen := seedLen
      gen := gen
      hSupportEasy := hSupportEasy
      epsilon := epsilon
      hEpsNonneg := hEpsNonneg
      hFoolingAtWitness := hFoolingAtWitness }

/--
Compile a source-level (`DAG`-quantified) easy-image fooling object into a
witness-level endpoint certificate.

This is the key source→endpoint adapter: source theorems can remain stated over
all small DAGs, while downstream contradiction machinery consumes
`EasyImagePRGAt W`.
-/
def easyImagePRGAt_of_smallDAGEasyImageFoolingSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyImageFoolingSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImagePRGAt W := by
  have hFoolingAtWitness :
      |dagUniformAcceptanceProbOnTotals W -
        dagSeedAcceptanceProbOnTotals W source.gen| ≤ source.epsilon := by
    simpa [dagUniformAcceptanceProbOnTotals, dagSeedAcceptanceProbOnTotals] using
      source.hFoolsSmall W.C W.hSize
  have hEpsNonneg : 0 ≤ source.epsilon := by
    have hAbsNonneg :
        0 ≤
          |dagUniformAcceptanceProbOnTotals W -
            dagSeedAcceptanceProbOnTotals W source.gen| := by
      positivity
    exact le_trans hAbsNonneg hFoolingAtWitness
  exact
    easyImagePRGAt_of_supportEasy_and_fooling
      (W := W)
      source.seedLen source.gen
      source.hSupportEasy source.epsilon hEpsNonneg hFoolingAtWitness

/--
Compile the minimal canonical distributional source object to consumer-side
`EasyImagePRGAt`.
-/
def easyImagePRGAt_of_smallDAGEasyDistSourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyDistSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImagePRGAt W := by
  have hFoolingAtWitness :
      |dagUniformAcceptanceProbOnTotals W -
        dagSeedAcceptanceProbOnTotals W source.gen| ≤ source.epsilon := by
    simpa [dagUniformAcceptanceProbOnTotals, dagSeedAcceptanceProbOnTotals] using
      source.hFoolsSmall W.C W.hSize
  have hEpsNonneg : 0 ≤ source.epsilon := by
    have hAbsNonneg :
        0 ≤
          |dagUniformAcceptanceProbOnTotals W -
            dagSeedAcceptanceProbOnTotals W source.gen| := by
      positivity
    exact le_trans hAbsNonneg hFoolingAtWitness
  exact
    easyImagePRGAt_of_supportEasy_and_fooling
      (W := W)
      source.seedLen source.gen
      source.hSupportEasy source.epsilon hEpsNonneg hFoolingAtWitness

/--
The Shannon-counting side condition in `GapPartialMCSPParams` implies that the
count-ratio upper bound leaves at least a quarter of slack.
-/
theorem quarter_lt_one_sub_countRatio_of_circuit_bound_ok
    (p : GapPartialMCSPParams) :
    (1 / 4 : Rat) <
      1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
            (2 ^ (Models.Partial.tableLen p.n) : Rat)) := by
  let L : Nat := Models.Partial.tableLen p.n
  have hLge4 : 4 ≤ L := by
    dsimp [L, Models.Partial.tableLen]
    have hn : 2 ≤ p.n := le_trans (by decide : 2 ≤ 8) p.n_large
    have hpow : 2 ^ 2 ≤ 2 ^ p.n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    simpa using hpow
  have hHalfLe : L / 2 + 2 ≤ L := by omega
  have hPowLeNat : 2 ^ (L / 2) * 4 ≤ 2 ^ L := by
    calc
      2 ^ (L / 2) * 4 = 2 ^ (L / 2) * 2 ^ 2 := by norm_num
      _ = 2 ^ (L / 2 + 2) := by rw [Nat.pow_add]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hHalfLe
  have hCountLtNat :
      Models.circuitCountBound p.n (p.sNO - 1) * 4 < 2 ^ L := by
    have hcount :
        Models.circuitCountBound p.n (p.sNO - 1) < 2 ^ (L / 2) := by
      simpa [L] using p.circuit_bound_ok
    have hMulLt :
        Models.circuitCountBound p.n (p.sNO - 1) * 4 <
          2 ^ (L / 2) * 4 :=
      Nat.mul_lt_mul_of_pos_right hcount (by decide : 0 < 4)
    exact lt_of_lt_of_le hMulLt hPowLeNat
  have hCountRat :
      ((Models.circuitCountBound p.n (p.sNO - 1) * 4 : Nat) : Rat) <
        ((2 ^ L : Nat) : Rat) := by
    exact_mod_cast hCountLtNat
  have hDenPosRat : (0 : Rat) < ((2 ^ L : Nat) : Rat) := by positivity
  have hDivLtOne :
      (((Models.circuitCountBound p.n (p.sNO - 1) * 4 : Nat) : Rat) /
        ((2 ^ L : Nat) : Rat)) < 1 := by
    exact (div_lt_one hDenPosRat).2 hCountRat
  have hRatioLtQuarter :
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        ((2 ^ L : Nat) : Rat)) < (1 / 4 : Rat) := by
    let c : Rat := (Models.circuitCountBound p.n (p.sNO - 1) : Rat)
    let d : Rat := ((2 ^ L : Nat) : Rat)
    have hdPos : (0 : Rat) < d := by
      simpa [d] using hDenPosRat
    have hdNe : d ≠ 0 := ne_of_gt hdPos
    have hDivLtOne' : (c * 4) / d < 1 := by
      simpa [c, d, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hDivLtOne
    have hMulLtOne : (4 : Rat) * (c / d) < 1 := by
      calc
        (4 : Rat) * (c / d) = (c * 4) / d := by
          field_simp [hdNe]
          ring
        _ < 1 := hDivLtOne'
    have hRatioLt : c / d < (1 / 4 : Rat) := by
      nlinarith [hMulLtOne]
    simpa [c, d] using hRatioLt
  have hCountRatioLtQuarter :
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) < (1 / 4 : Rat) := by
    simpa [L] using hRatioLtQuarter
  linarith

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
Slice-family provider for witness-indexed distributional easy-image PRG
certificates.
-/
abbrev easyImagePRGAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      EasyImagePRGAt W

/--
Slice-family provider for witness-level minimal one-sided transfer endpoints.
-/
abbrev easyImageTransferAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      EasyImageTransferAt W

/--
Slice-family provider for source-level easy-image fooling objects against all
small DAGs on each slice.
-/
abbrev smallDAGEasyImageFoolingSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    SmallDAGEasyImageFoolingSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Slice-family provider for the minimal canonical distributional source target.
-/
abbrev smallDAGEasyDistSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    SmallDAGEasyDistSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Slice-family provider for one-sided easy-HSG source objects on each slice.
-/
abbrev smallDAGEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    SmallDAGEasyHSGSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Slice-family provider for canonical easy-density source objects.
-/
abbrev canonicalSmallDAGEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    CanonicalSmallDAGEasyDensitySourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Slice-family provider for witness-indexed canonical easy-density sources.
-/
abbrev canonicalWitnessEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    CanonicalWitnessEasyDensitySourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Slice-family provider for witness-indexed uniform-lower source objects.
-/
abbrev witnessUniformLowerSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    WitnessUniformLowerSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Quarter-bounded transfer provider predicate.

It packages a witness-level transfer provider together with the key quantitative
fact needed for the uniform-lower core: all produced transfer epsilons are at
most `1/4`.
-/
abbrev easyImageTransferQuarterProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hTr : easyImageTransferAtProviderOnSlices F SizeBound) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat,
    ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
      (hTr n β ε W).epsilon ≤ (1 / 4 : Rat)

/--
Packaged quarter-bounded transfer provider on slices.
-/
structure EasyImageTransferQuarterBundleOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) where
  hTr : easyImageTransferAtProviderOnSlices F SizeBound
  hQuarter : easyImageTransferQuarterProviderOnSlices F SizeBound hTr

/--
Lift the single-slice extraction-budget constructor to a slice-family provider.

This packages the exact local data needed to instantiate
`canonicalWitnessEasyDensitySourceAt_of_extractionBudget` independently on each
slice `(n, β)`.
-/
noncomputable def canonicalWitnessEasyDensitySourceProviderOnSlices_of_extractionBudget
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
    (hBudget :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (canonicalValueAliveSet (hExtract n β ε W)).card ≤ hardwireBudgetOf n β) :
    canonicalWitnessEasyDensitySourceProviderOnSlices F SizeBound := by
  intro n β
  exact canonicalWitnessEasyDensitySourceAt_of_extractionBudget
    (p := F.paramsOf n β)
    (SizeBound := fun ε' s => SizeBound n β ε' s)
    (epsilonOf n β)
    (hEpsQuarter n β)
    (hEpsNonneg n β)
    (hardwireBudgetOf n β)
    (hCoverBudget n β)
    (hExtract := fun {εslice} W => hExtract n β εslice W)
    (hBudget := fun {εslice} W => hBudget n β εslice W)

/--
Support-budget specialization of
`canonicalWitnessEasyDensitySourceProviderOnSlices_of_extractionBudget`.
-/
noncomputable def canonicalWitnessEasyDensitySourceProviderOnSlices_of_supportBudget
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hSupportBudget :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (DagCircuit.support W.C).card ≤ hardwireBudgetOf n β) :
    canonicalWitnessEasyDensitySourceProviderOnSlices F SizeBound := by
  intro n β
  exact canonicalWitnessEasyDensitySourceAt_of_supportBudget
    (p := F.paramsOf n β)
    (SizeBound := fun ε' s => SizeBound n β ε' s)
    (epsilonOf n β)
    (hEpsQuarter n β)
    (hEpsNonneg n β)
    (hardwireBudgetOf n β)
    (hCoverBudget n β)
    (hSupportBudget := fun {εslice} W => hSupportBudget n β εslice W)

/--
Provider-level compiler:
witness-indexed canonical easy-density sources -> witness-uniform-lower
sources.
-/
def witnessUniformLowerSourceProviderOnSlices_of_canonicalWitnessEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hDensity : canonicalWitnessEasyDensitySourceProviderOnSlices F SizeBound) :
    witnessUniformLowerSourceProviderOnSlices F SizeBound := by
  intro n β
  exact witnessUniformLowerSourceAt_of_canonicalWitnessEasyDensitySourceAt
    (hDensity n β)

/--
Provider-level compiler:
witness-indexed canonical easy-density sources -> quarter-bounded witness
transfer bundles.
-/
def easyImageTransferQuarterBundleOnSlices_of_canonicalWitnessEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hDensity : canonicalWitnessEasyDensitySourceProviderOnSlices F SizeBound) :
    EasyImageTransferQuarterBundleOnSlices F SizeBound := by
  refine
    { hTr := ?_
      hQuarter := ?_ }
  · intro n β ε W
    exact easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
      (source := hDensity n β) W
  · intro n β ε W
    let tr : EasyImageTransferAt W :=
      easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
        (source := hDensity n β) W
    have hQuarter : tr.epsilon ≤ (1 / 4 : Rat) := by
      simpa [tr] using (hDensity n β).hEpsQuarter
    simpa [tr] using hQuarter

/--
Slice-family provider for upstream average-case / semantic-sampling sources.
-/
abbrev smallDAGAverageCaseHardnessSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Type :=
  ∀ n : Nat, ∀ β : Rat,
    SmallDAGAverageCaseHardnessSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => SizeBound n β ε' s)

/--
Canonical source statement at the `ppolyDAG` size bound for one `hInDag`.

This is the exact remaining source-theorem target for the unrestricted-DAG
mainline.
-/
abbrev CanonicalSmallDAGEasyImageSourceStatement
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) : Type :=
  smallDAGEasyDistSourceProviderOnSlices
    F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Canonical average-case/hardness source target at `ppolyDAG` slice bounds.
-/
abbrev CanonicalSmallDAGAvgHardnessSourceStatement
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) : Type :=
  smallDAGAverageCaseHardnessSourceProviderOnSlices
    F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Canonical one-sided easy-HSG source target at `ppolyDAG` slice bounds.
-/
abbrev CanonicalSmallDAGEasyHSGSourceStatement
    (F : GapSliceFamily)
    (hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) : Type :=
  (∀ n : Nat, ∀ β : Rat,
    CanonicalSmallDAGEasyHSGSourceAt
      (p := F.paramsOf n β)
      (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s))
  
/--
Compile a canonical (fixed-sampler) easy-HSG provider into the generic
`SmallDAGEasyHSGSourceAt` provider expected by downstream weak-route closures.
-/
def smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCanonical :
      ∀ n : Nat, ∀ β : Rat,
        CanonicalSmallDAGEasyHSGSourceAt
          (p := F.paramsOf n β)
          (fun ε' s => SizeBound n β ε' s)) :
    smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  fun n β =>
    smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt (hCanonical n β)

/--
Compile a canonical easy-density source provider into a generic one-sided HSG
source provider.
-/
def smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCanonicalDensity :
      canonicalSmallDAGEasyDensitySourceProviderOnSlices F SizeBound) :
    smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  fun n β =>
    smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt
      (canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt
        (hCanonicalDensity n β))

/--
Global canonical source-theorem debt, factored as one explicit proposition.

When this proposition is proved unconditionally, the downstream chain is already
closed by existing compilers/wrappers.
-/
abbrev canonical_smallDAG_easyImage_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    CanonicalSmallDAGEasyImageSourceStatement F hInDag

/--
Global canonical easy-density source debt (preferred primary theorem target).
-/
abbrev canonical_smallDAG_easyDensity_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    canonicalSmallDAGEasyDensitySourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Global witness-indexed canonical easy-density source debt.

This is a weaker variant of
`canonical_smallDAG_easyDensity_source_on_slices`: instead of requiring the
density inequality for *all* size-bounded DAG circuits, it only asks for the
inequality on concrete slice witnesses (`SmallDAGWitnessOnSlice`).

Why this matters for Gate G1:
- many DAG-side semantic/locality arguments naturally produce witness-indexed
  bounds first;
- the weak-route contradiction chain already consumes witness-level transfer;
- so this debt can serve as a practically easier attack surface when the full
  all-circuits theorem is not yet available.
-/
abbrev canonical_smallDAG_witnessEasyDensity_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    canonicalWitnessEasyDensitySourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Global witness-indexed uniform-lower source debt.

This is a strong sufficient condition for
`canonical_smallDAG_witnessEasyDensity_source_on_slices`.
-/
abbrev canonical_smallDAG_witnessUniformLower_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    witnessUniformLowerSourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Global quarter-bounded witness-transfer debt at canonical `ppolyDAG` bounds.
-/
abbrev canonical_smallDAG_witnessTransferQuarter_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
      EasyImageTransferQuarterBundleOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag)

/--
Canonical witness-indexed easy-density debt from extraction-budget data on the
canonical `ppolyDAG` size surface.
-/
noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_extractionBudget
    (F : GapSliceFamily)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hExtract :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessRestrictionExtractionProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag))
    (hBudget :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β : Rat, ∀ ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (canonicalValueAliveSet (((hExtract hInDag) n β) ε W)).card ≤
              hardwireBudgetOf n β) :
    canonical_smallDAG_witnessEasyDensity_source_on_slices F := by
  intro hInDag
  exact canonicalWitnessEasyDensitySourceProviderOnSlices_of_extractionBudget
    F (ppolyDAGSizeBoundOnSlices F hInDag)
    epsilonOf hardwireBudgetOf
    hEpsQuarter hEpsNonneg hCoverBudget
    (hExtract hInDag)
    (fun n β ε W => hBudget hInDag n β ε W)

/--
Canonical witness-indexed easy-density debt from support-budget data on the
canonical `ppolyDAG` size surface.
-/
noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget
    (F : GapSliceFamily)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hSupportBudget :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β : Rat, ∀ ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤ hardwireBudgetOf n β) :
    canonical_smallDAG_witnessEasyDensity_source_on_slices F := by
  intro hInDag
  exact canonicalWitnessEasyDensitySourceProviderOnSlices_of_supportBudget
    F (ppolyDAGSizeBoundOnSlices F hInDag)
    epsilonOf hardwireBudgetOf
    hEpsQuarter hEpsNonneg hCoverBudget
    (fun n β ε W => hSupportBudget hInDag n β ε W)

/--
Canonical witness-uniform-lower debt from support-budget data on the canonical
`ppolyDAG` size surface.
-/
noncomputable def canonical_smallDAG_witnessUniformLower_source_on_slices_of_supportBudget
    (F : GapSliceFamily)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hSupportBudget :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β : Rat, ∀ ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤ hardwireBudgetOf n β) :
    canonical_smallDAG_witnessUniformLower_source_on_slices F := by
  intro hInDag
  exact
    witnessUniformLowerSourceProviderOnSlices_of_canonicalWitnessEasyDensitySourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag)
      ((canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget
          F epsilonOf hardwireBudgetOf
          hEpsQuarter hEpsNonneg hCoverBudget hSupportBudget) hInDag)

/--
Canonical quarter-bounded witness-transfer debt from support-budget data on the
canonical `ppolyDAG` size surface.
-/
noncomputable def canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_supportBudget
    (F : GapSliceFamily)
    (epsilonOf : Nat → Rat → Rat)
    (hardwireBudgetOf : Nat → Rat → Nat)
    (hEpsQuarter :
      ∀ n : Nat, ∀ β : Rat, epsilonOf n β ≤ (1 / 4 : Rat))
    (hEpsNonneg :
      ∀ n : Nat, ∀ β : Rat, 0 ≤ epsilonOf n β)
    (hCoverBudget :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize (F.paramsOf n β).n (hardwireBudgetOf n β) <
          (F.paramsOf n β).sYES)
    (hSupportBudget :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β : Rat, ∀ ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤ hardwireBudgetOf n β) :
    canonical_smallDAG_witnessTransferQuarter_source_on_slices F := by
  intro hInDag
  exact
    easyImageTransferQuarterBundleOnSlices_of_canonicalWitnessEasyDensitySourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag)
      ((canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget
          F epsilonOf hardwireBudgetOf
          hEpsQuarter hEpsNonneg hCoverBudget hSupportBudget) hInDag)

/--
Specialization of the witness-indexed canonical easy-density route to the
direct support-half fallback family.

This is the thin bridge from the old Route-B style source hypothesis

`support ≤ tableLen/2`

plus the explicit hardwire-cover arithmetic at the same budget, into the new
witness-indexed density debt on canonical `ppolyDAG` slices.
-/
noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportHalfBoundFamily
    (F : GapSliceFamily)
    (hCoverBudgetHalf :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize
            (F.paramsOf n β).n
            (Models.Partial.tableLen (F.paramsOf n β).n / 2) <
          (F.paramsOf n β).sYES)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    canonical_smallDAG_witnessEasyDensity_source_on_slices F :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget
    F
    (fun _ _ => (1 / 4 : Rat))
    (fun n β => Models.Partial.tableLen (F.paramsOf n β).n / 2)
    (fun _ _ => le_rfl)
    (fun _ _ => by norm_num)
    hCoverBudgetHalf
    hSupportHalf

/--
Specialization of the witness-uniform-lower route to the same support-half
fallback family.
-/
noncomputable def canonical_smallDAG_witnessUniformLower_source_on_slices_of_supportHalfBoundFamily
    (F : GapSliceFamily)
    (hCoverBudgetHalf :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize
            (F.paramsOf n β).n
            (Models.Partial.tableLen (F.paramsOf n β).n / 2) <
          (F.paramsOf n β).sYES)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    canonical_smallDAG_witnessUniformLower_source_on_slices F :=
  canonical_smallDAG_witnessUniformLower_source_on_slices_of_supportBudget
    F
    (fun _ _ => (1 / 4 : Rat))
    (fun n β => Models.Partial.tableLen (F.paramsOf n β).n / 2)
    (fun _ _ => le_rfl)
    (fun _ _ => by norm_num)
    hCoverBudgetHalf
    hSupportHalf

/--
Specialization of the quarter-bounded witness-transfer route to the same
support-half fallback family.
-/
noncomputable def canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_supportHalfBoundFamily
    (F : GapSliceFamily)
    (hCoverBudgetHalf :
      ∀ n : Nat, ∀ β : Rat,
        hardwireCircuitSize
            (F.paramsOf n β).n
            (Models.Partial.tableLen (F.paramsOf n β).n / 2) <
          (F.paramsOf n β).sYES)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    canonical_smallDAG_witnessTransferQuarter_source_on_slices F :=
  canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_supportBudget
    F
    (fun _ _ => (1 / 4 : Rat))
    (fun n β => Models.Partial.tableLen (F.paramsOf n β).n / 2)
    (fun _ _ => le_rfl)
    (fun _ _ => by norm_num)
    hCoverBudgetHalf
    hSupportHalf

/--
Global compiler:
witness-uniform-lower debt -> witness-indexed canonical easy-density debt.
-/
def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
    (F : GapSliceFamily)
    (hUniform : canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    canonical_smallDAG_witnessEasyDensity_source_on_slices F := by
  intro hInDag n β
  exact canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt
    ((hUniform hInDag) n β)

/--
Compile quarter-bounded witness-level transfer providers to witness-uniform-
lower source providers.

Idea:
- each transfer witness gives `1 - tr.ε ≤ uniform`;
- if `tr.ε ≤ 1/4`, then `1 - 1/4 ≤ 1 - tr.ε`;
- thus `3/4 ≤ uniform`, i.e. uniform-lower with canonical `ε = 1/4`.
-/
def witnessUniformLowerSourceProviderOnSlices_of_easyImageTransferQuarterProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hTr : easyImageTransferAtProviderOnSlices F SizeBound)
    (hQuarter : easyImageTransferQuarterProviderOnSlices F SizeBound hTr) :
    witnessUniformLowerSourceProviderOnSlices F SizeBound := by
  intro n β
  refine
    { epsilon := (1 / 4 : Rat)
      hEpsQuarter := le_rfl
      hUniformLower := ?_ }
  intro εslice W
  let tr : EasyImageTransferAt W := hTr n β εslice W
  have hTrQuarter : tr.epsilon ≤ (1 / 4 : Rat) := by
    simpa [tr] using hQuarter n β εslice W
  have hFromTr : 1 - tr.epsilon ≤ dagUniformAcceptanceProbOnTotals W := tr.hUniformLower
  have hBridge : 1 - (1 / 4 : Rat) ≤ 1 - tr.epsilon := by linarith
  exact le_trans hBridge hFromTr

/--
Compile witness-uniform-lower providers to quarter-bounded witness-transfer
bundles.

This is the converse direction to
`witnessUniformLowerSourceProviderOnSlices_of_easyImageTransferQuarterProviderOnSlices`:
uniform-lower gives witness-easy-density (with `delta = 1`), then transfer with
the same epsilon, and finally the quarter bound follows from `hEpsQuarter`.
-/
def easyImageTransferQuarterBundleOnSlices_of_witnessUniformLowerSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hUniform : witnessUniformLowerSourceProviderOnSlices F SizeBound) :
    EasyImageTransferQuarterBundleOnSlices F SizeBound := by
  refine
    { hTr := ?_
      hQuarter := ?_ }
  · intro n β ε W
    exact easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
      (source :=
        canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt
          (hUniform n β))
      W
  · intro n β ε W
    let tr : EasyImageTransferAt W :=
      easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
        (source :=
          canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt
            (hUniform n β))
        W
    have hQuarter : tr.epsilon ≤ (1 / 4 : Rat) := by
      simpa [tr] using (hUniform n β).hEpsQuarter
    simpa [tr]
      using hQuarter

/--
Global equivalence:
witness-indexed canonical easy-density debt is equivalent to witness-uniform-
lower debt.

This theorem isolates the exact mathematical core of the G1 witness-indexed
route: proving `canonical_smallDAG_witnessEasyDensity_source_on_slices` is
precisely proving a quarter-threshold uniform acceptance lower bound object on
all canonical slices.
-/
theorem canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessUniformLower
    (F : GapSliceFamily) :
    Nonempty (canonical_smallDAG_witnessEasyDensity_source_on_slices F) ↔
      Nonempty (canonical_smallDAG_witnessUniformLower_source_on_slices F) := by
  constructor
  · intro h
    rcases h with ⟨hDensity⟩
    refine ⟨?_⟩
    intro hInDag n β
    exact witnessUniformLowerSourceAt_of_canonicalWitnessEasyDensitySourceAt
      ((hDensity hInDag) n β)
  · intro h
    rcases h with ⟨hUniform⟩
    exact ⟨canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
      F hUniform⟩

/--
Global compiler:
quarter-bounded witness-transfer debt -> witness-uniform-lower debt.
-/
def canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter
    (F : GapSliceFamily)
    (hQuarterTr : canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    canonical_smallDAG_witnessUniformLower_source_on_slices F := by
  intro hInDag
  let pack := hQuarterTr hInDag
  exact
    witnessUniformLowerSourceProviderOnSlices_of_easyImageTransferQuarterProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag) pack.hTr pack.hQuarter

/--
Global compiler:
witness-uniform-lower debt -> quarter-bounded witness-transfer debt.
-/
def canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_witnessUniformLower
    (F : GapSliceFamily)
    (hUniform : canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    canonical_smallDAG_witnessTransferQuarter_source_on_slices F := by
  intro hInDag
  exact
    easyImageTransferQuarterBundleOnSlices_of_witnessUniformLowerSourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag) (hUniform hInDag)

/--
Global equivalence:
witness-uniform-lower debt is equivalent to quarter-bounded witness-transfer
debt.
-/
theorem canonical_smallDAG_witnessUniformLower_source_on_slices_iff_witnessTransferQuarter
    (F : GapSliceFamily) :
    Nonempty (canonical_smallDAG_witnessUniformLower_source_on_slices F) ↔
      Nonempty (canonical_smallDAG_witnessTransferQuarter_source_on_slices F) := by
  constructor
  · intro h
    rcases h with ⟨hUniform⟩
    exact ⟨canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_witnessUniformLower
      F hUniform⟩
  · intro h
    rcases h with ⟨hQuarterTr⟩
    exact
      ⟨canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter
        F hQuarterTr⟩

/--
Global equivalence (composed form):
witness-indexed canonical easy-density debt is equivalent to quarter-bounded
witness-transfer debt.
-/
theorem canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessTransferQuarter
    (F : GapSliceFamily) :
    Nonempty (canonical_smallDAG_witnessEasyDensity_source_on_slices F) ↔
      Nonempty (canonical_smallDAG_witnessTransferQuarter_source_on_slices F) := by
  constructor
  · intro h
    rcases (canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessUniformLower F).1 h with
      ⟨hUniform⟩
    exact ⟨canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_witnessUniformLower
      F hUniform⟩
  · intro h
    rcases (canonical_smallDAG_witnessUniformLower_source_on_slices_iff_witnessTransferQuarter F).2 h with
      ⟨hUniform⟩
    exact ⟨canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
      F hUniform⟩

/--
Global compiler:
quarter-bounded witness-transfer debt -> witness-indexed canonical easy-density
debt.
-/
def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessTransferQuarter
    (F : GapSliceFamily)
    (hQuarterTr : canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    canonical_smallDAG_witnessEasyDensity_source_on_slices F :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
    F
    (canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter
      F hQuarterTr)

/--
Global canonical average-case/hardness source debt (upstream of easy-dist).
-/
abbrev canonical_smallDAG_avgHardness_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    CanonicalSmallDAGAvgHardnessSourceStatement F hInDag

/--
Global canonical one-sided easy-HSG source debt.

Design intent:
- this is the weakest source target currently sufficient for the counting-closed
  contradiction chain, and therefore the preferred canonical debt.
-/
abbrev canonical_smallDAG_easyHSG_source_on_slices
    (F : GapSliceFamily) : Type :=
  ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
    CanonicalSmallDAGEasyHSGSourceStatement F hInDag

/--
Global compiler from canonical easy-density debt to canonical one-sided easy-HSG
debt.

This keeps the theorem-level roadmap explicit: proving the density debt is
already sufficient to discharge the older canonical HSG debt via a thin
internal compilation step.
-/
def canonical_smallDAG_easyHSG_source_on_slices_of_canonical_smallDAG_easyDensity_source_on_slices
    (F : GapSliceFamily)
    (hDensity : canonical_smallDAG_easyDensity_source_on_slices F) :
    canonical_smallDAG_easyHSG_source_on_slices F := by
  intro hInDag n β
  exact canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt
    ((hDensity hInDag) n β)

/--
Global compiler from canonical one-sided easy-HSG debt to canonical easy-density
debt for the current singleton canonical sampler.
-/
def canonical_smallDAG_easyDensity_source_on_slices_of_canonical_smallDAG_easyHSG_source_on_slices
    (F : GapSliceFamily)
    (hHSG : canonical_smallDAG_easyHSG_source_on_slices F) :
    canonical_smallDAG_easyDensity_source_on_slices F := by
  intro hInDag n β
  exact canonicalEasyDensitySourceAt_of_canonicalEasyHSGSourceAt
    ((hHSG hInDag) n β)

/--
Compile source-level providers into witness-level endpoint providers.
-/
def easyImagePRGAtProviderOnSlices_of_smallDAGEasyImageFoolingSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound) :
    easyImagePRGAtProviderOnSlices F SizeBound :=
  fun n β ε W =>
    easyImagePRGAt_of_smallDAGEasyImageFoolingSourceAt
      (source := hSource n β) W

/--
Compile minimal canonical distributional source providers into witness-level
endpoint providers.
-/
def easyImagePRGAtProviderOnSlices_of_smallDAGEasyDistSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyDistSourceProviderOnSlices F SizeBound) :
    easyImagePRGAtProviderOnSlices F SizeBound :=
  fun n β ε W =>
    easyImagePRGAt_of_smallDAGEasyDistSourceAt
      (source := hSource n β) W

/--
Compile one-sided easy-HSG source providers into witness-level transfer
endpoint providers.
-/
def easyImageTransferAtProviderOnSlices_of_smallDAGEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyHSGSourceProviderOnSlices F SizeBound) :
    easyImageTransferAtProviderOnSlices F SizeBound :=
  fun n β ε W =>
    easyImageTransferAt_of_smallDAGEasyHSGSourceAt
      (source := hSource n β) W

/--
Compile canonical easy-density source providers directly into witness-level
transfer endpoint providers.
-/
def easyImageTransferAtProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : canonicalSmallDAGEasyDensitySourceProviderOnSlices F SizeBound) :
    easyImageTransferAtProviderOnSlices F SizeBound :=
  fun n β ε W =>
    easyImageTransferAt_of_canonicalEasyDensitySourceAt
      (source := hSource n β) W

/--
Compiler: provider-level average-case/hardness source to canonical easy-dist
provider.
-/
def smallDAGEasyDistSourceProviderOnSlices_of_avgHardnessSource
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hAvg : smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound) :
    smallDAGEasyDistSourceProviderOnSlices F SizeBound :=
  fun n β =>
    smallDAGEasyDistSourceAt_of_averageCaseHardnessSourceAt (hAvg n β)

/--
Compiler: provider-level average-case/hardness source to one-sided easy-HSG
source provider.
-/
def smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hAvg : smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound) :
    smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  fun n β =>
    smallDAGEasyHSGSourceAt_of_averageCaseHardnessSourceAt (hAvg n β)

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
Statement-level strict-mainline compiler to the canonical asymptotic Route-A1
surface.
-/
theorem smallDAGPromiseYesSubcubeStatement_of_strictSemanticsAndRequiredBudgetProvider
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hBudget :
      promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F SizeBound)) :
    SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound := by
  exact smallDAGPromiseYesSubcubeStatement_of_certificateProvider
    F SizeBound
    (promiseYesSubcubeCertificateAtProviderOnSlices_of_strictSemanticsAndRequiredBudgetProvider
      F SizeBound hBudget)

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
Gate-G1 (Route A / item 2) endpoint wrapper.

This packages the currently preferred weak accepted-family source theorem in the
exact asymptotic shape used by the final contradiction wrappers:

`∀ hInDag, SmallDAGImpliesAcceptedFamilyStatement F (ppolyDAGSizeBoundOnSlices F hInDag)`.

The theorem is intentionally thin and assumption-preserving; it exists so source
work can be tracked as "G1-closed for route A.2" without additional API layers.
-/
theorem gateG1_routeA2_acceptedFamily_of_providerFamily
    (F : GapSliceFamily)
    (hAccepted :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        acceptedFamilyCertificateAtProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGAcceptedFamilyStatement_of_certificateProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hAccepted hInDag)

/--
Canonical thin wrapper from support-half family bounds to Gate-G1 Route-A.2.

This keeps the mainline focused on one real source obligation (`hSupportHalf`)
while reusing the already closed strong-fallback bridge to the accepted-family
endpoint.
-/
theorem gateG1_routeA2_acceptedFamily_of_supportHalfBoundFamily
    (F : GapSliceFamily)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGAcceptedFamilyStatement_of_supportHalfBound
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hSupportHalf hInDag)

/--
Gate-G1 (Route A / item 1) endpoint wrapper.

Same idea as `gateG1_routeA2_acceptedFamily_of_providerFamily`, but for the
one-sided promise-YES source theorem:

`∀ hInDag, SmallDAGImpliesPromiseYesSubcubeStatement F (ppolyDAGSizeBoundOnSlices F hInDag)`.
-/
theorem gateG1_routeA1_promiseYes_of_providerFamily
    (F : GapSliceFamily)
    (hYes :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        promiseYesSubcubeCertificateAtProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesPromiseYesSubcubeStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGPromiseYesSubcubeStatement_of_certificateProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hYes hInDag)

/--
Gate-G1 Route-A.2 thin compiler from the PRG-image source route.

This is the direct backup-route realization requested by the active plan:
if the source theorem provides `PRGImageAcceptanceAt` providers on canonical
families, we immediately land in the same accepted-family endpoint used by the
default weak consumer stack.
-/
theorem gateG1_routeA2_acceptedFamily_of_prgImageProviderFamily
    (F : GapSliceFamily)
    (hPrg :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        prgImageAcceptanceAtProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hPrg hInDag)

/--
Concrete Gate-G1 Route-A.2 compiler from the strong fallback source contract.

If for each canonical `hInDag` family we can prove witness-indexed restriction
certificate data on slices, then the accepted-family source theorem required by
Gate G1 item (2) follows immediately.

This theorem is mathematically stronger than the abstract provider-family gate
wrapper above and is intended as a realistic implementation target when source
proofs naturally produce full restriction certificate data.
-/
theorem gateG1_routeA2_acceptedFamily_of_restrictionDataFamily
    (F : GapSliceFamily)
    (hData :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessRestrictionCertificateDataProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGAcceptedFamilyStatement_of_restrictionDataProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hData hInDag)

/--
Concrete Gate-G1 Route-A.2 compiler from separated extraction + numeric sources.

This is the least intrusive strong-fallback route already supported by the
current pipeline: source-side proofs may construct semantic restriction
extraction and prove numeric side data independently, and this theorem composes
them into the exact Gate G1 accepted-family endpoint.
-/
theorem gateG1_routeA2_acceptedFamily_of_restrictionExtractionAndNumericFamily
    (F : GapSliceFamily)
    (hExtract :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessRestrictionExtractionProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag))
    (hNumeric :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessRestrictionNumericDataProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)
          (hExtract hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hExtract hInDag) (hNumeric hInDag)

/--
Concrete Gate-G1 Route-A.1 compiler from pairwise promise/value packages.

When the source theorem can uniformly provide the existing pairwise
promise/value locality package for each canonical `hInDag` family, the required
promise-YES Gate G1 endpoint follows through the already-compiled bridge.
-/
theorem gateG1_routeA1_promiseYes_of_packageFamily
    (F : GapSliceFamily)
    (hPkg :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        promiseValueLocalityPackageAtProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesPromiseYesSubcubeStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact smallDAGPromiseYesSubcubeStatement_of_packageProvider
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hPkg hInDag)

/--
Route-A2 mainline synchronization lemma on the canonical DAG-size surface.

It records that the chosen extraction family and the provided numeric family are
indexed by the same `ppolyDAGSizeBoundOnSlices F hInDag`, so they can be fed
together into the extraction+numeric compiler without any coercion glue.
-/
theorem routeA2_mainline_supportExtractionAndNumeric_synchronized_onCanonicalBound
    (F : GapSliceFamily)
    (hNumeric :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessSupportNumericDataProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      smallDAGWitnessRestrictionNumericDataProviderOnSlices
        F (ppolyDAGSizeBoundOnSlices F hInDag)
        (smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support
          F (ppolyDAGSizeBoundOnSlices F hInDag)) := by
  intro hInDag
  exact smallDAGWitnessRestrictionNumericDataProviderOnSlices_of_supportNumeric
    F (ppolyDAGSizeBoundOnSlices F hInDag) (hNumeric hInDag)

/--
Route-A2 mainline closure on the canonical DAG-size surface.

This is the direct "pick one mainline and finish it" theorem for the current
sprint:
1. extraction family is fixed to the support-based constructor,
2. source work supplies only the matching numeric family,
3. closure to the exact accepted-family G1 endpoint is immediate.
-/
theorem routeA2_mainline_acceptedFamily_onCanonicalBound_of_supportExtractionAndNumericFamily
    (F : GapSliceFamily)
    (hNumeric :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessSupportNumericDataProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  intro hInDag
  exact
    smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider
      F (ppolyDAGSizeBoundOnSlices F hInDag)
      (smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support
        F (ppolyDAGSizeBoundOnSlices F hInDag))
      (routeA2_mainline_supportExtractionAndNumeric_synchronized_onCanonicalBound
        F hNumeric hInDag)

/--
Thin canonical Route-A2 closure from support-card bounds plus
`supportHalf + canonicalFactor≤1`.

This theorem deliberately avoids introducing any new endpoint shape: it builds
the required support-numeric family through
`smallDAGWitnessSupportNumericDataProviderOnSlices_onCanonicalBound_of_supportBounds_and_factorOne`
and then immediately reuses the existing
`routeA2_mainline_acceptedFamily_onCanonicalBound_of_supportExtractionAndNumericFamily`.
-/
theorem routeA2_mainline_acceptedFamily_onCanonicalBound_of_supportBounds_and_factorOne
    (F : GapSliceFamily)
    (hSupportPolylog :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Facts.LocalityLift.polylogBudget
                (Facts.LocalityLift.inputLen
                  (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β))))
    (hSupportQuarter :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Facts.LocalityLift.inputLen
                (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 4)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Facts.LocalityLift.inputLen
                (ThirdPartyFacts.toFactsParamsPartial (F.paramsOf n β)) / 2)
    (hCanonicalFactorOne :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            Nat.log2
                ((hInDag n β).polyBound (GapSliceFamily.encodedLen F n β) *
                  ((DagCircuit.support W.C).card.succ) + 2) + 1
              ≤ 1) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (Models.gapPartialMCSP_Language (F.paramsOf n β)),
      SmallDAGImpliesAcceptedFamilyStatement
        F (ppolyDAGSizeBoundOnSlices F hInDag) := by
  have hNumeric :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        smallDAGWitnessSupportNumericDataProviderOnSlices
          F (ppolyDAGSizeBoundOnSlices F hInDag) := by
    intro hInDag
    exact
      smallDAGWitnessSupportNumericDataProviderOnSlices_onCanonicalBound_of_supportBounds_and_factorOne
        F hInDag
        (hSupportPolylog hInDag)
        (hSupportQuarter hInDag)
        (hSupportHalf hInDag)
        (hCanonicalFactorOne hInDag)
  exact routeA2_mainline_acceptedFamily_onCanonicalBound_of_supportExtractionAndNumericFamily
    F hNumeric

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
Direct fallback closure from the canonical support-half family.

This is the theorem-minimal accepted-family fallback on the unrestricted-DAG
surface:

`supportHalf family -> acceptedFamily weak route -> noSmallDAG`.
-/
theorem noSmallDAG_of_supportHalfBoundFamily
    (F : GapSliceFamily)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
      ∀ n : Nat, ∀ β ε : Rat,
        ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  intro hInDag n β ε
  exact
    no_dag_solver_of_acceptedFamily
      F (ppolyDAGSizeBoundOnSlices F hInDag)
      (smallDAGAcceptedFamilyStatement_of_supportHalfBound
        F (ppolyDAGSizeBoundOnSlices F hInDag) (hSupportHalf hInDag))
      n β ε

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
Direct weak-route closure from distributional easy-image PRG providers,
using internal counting closure (no external ad-hoc upper bound).
-/
theorem noSmallDAG_of_easyImagePRGAtProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hCert : easyImagePRGAtProviderOnSlices F SizeBound)
    (hEpsSmall :
      ∀ n : Nat, ∀ β ε : Rat,
        ∀ W : SmallDAGWitnessOnSlice
          (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
          (hCert n β ε W).epsilon <
            1 - ((Models.circuitCountBound (F.paramsOf n β).n
                    ((F.paramsOf n β).sNO - 1) : Rat) /
                  (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat))) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  exact no_small_dag_solver_of_easyImagePRGAt_of_counting W (hCert n β ε W)
    (hEpsSmall n β ε W)

/--
Direct weak-route closure from source-level easy-image fooling providers.

The epsilon-smallness side condition is discharged internally from:
1. source field `hEpsQuarter`, and
2. counting-budget field `circuit_bound_ok` in slice parameters.
-/
theorem noSmallDAG_of_smallDAGEasyImageFoolingSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let cert : EasyImagePRGAt W :=
    easyImagePRGAt_of_smallDAGEasyImageFoolingSourceAt (source := hSource n β) W
  have hEpsSmall :
      cert.epsilon <
        1 - ((Models.circuitCountBound (F.paramsOf n β).n
                ((F.paramsOf n β).sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) := by
    have hQuarter :
        (1 / 4 : Rat) <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) :=
      quarter_lt_one_sub_countRatio_of_circuit_bound_ok (F.paramsOf n β)
    have hEpsQuarter' : cert.epsilon ≤ (1 / 4 : Rat) := by
      simpa [cert] using (hSource n β).hEpsQuarter
    exact lt_of_le_of_lt hEpsQuarter' hQuarter
  exact no_small_dag_solver_of_easyImagePRGAt_of_counting W cert hEpsSmall

/--
Direct weak-route closure from one-sided easy-HSG source providers.

This route is strictly weaker than the distributional route: it compiles the
source directly to `EasyImageTransferAt` and uses only one-sided lower transfer
plus counting closure.
-/
theorem noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyHSGSourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let tr : EasyImageTransferAt W :=
    easyImageTransferAt_of_smallDAGEasyHSGSourceAt (source := hSource n β) W
  have hEpsSmall :
      tr.epsilon <
        1 - ((Models.circuitCountBound (F.paramsOf n β).n
                ((F.paramsOf n β).sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) := by
    have hQuarter :
        (1 / 4 : Rat) <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) :=
      quarter_lt_one_sub_countRatio_of_circuit_bound_ok (F.paramsOf n β)
    have hEpsQuarter' : tr.epsilon ≤ (1 / 4 : Rat) := by
      simpa [tr] using (hSource n β).hEpsQuarter
    exact lt_of_le_of_lt hEpsQuarter' hQuarter
  exact no_small_dag_solver_of_easyImageTransferAt_of_counting W tr hEpsSmall

/--
Direct weak-route closure from the minimal canonical distributional source
provider (without injective/large-image obligations).
-/
theorem noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : smallDAGEasyDistSourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let cert : EasyImagePRGAt W :=
    easyImagePRGAt_of_smallDAGEasyDistSourceAt (source := hSource n β) W
  have hEpsSmall :
      cert.epsilon <
        1 - ((Models.circuitCountBound (F.paramsOf n β).n
                ((F.paramsOf n β).sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) := by
    have hQuarter :
        (1 / 4 : Rat) <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) :=
      quarter_lt_one_sub_countRatio_of_circuit_bound_ok (F.paramsOf n β)
    have hEpsQuarter' : cert.epsilon ≤ (1 / 4 : Rat) := by
      simpa [cert] using (hSource n β).hEpsQuarter
    exact lt_of_le_of_lt hEpsQuarter' hQuarter
  exact no_small_dag_solver_of_easyImagePRGAt_of_counting W cert hEpsSmall

/--
Direct weak-route closure from canonical easy-density source providers.

This is the density-first closure route:

`canonical density source -> canonical HSG compiler -> transfer -> counting`.
-/
theorem noSmallDAG_of_canonicalSmallDAGEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : canonicalSmallDAGEasyDensitySourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact
    noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
      F SizeBound
      (smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices
        F SizeBound hSource)

/--
Direct weak-route closure from witness-indexed canonical easy-density source
providers.

Compared with `noSmallDAG_of_canonicalSmallDAGEasyDensitySourceProviderOnSlices`
this route avoids the intermediate all-circuits source object and compiles
directly to transfer at witness level.
-/
theorem noSmallDAG_of_canonicalWitnessEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hSource : canonicalWitnessEasyDensitySourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  intro n β ε hExists
  rcases hExists with ⟨C, hSize, hCorrect⟩
  let W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε := {
    C := C
    hSize := hSize
    hCorrect := hCorrect
  }
  let tr : EasyImageTransferAt W :=
    easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
      (source := hSource n β) W
  have hEpsSmall :
      tr.epsilon <
        1 - ((Models.circuitCountBound (F.paramsOf n β).n
                ((F.paramsOf n β).sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) := by
    have hQuarter :
        (1 / 4 : Rat) <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat)) :=
      quarter_lt_one_sub_countRatio_of_circuit_bound_ok (F.paramsOf n β)
    have hEpsQuarter' : tr.epsilon ≤ (1 / 4 : Rat) := by
      simpa [tr] using (hSource n β).hEpsQuarter
    exact lt_of_le_of_lt hEpsQuarter' hQuarter
  exact no_small_dag_solver_of_easyImageTransferAt_of_counting W tr hEpsSmall

/--
Weak-route closure specialized to the global witness-indexed canonical
easy-density debt at `ppolyDAG` size bounds.

This is the witness-indexed sibling of
`noSmallDAG_of_canonical_smallDAG_easyDensity_source_on_slices`.
-/
theorem noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices
    (F : GapSliceFamily)
    (hCanonical : canonical_smallDAG_witnessEasyDensity_source_on_slices F) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
      ∀ n : Nat, ∀ β ε : Rat,
        ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  intro hInDag n β ε
  exact
    noSmallDAG_of_canonicalWitnessEasyDensitySourceProviderOnSlices
      F (ppolyDAGSizeBoundOnSlices F hInDag) (hCanonical hInDag) n β ε

/--
Direct weak-route closure from the global quarter-bounded witness-transfer debt.

This theorem is intentionally thin and composes only already-proved compilers:

`witnessTransferQuarter -> witnessUniformLower -> witnessEasyDensity -> noSmallDAG`.
-/
theorem noSmallDAG_of_canonical_smallDAG_witnessTransferQuarter_source_on_slices
    (F : GapSliceFamily)
    (hQuarterTr : canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)),
      ∀ n : Nat, ∀ β ε : Rat,
        ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
  exact
    noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices
      F
      (canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessTransferQuarter
        F hQuarterTr)

/--
Direct weak-route closure from upstream average-case/hardness source providers.

This theorem is intentionally thin: it compiles the upstream source object to
the canonical minimal distributional source provider and reuses the existing
counting-closed contradiction route.
-/
theorem noSmallDAG_of_smallDAGAverageCaseHardnessSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (hAvg : smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound) :
    ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε := by
  exact
    noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
      F SizeBound
      (smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource F SizeBound hAvg)

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
