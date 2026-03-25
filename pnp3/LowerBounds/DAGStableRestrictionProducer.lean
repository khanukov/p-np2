import LowerBounds.SingletonDensityContradiction

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

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

end LowerBounds
end Pnp3
