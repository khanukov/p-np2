import Magnification.FinalResultMainline
import Magnification.CanonicalAsymptoticTrackData
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.DAGStableRestrictionProducer
import «pnp3».Tests.IsoStrongConclusionProbe
import «pnp3».Tests.GlobalHInDagContractProbe

/-!
# Promise-YES conclusion negation probe (canonical track)

Companion to `Tests/IsoStrongConclusionProbe.lean`.  That file proves the
canonical-track iso-strong conclusion negation
`isoStrong_conclusion_negative_for_canonical` per `globalWitness_to_hInDag W`.
By the existing route-level implications
`asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute` and
`asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
(`pnp3/Magnification/FinalResultMainline.lean:348` and `:400`), the
promise-YES certificate and promise-YES weak (eventual) routes are closed
at the same `hInDag = globalWitness_to_hInDag W` by pointwise
contrapositive.

`STATUS.md` records that closure as a meta-argument; this file packages it
as two named conclusion-level negation theorems with the same shape as
`isoStrong_conclusion_negative_for_canonical`, so a reviewer scanning the
audit chain for standalone Lean witnesses can read them off the API
directly:

* `promiseYesCertificate_conclusion_negative_for_canonical`,
* `promiseYesWeak_conclusion_negative_for_canonical`.

These are not new mathematics.  They are corollaries.  Their job is to make
the post-PR13 audit chain a self-contained sequence of Lean theorems
rather than a Lean theorem plus a prose paragraph.

The file is local to `pnp3/Tests/` and does not modify endpoints, specs,
or trust-root surfaces.
-/

namespace Pnp3
namespace Tests
namespace PromiseRouteConclusionProbe

open Magnification
open Models
open LowerBounds
open ComplexityInterfaces
open GlobalHInDagContractProbe

/-!
## Pointwise body predicates

`AsymptoticPromiseYesCertificateRoute hAsym` and
`AsymptoticPromiseYesWeakRouteEventually hAsym` are universally
quantified over the per-slice `InPpolyDAG` witness `hInDag`.  The
following two definitions name the body of each at a specific
`hInDag`, so that the conclusion-level negation theorems below have a
clean, standalone statement.
-/

/-- Body of `AsymptoticPromiseYesCertificateRoute hAsym` at a specific
`hInDag`.  Definitionally equal to the body inside the existing route
definition; introduced only so the negation theorem has a clean named
target. -/
def PromiseYesCertificateConclusion
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language
            ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))) :
    Prop :=
  ∃ β0 : Rat, 0 < β0 ∧
    ∃ nCert : Rat → Nat,
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max hAsym.N0 (nCert β) →
        ∀ W : SmallDAGWitnessOnSlice
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)
          (fun ε' s =>
            ppolyDAGSizeBoundOnSlicesEventually
              (eventualGapSliceFamily_of_asymptotic hAsym)
              hInDag n β ε' s)
          1,
          Nonempty (PromiseYesSubcubeCertificateAt W)

/-- Body of `AsymptoticPromiseYesWeakRouteEventually hAsym` at a specific
`hInDag`. -/
def PromiseYesWeakRouteConclusion
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language
            ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))) :
    Prop :=
  ∃ ε : Rat, 0 < ε ∧
    ∃ β0 : Rat, 0 < β0 ∧
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ n0 : Nat,
          (eventualGapSliceFamily_of_asymptotic hAsym).N0 ≤ n0 ∧
            ∀ n ≥ n0,
              SmallDAGImpliesPromiseYesSubcubeAtEventually
                (eventualGapSliceFamily_of_asymptotic hAsym)
                (ppolyDAGSizeBoundOnSlicesEventually
                  (eventualGapSliceFamily_of_asymptotic hAsym) hInDag)
                n β ε

/-!
## Pointwise route-implication helpers

These are the per-`hInDag` versions of
`asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
and `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
Their proof bodies are the same as the corresponding existing
implications minus the leading `intro hInDag`.  We keep them here as
local helpers; the existing implications in
`FinalResultMainline.lean` are untouched.
-/

/-- Pointwise version of
`asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`. -/
theorem promiseYesCertificateConclusion_of_promiseYesWeakRouteConclusion
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language
            ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)))
    (hWeak : PromiseYesWeakRouteConclusion hAsym hInDag) :
    PromiseYesCertificateConclusion hAsym hInDag := by
  let F : GapSliceFamilyEventually := eventualGapSliceFamily_of_asymptotic hAsym
  rcases hWeak with ⟨ε, hε, β0, hβ0, hEventuallyYes⟩
  let nCert : Rat → Nat := fun β =>
    if hβ : 0 < β ∧ β < β0 then
      Classical.choose (hEventuallyYes β hβ.1 hβ.2)
    else
      F.N0
  refine ⟨β0, hβ0, nCert, ?_⟩
  intro n β hβPos hβLt hn W
  have hβ : 0 < β ∧ β < β0 := ⟨hβPos, hβLt⟩
  have hChoice :
      F.N0 ≤ Classical.choose (hEventuallyYes β hβPos hβLt) ∧
        ∀ m ≥ Classical.choose (hEventuallyYes β hβPos hβLt),
          SmallDAGImpliesPromiseYesSubcubeAtEventually
            F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) m β ε :=
    Classical.choose_spec (hEventuallyYes β hβPos hβLt)
  have hN0Cert : F.N0 ≤ nCert β := by
    simpa [nCert, hβ] using hChoice.1
  have hnCert : nCert β ≤ n := by
    have hmaxEq : max hAsym.N0 (nCert β) = nCert β := by
      apply Nat.max_eq_right
      simpa [F, eventualGapSliceFamily_of_asymptotic] using hN0Cert
    simpa [hmaxEq] using hn
  have hn0 : F.N0 ≤ n := by
    exact le_trans hN0Cert hnCert
  have hYesAtN :
      SmallDAGImpliesPromiseYesSubcubeAtEventually
        F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε := by
    have hLarge :
        ∀ m ≥ nCert β,
          SmallDAGImpliesPromiseYesSubcubeAtEventually
            F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) m β ε := by
      simpa [nCert, hβ] using hChoice.2
    exact hLarge n hnCert
  exact
    ⟨promiseYesSubcubeCertificateAt_of_eventualPromiseYesWeakRoute
      (hn0 := hn0) W hYesAtN⟩

/-- Pointwise version of
`asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`. -/
theorem isoStrongFamilyEventually_of_promiseYesCertificateConclusion
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language
            ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)))
    (hCert : PromiseYesCertificateConclusion hAsym hInDag) :
    IsoStrongFamilyEventually
      (eventualGapSliceFamily_of_asymptotic hAsym) hInDag := by
  rcases hCert with ⟨β0, hβ0, nCert, hCert⟩
  let F : GapSliceFamilyEventually := eventualGapSliceFamily_of_asymptotic hAsym
  let κ : Nat → Rat → Nat :=
    fun n β =>
      GapSliceFamilyEventually.tableLen F n β -
        requiredComplementBudget (F.paramsOf n β)
  refine ⟨β0, hβ0, κ, nCert, ?_, ?_⟩
  · intro n β hβPos hβLt hn C hSize hCorrect
    let p : GapPartialMCSPParams := F.paramsOf n β
    let W : SmallDAGWitnessOnSlice p
        (fun ε' s => ppolyDAGSizeBoundOnSlicesEventually F hInDag n β ε' s) 1 := {
      C := C
      hSize := hSize
      hCorrect := hCorrect
    }
    let cert : PromiseYesSubcubeCertificateAt W :=
      Classical.choice (hCert n β hβPos hβLt hn W)
    have hBudget :
        requiredComplementBudget p ≤ Models.Partial.tableLen p.n - cert.S.card := by
      exact Nat.find_min' (exists_countingSlack_budget p) cert.hSlack
    have hCardTable :
        cert.S.card ≤ Models.Partial.tableLen p.n := by
      simpa using Finset.card_le_univ cert.S
    have hCardLe :
        cert.S.card ≤ κ n β := by
      change cert.S.card ≤ Models.Partial.tableLen p.n - requiredComplementBudget p
      omega
    refine ⟨cert.yYes, ?_, cert.hValidYes, cert.S, hCardLe, ?_⟩
    · simpa [gapSliceOfParams, GapPartialMCSPPromise] using cert.hYes
    · intro z hzValid hzAgree
      have hzPromise :
          z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No :=
        mem_yes_or_no_gapSliceOfParams (p := p) z
      have hzEval : DagCircuit.eval C z = true := cert.hAccept z
        (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hzPromise)
        hzValid hzAgree
      cases hzPromise with
      | inl hzYes =>
          exact hzYes
      | inr hzNo =>
          have hzFalse : DagCircuit.eval C z = false := hCorrect.2 z hzNo
          have hContra : false = true := hzFalse.symm.trans hzEval
          exact False.elim (Bool.false_ne_true hContra)
  · intro n β hβPos hβLt hn
    let p : GapPartialMCSPParams := F.paramsOf n β
    have hcoh := eventual_coherence_at F n β (le_trans (Nat.le_max_left _ _) hn)
    rcases hcoh with ⟨_, _, hMof⟩
    have hReqLeHalf :
        requiredComplementBudget p ≤ Models.Partial.tableLen p.n / 2 := by
      exact Nat.find_min' (exists_countingSlack_budget p) p.circuit_bound_ok
    have hReqLeTable :
        requiredComplementBudget p ≤ GapSliceFamilyEventually.tableLen F n β := by
      simpa [GapSliceFamilyEventually.tableLen, p] using
        le_trans hReqLeHalf (Nat.div_le_self (Models.Partial.tableLen p.n) 2)
    have hExpEq :
        GapSliceFamilyEventually.tableLen F n β - κ n β =
          requiredComplementBudget p := by
      simpa [κ, GapSliceFamilyEventually.tableLen, p] using
        (Nat.sub_sub_self hReqLeTable)
    calc
      F.Mof n (F.Tof n β)
          = Models.circuitCountBound p.n (p.sNO - 1) := by
              simpa [p] using hMof
      _ < 2 ^ requiredComplementBudget p :=
        countingSlack_at_requiredComplementBudget p
      _ = 2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β) := by
            simp [hExpEq]

/-!
## Companion negation theorems

These are the canonical-track conclusion negations packaged in the
same `∀ W, ¬ ...` shape as `isoStrong_conclusion_negative_for_canonical`.
Each is a direct corollary of `isoStrong_conclusion_negative_for_canonical`
composed with the pointwise implications above.
-/

/-- Canonical-track promise-YES certificate conclusion negation.

Companion to `IsoStrongConclusionProbe.isoStrong_conclusion_negative_for_canonical`
covering the certificate route at the same per-`W` `hInDag`. -/
theorem promiseYesCertificate_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ PromiseYesCertificateConclusion canonicalAsymptoticHAsym
          (globalWitness_to_hInDag W) := by
  intro W hCert
  exact IsoStrongConclusionProbe.isoStrong_conclusion_negative_for_canonical W
    (isoStrongFamilyEventually_of_promiseYesCertificateConclusion
      canonicalAsymptoticHAsym (globalWitness_to_hInDag W) hCert)

/-- Canonical-track promise-YES weak (eventual) conclusion negation.

Companion to `IsoStrongConclusionProbe.isoStrong_conclusion_negative_for_canonical`
covering the eventual weak route at the same per-`W` `hInDag`. -/
theorem promiseYesWeak_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ PromiseYesWeakRouteConclusion canonicalAsymptoticHAsym
          (globalWitness_to_hInDag W) := by
  intro W hWeak
  exact promiseYesCertificate_conclusion_negative_for_canonical W
    (promiseYesCertificateConclusion_of_promiseYesWeakRouteConclusion
      canonicalAsymptoticHAsym (globalWitness_to_hInDag W) hWeak)

end PromiseRouteConclusionProbe
end Tests
end Pnp3
