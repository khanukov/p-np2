import Magnification.Bridge_to_Magnification_Partial
import Magnification.AsymptoticFormulaCollapse
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Magnification.PipelineStatements_Partial
import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.RouteBSourceClosure
import LowerBounds.AsymptoticDAGBarrier
import LowerBounds.SingletonDensityContradiction
import Models.Model_PartialMCSP
import Complexity.Interfaces
import Complexity.PpolyFormula_from_PpolyDAG_FixedSlice
import Complexity.PsubsetPpolyDAG_Internal
import Complexity.Simulation.Circuit_Compiler

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-!
# Final-result mainline layer

This file is not the public unconditional frontier.  The active public boundary
is `Magnification.UnconditionalResearchGap`, where `P_ne_NP_final` takes only a
`ResearchGapWitness`.

The declarations below are retained as conditional integration surfaces and
mainline DAG wrappers.  Refuted support-bounds/provider-backed compatibility
routes live in `Magnification.FinalResultAuditRoutes`.  New work should prefer
anti-checker-only DAG routes plus an explicit, non-vacuous DAG-separation
witness.
-/

/--
Asymptotic entry hypothesis for the partial formula track:
explicitly provides parameters and lower-bound hypotheses at all
sizes above a threshold `N0`.
-/
structure AsymptoticFormulaTrackHypothesis where
  spec : GapPartialMCSPAsymptoticSpec
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  sliceEq :
    ∀ n (hn : N0 ≤ n),
      ∀ x : Core.BitVec (Models.partialInputLen (pAt n hn)),
        gapPartialMCSP_AsymptoticLanguage spec
            (Models.partialInputLen (pAt n hn)) x =
          gapPartialMCSP_Language (pAt n hn)
            (Models.partialInputLen (pAt n hn)) x

/--
Asymptotic NP bridge package:
strict NP witness for the global asymptotic language.
-/
structure AsymptoticNPPullback (hAsym : AsymptoticFormulaTrackHypothesis) : Type where
  strictAsymptotic :
    ComplexityInterfaces.NP_strict
      (gapPartialMCSP_AsymptoticLanguage hAsym.spec)

/--
Theorem-level constructive source package for the asymptotic track.

Unlike provider classes, this structure keeps all source obligations explicit as
ordinary fields.  It is intended for the "real internalization" step where
`hAsym`/`hNPbridge` are derived from concrete mathematical payload, not injected
through endpoint-level class wiring.
-/
structure AsymptoticFormulaTrackData where
  spec : GapPartialMCSPAsymptoticSpec
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  sliceEq :
    ∀ n (hn : N0 ≤ n),
      ∀ x : Core.BitVec (Models.partialInputLen (pAt n hn)),
        gapPartialMCSP_AsymptoticLanguage spec
            (Models.partialInputLen (pAt n hn)) x =
          gapPartialMCSP_Language (pAt n hn)
            (Models.partialInputLen (pAt n hn)) x
  asymptoticNP_TM : Models.gapPartialMCSP_Asymptotic_in_NP_TM spec

/--
Build `AsymptoticFormulaTrackHypothesis` from constructive asymptotic source
data.
-/
def asymptoticFormulaTrackHypothesis_of_data
    (D : AsymptoticFormulaTrackData) : AsymptoticFormulaTrackHypothesis where
  spec := D.spec
  N0 := D.N0
  pAt := D.pAt
  pAt_n := D.pAt_n
  sliceEq := D.sliceEq

/--
Build the NP pullback package from constructive asymptotic source data.

The strict NP witness is obtained canonically from the asymptotic TM witness
embedded in `AsymptoticFormulaTrackData`.
-/
def asymptoticNPPullback_of_data
    (D : AsymptoticFormulaTrackData) :
    AsymptoticNPPullback (asymptoticFormulaTrackHypothesis_of_data D) where
  strictAsymptotic :=
    Models.gapPartialMCSP_Asymptotic_in_NP_of_TM D.spec D.asymptoticNP_TM

/--
Explicit assumptions package for the switching/shrinkage side:
it carries the strengthened A9 multi-switching contract (including semantic
linkage), from which support-bounds and the structured provider are derived
internally.
-/
structure SwitchingAssumptions : Type where
  multiswitching : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract

/-- **Step 4 pipeline-aware** — the replacement for `SwitchingAssumptions`.

The old `SwitchingAssumptions` packages only the inconsistent
`FormulaSupportBoundsFromMultiSwitchingContract` (audit Probe 4), so
any `MagnificationAssumptions` consumer inherits ex-falso.

This pipeline version takes the two *separately-consistent* pieces:
- `semProv`: AC0 provenance per PpolyFormula witness.
- `boundsP`: support bounds GIVEN provenance (non-vacuous because it
  takes provenance as input).

Neither is known to be inconsistent in the current formalization. -/
structure SwitchingAssumptions_fromPipeline : Type where
  semProv : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider
  boundsP : FormulaSupportBoundsPartial_fromPipeline

/--
Explicit assumptions package for the anti-checker side of the final route.
-/
structure AntiCheckerAssumptions : Type where
  asymptotic : AsymptoticFormulaTrackHypothesis
  npBridge : AsymptoticNPPullback asymptotic

/--
Top-level explicit assumptions package for the magnification final statements.

This keeps imported assumptions grouped and auditable at theorem boundaries.

Legacy/audit status: the `switching` field contains
`FormulaSupportBoundsFromMultiSwitchingContract`, a refuted support-bounds
surface.  The active public final theorem intentionally does not consume this
package; see `UnconditionalResearchGap.ResearchGapWitness`.
-/
structure MagnificationAssumptions : Type where
  switching : SwitchingAssumptions
  antiChecker : AntiCheckerAssumptions

/-- **Step 4 pipeline-aware** — non-ex-falso replacement for
`MagnificationAssumptions`.  The `switching` field uses
`SwitchingAssumptions_fromPipeline`, which bundles the two separately-
consistent AC0-multiswitching ingredients rather than the inconsistent
single-contract package. -/
structure MagnificationAssumptions_fromPipeline : Type where
  switching : SwitchingAssumptions_fromPipeline
  antiChecker : AntiCheckerAssumptions

/--
Eventual slice family induced by the asymptotic anti-checker track.

The asymptotic hypothesis is indexed only by `n`, while the eventual DAG route
is parametrized by `(n, β)`.  This adapter keeps the same asymptotic slice on
all `β` and uses `max n N0` to make the family total below the asymptotic
threshold without introducing new mathematical obligations there.
-/
def eventualGapSliceFamily_of_asymptotic
    (hAsym : AsymptoticFormulaTrackHypothesis) :
    GapSliceFamilyEventually where
  N0 := hAsym.N0
  paramsOf n _β := hAsym.pAt (max n hAsym.N0) (Nat.le_max_right _ _)
  Tof n β := (hAsym.pAt (max n hAsym.N0) (Nat.le_max_right _ _)).sNO - 1
  Mof n T := Models.circuitCountBound n T
  hIndex n hn β := by
    simpa [Nat.max_eq_left hn] using hAsym.pAt_n n hn
  hT n hn β := by
    simp [Nat.max_eq_left hn]
  hM n hn T := by
    rfl

/--
Canonical-length bridge from the asymptotic global language to the eventual DAG
carrier induced by `eventualGapSliceFamily_of_asymptotic`.
-/
noncomputable def eventualCanonicalBridge_of_asymptotic
    (hAsym : AsymptoticFormulaTrackHypothesis) :
    AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths
      (eventualGapSliceFamily_of_asymptotic hAsym) where
  L := gapPartialMCSP_AsymptoticLanguage hAsym.spec
  sliceEq n β x := by
    exact hAsym.sliceEq (max n hAsym.N0) (Nat.le_max_right _ _) x

/--
The asymptotic NP witness already packaged in `AsymptoticNPPullback` is exactly
the NP witness needed by the canonical-length eventual DAG bridge.
-/
theorem eventualCanonicalBridge_in_NP_of_asymptotic
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPbridge : AsymptoticNPPullback hAsym) :
    ComplexityInterfaces.NP
      (eventualCanonicalBridge_of_asymptotic hAsym).L :=
  hNPbridge.strictAsymptotic

/--
Strong eventual source contract on top of the asymptotic anti-checker track.

This is the direct mainline theorem target for the non-vacuous eventual DAG
route: once every hypothetical small-DAG slice family yields an
`IsoStrongFamilyEventually` witness, the rest of the canonical-length closure to
`NP_not_subset_PpolyDAG` is generic.
-/
def AsymptoticIsoStrongRoute
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ hInDag :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)),
    IsoStrongFamilyEventually
      (eventualGapSliceFamily_of_asymptotic hAsym)
      hInDag

/--
Witness-indexed eventual promise-YES certificate route on the asymptotic
anti-checker track.

Compared with `AsymptoticIsoStrongRoute`, this route asks source work for the
already-familiar object `PromiseYesSubcubeCertificateAt` on each sufficiently
large canonical slice.  The uniform cardinality budget `κ` is then recovered
mechanically from `requiredComplementBudget`.
-/
def AsymptoticPromiseYesCertificateRoute
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ hInDag :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)),
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

/--
Canonical eventual weak-route source theorem shape on the asymptotic
anti-checker track.

This is the theorem-level payload already consumed directly by the non-vacuous
eventual barrier endpoint at canonical lengths.
-/
def AsymptoticPromiseYesWeakRouteEventually
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ hInDag :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)),
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

/--
Build a witness-indexed promise-YES certificate from the eventual weak-route
payload at one concrete canonical slice.

The source theorem may use any `ε`; the target witness here is fixed at `ε = 1`
because `ppolyDAGSizeBoundOnSlicesEventually` ignores the epsilon parameter.
-/
noncomputable def promiseYesSubcubeCertificateAt_of_eventualPromiseYesWeakRoute
    {F : GapSliceFamilyEventually}
    {hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))}
    {n : Nat}
    {β ε : Rat}
    (hn0 : F.N0 ≤ n)
    (W : SmallDAGWitnessOnSlice
      (F.paramsOf n β)
      (fun ε' s => ppolyDAGSizeBoundOnSlicesEventually F hInDag n β ε' s)
      1)
    (hYes :
      SmallDAGImpliesPromiseYesSubcubeAtEventually
        F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε) :
    PromiseYesSubcubeCertificateAt W := by
  classical
  let hExists :=
    hYes W.C
      (by simpa [ppolyDAGSizeBoundOnSlicesEventually] using W.hSize)
      W.hCorrect
  let yYes := Classical.choose hExists
  have hySpec := Classical.choose_spec hExists
  let S := Classical.choose hySpec.2.2
  have hSSpec := Classical.choose_spec hySpec.2.2
  have hcoh := eventual_coherence_at F n β hn0
  rcases hcoh with ⟨hpn, hTof, hMof⟩
  refine
    { yYes := yYes
      hYes := by
        simpa [gapSliceOfParams, GapPartialMCSPPromise] using hySpec.1
      hValidYes := hySpec.2.1
      S := S
      hSlack := by
        calc
          Models.circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)
              = F.Mof n (F.Tof n β) := by simpa using hMof.symm
          _ < 2 ^ (GapSliceFamilyEventually.tableLen F n β - S.card) := hSSpec.1
          _ = 2 ^ (Models.Partial.tableLen (F.paramsOf n β).n - S.card) := by
                simp [GapSliceFamilyEventually.tableLen, hpn]
      hAccept := by
        intro z hzPromise hzValid hAgree
        exact hSSpec.2 z
          ((by
            cases hzPromise with
            | inl hzYes =>
                exact Or.inl (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hzYes)
            | inr hzNo =>
                exact Or.inr (by simpa [gapSliceOfParams, GapPartialMCSPPromise] using hzNo)))
          hzValid
          hAgree }

/--
Convert the theorem-minimal eventual weak-route payload to the stronger
witness-indexed certificate route.
-/
theorem asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hRoute : AsymptoticPromiseYesWeakRouteEventually hAsym) :
    AsymptoticPromiseYesCertificateRoute hAsym := by
  intro hInDag
  let F : GapSliceFamilyEventually := eventualGapSliceFamily_of_asymptotic hAsym
  rcases hRoute hInDag with ⟨ε, hε, β0, hβ0, hEventuallyYes⟩
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

/--
Recover the stronger eventual isolation-envelope route from witness-indexed
promise-YES certificates.

This is a pure closure step.  The only arithmetic ingredient is that every
certificate already carries counting slack on its own semantic set `S`, so the
minimal complement threshold `requiredComplementBudget` yields a uniform
cardinality bound `κ`.
-/
theorem asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hRoute : AsymptoticPromiseYesCertificateRoute hAsym) :
    AsymptoticIsoStrongRoute hAsym := by
  intro hInDag
  rcases hRoute hInDag with ⟨β0, hβ0, nCert, hCert⟩
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

/--
Family-specific entrypoint for the singleton `β`-route decision layer.

This theorem does not prove the comparison inequality on its own. It packages
the exact arithmetic hypothesis currently missing from the generic asymptotic
API and feeds it into the current singleton-source decision theorem on the
chosen fixed slice `pAt n hn`.
-/
theorem empty_witness_admissible_for_asymptotic_slice_of_nat_cmp
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n)
  (hFormula : ComplexityInterfaces.PpolyFormula
    (gapPartialMCSP_Language (hAsym.pAt n hn)))
  (hCmp :
    Models.circuitCountBound (hAsym.pAt n hn).n (hAsym.pAt n hn).sYES *
      3 ^ Models.Partial.tableLen (hAsym.pAt n hn).n *
      (Models.partialInputLen (hAsym.pAt n hn) + 2)
    ≤
      4 ^ Models.Partial.tableLen (hAsym.pAt n hn).n) :
  AC0LocalityBridge.CurrentSingletonRouteWitnessProp hFormula := by
  exact
    AC0LocalityBridge.empty_witness_admissible_for_current_singleton_route_of_nat_cmp
      (p := hAsym.pAt n hn)
      hFormula
      hCmp

/--
Asymptotic formula collapse, routed through a fixed-slice bridge.

This theorem is the active bridge-shaped entrypoint in `codex-refactoring`:
the fixed-slice collapse side is internalized from provider + lower-bound data,
while the asymptotic-to-slice conversion remains an explicit bridge parameter.
-/
theorem asymptotic_formula_collapse
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False := by
  let p : GapPartialMCSPParams := hAsym.pAt n hn
  have hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_semantic
      (p := p) (δ := (1 : Rat)) (hδ := by norm_num)
  have hFixedCollapse :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False :=
    fixed_formula_collapse_of_provider (hProvider := hProvider) (p := p) (δ := (1 : Rat)) hHyp
  exact
    asymptotic_formula_collapse_of_slice_agreement
      (spec := hAsym.spec)
      (p := p)
      hFixedCollapse
      (hAsym.sliceEq n hn)

/-- **Step 3b** — pipeline-aware asymptotic collapse.  Takes the
pipeline structured provider + semantic-multi-switching provider in
place of the ex-falso old structured provider. -/
theorem asymptotic_formula_collapse_fromPipeline
  (hProviderP : StructuredLocalityProviderPartial_fromPipeline)
  (hSemProv : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False := by
  let p : GapPartialMCSPParams := hAsym.pAt n hn
  have hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_semantic
      (p := p) (δ := (1 : Rat)) (hδ := by norm_num)
  have hFixedCollapse :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False :=
    fixed_formula_collapse_of_provider_fromPipeline
      (hProviderP := hProviderP) (hSemProv := hSemProv)
      (p := p) (δ := (1 : Rat)) hHyp
  exact
    asymptotic_formula_collapse_of_slice_agreement
      (spec := hAsym.spec)
      (p := p)
      hFixedCollapse
      (hAsym.sliceEq n hn)

/--
Primary final statement (asymptotic entry): from the structured provider and
asymptotic formula-track hypothesis we derive `NP ⊄ PpolyFormula`.

Scope note:
this theorem is a formula-separation endpoint of the AC0-target magnification
route; it is not a standalone global non-uniform separation claim.
-/
theorem NP_not_subset_PpolyFormula_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hCollapse :
      ComplexityInterfaces.PpolyFormula
        (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False :=
    asymptotic_formula_collapse hProvider hAsym n hn
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse
      (spec := hAsym.spec)
      (hNPstrict := hNPbridge.strictAsymptotic)
      hCollapse

/-- **Step 3c — pipeline-aware final formula separation (with provider)**.

Parallel to `NP_not_subset_PpolyFormula_final_with_provider`, but takes:
- `hProviderP : StructuredLocalityProviderPartial_fromPipeline` — non-ex-falso.
- `hSemProv : FormulaSemanticMultiSwitchingProvider` — supplies AC0 provenance per hFormula.

**Soundness note**: this theorem is NOT ex-falso via the audit's
truth-table probe, because:
- `hProviderP` takes AC0 provenance as input (Probe 3 no longer applies).
- `hSemProv` asserts existence of AC0 family per hFormula — potentially
  inconsistent IF the project has MCSP-not-AC0 as a theorem, but such
  a lower bound is not currently in-project.

The pipeline migration thus SURFACES the AC0-multiswitching assumption
explicitly in the final theorem's signature rather than hiding it in
an ex-falso predicate. -/
theorem NP_not_subset_PpolyFormula_final_with_provider_fromPipeline
  (hProviderP : StructuredLocalityProviderPartial_fromPipeline)
  (hSemProv : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hCollapse :
      ComplexityInterfaces.PpolyFormula
        (gapPartialMCSP_AsymptoticLanguage hAsym.spec) → False :=
    asymptotic_formula_collapse_fromPipeline hProviderP hSemProv hAsym n hn
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse
      (spec := hAsym.spec)
      (hNPstrict := hNPbridge.strictAsymptotic)
      hCollapse

/--
Provider-free wrapper at the formula endpoint boundary:
derive the structured locality provider internally from support-based bounds.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

The hypothesis `hBounds : FormulaSupportRestrictionBoundsPartial` has
been proven INCONSISTENT by the April 2026 falsifiability audit —
see `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` Probe 3
(`false_of_FormulaSupportRestrictionBoundsPartial`) for the formal
Lean proof.  Any call site using this theorem inherits the ex-falso
nature: the conclusion `NP_not_subset_PpolyFormula` is derivable
directly via `False.elim` (see Probe 6).

For legitimate use, migrate to `NP_not_subset_PpolyFormula_final_with_provider`
and provide the `StructuredLocalityProviderPartial` through a
non-ex-falso route (not yet available in this project — all current
provider constructors ultimately route through `hBounds`).

The migration plan is documented in `pnp3/Docs/PhaseI_Verifier_Design.md`
session 55 / 57 entries.
-/
theorem NP_not_subset_PpolyFormula_final_with_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hBounds)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Provider-free wrapper at the formula endpoint boundary:
derive support-bounds and the structured locality provider internally from the
strengthened A9 multi-switching contract.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

Same caveat as `NP_not_subset_PpolyFormula_final_with_supportBounds`:
the hypothesis `hMS : FormulaSupportBoundsFromMultiSwitchingContract`
is inconsistent (Probe 4 of the audit,
`false_of_FormulaSupportBoundsFromMultiSwitchingContract`), because it
universally quantifies over every `PpolyFormula` witness and packages
the same false support-bounds claim.  Downstream conclusions are
ex-falso.

Migrate to `NP_not_subset_PpolyFormula_final_with_provider` with a
non-ex-falso provider source (TBD — see session 55/57 migration plan).
-/
theorem NP_not_subset_PpolyFormula_final_with_multiswitching
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_supportBounds
      (hBounds := formula_support_bounds_from_multiswitching hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Primary asymptotic final formula-separation statement.

This is the active audit-facing entrypoint: all external assumptions are passed
explicitly via `MagnificationAssumptions`.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

`MagnificationAssumptions` contains the inconsistent hypothesis
`switching.multiswitching : FormulaSupportBoundsFromMultiSwitchingContract`,
so this theorem's conclusion is ex-falso (Probe 5/6 of the audit,
`false_of_MagnificationAssumptions` +
`NP_not_subset_PpolyFormula_final_via_ex_falso`).

**This theorem's current statement does NOT represent genuine progress
toward unconditional `NP ⊄ P/poly`.**  To make this claim sound, the
`MagnificationAssumptions` structure must be refactored to carry a
non-inconsistent locality-provider source — see session 55/57
migration plan in `pnp3/Docs/PhaseI_Verifier_Design.md`.

Until the migration completes, callers should prefer the underlying
`NP_not_subset_PpolyFormula_final_with_provider` directly, making
the ex-falso-vs-legitimate distinction explicit at the call site.
-/
theorem NP_not_subset_PpolyFormula_final
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_multiswitching
      (hMS := hMag.switching.multiswitching)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/-- **Step 4 pipeline-aware top-level theorem**.  Takes the
pipeline-aware `MagnificationAssumptions_fromPipeline` package and
routes through Step 3c's `_with_provider_fromPipeline` chain.

**Soundness vs. ex-falso `_final`**: the old `_final` takes
`MagnificationAssumptions` which contains an ex-falso
`FormulaSupportBoundsFromMultiSwitchingContract` field (audit Probes
4-6).  This pipeline version takes the two separately-consistent
ingredients (semProv + boundsP) without the inconsistent packaging.

This is the **recommended** entrypoint for new downstream callers:
the conclusion `NP_not_subset_PpolyFormula` is genuinely derived, not
ex-falso. -/
theorem NP_not_subset_PpolyFormula_final_fromPipeline
  (hMagP : MagnificationAssumptions_fromPipeline)
  (n : Nat) (hn : hMagP.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula :=
  NP_not_subset_PpolyFormula_final_with_provider_fromPipeline
    (hProviderP :=
      structuredLocalityProviderPartial_fromPipeline_of_supportBoundsFromPipeline
        hMagP.switching.boundsP)
    (hSemProv := hMagP.switching.semProv)
    (hAsym := hMagP.antiChecker.asymptotic)
    (hNPbridge := hMagP.antiChecker.npBridge)
    (n := n)
    (hn := hn)

/--
Primary final statement on the nontrivial non-uniform class `PpolyReal`.

In the current strict interface this endpoint is a thin corollary of the
formula-separation route, because `PpolyReal` and `PpolyFormula` share the same
concrete witness model.
-/
theorem NP_not_subset_PpolyReal_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    ComplexityInterfaces.NP_not_subset_PpolyReal_of_PpolyFormula
      (NP_not_subset_PpolyFormula_final_with_provider
        (hProvider := hProvider)
        (hAsym := hAsym)
        (hNPbridge := hNPbridge)
        (n := n)
        (hn := hn))

/-- **Step 4 pipeline-aware PpolyReal with-provider**.  Thin corollary
of the PpolyFormula pipeline theorem via the
`NP_not_subset_PpolyReal_of_PpolyFormula` bridge. -/
theorem NP_not_subset_PpolyReal_final_with_provider_fromPipeline
  (hProviderP : StructuredLocalityProviderPartial_fromPipeline)
  (hSemProv : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal :=
  ComplexityInterfaces.NP_not_subset_PpolyReal_of_PpolyFormula
    (NP_not_subset_PpolyFormula_final_with_provider_fromPipeline
      (hProviderP := hProviderP)
      (hSemProv := hSemProv)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn))

/--
Provider-free wrapper at the `PpolyReal` endpoint boundary:
derive the structured locality provider internally from support-based bounds.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

See the formula-side counterpart
`NP_not_subset_PpolyFormula_final_with_supportBounds`: the
`hBounds : FormulaSupportRestrictionBoundsPartial` hypothesis is
inconsistent (audit Probe 3).
-/
theorem NP_not_subset_PpolyReal_final_with_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hBounds)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Provider-free wrapper at the `PpolyReal` endpoint boundary:
derive support-bounds and the structured locality provider internally from the
strengthened A9 multi-switching contract.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

See the formula-side counterpart
`NP_not_subset_PpolyFormula_final_with_multiswitching`: the
`hMS : FormulaSupportBoundsFromMultiSwitchingContract` hypothesis is
inconsistent (audit Probe 4).
-/
theorem NP_not_subset_PpolyReal_final_with_multiswitching
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_supportBounds
      (hBounds := formula_support_bounds_from_multiswitching hMS)
      (hAsym := hAsym)
      (hNPbridge := hNPbridge)
      (n := n)
      (hn := hn)

/--
Primary asymptotic final `PpolyReal`-separation statement.

## ⚠ EX-FALSO UNDER CURRENT FORMALIZATION ⚠

See formula-side counterpart `NP_not_subset_PpolyFormula_final`: the
`hMag.switching.multiswitching` field is inconsistent (audit Probes 4–6).
The conclusion is ex-falso and does not represent genuine progress
toward unconditional `NP ⊄ P/poly_real`.
-/
theorem NP_not_subset_PpolyReal_final
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal := by
  exact
    NP_not_subset_PpolyReal_final_with_multiswitching
      (hMS := hMag.switching.multiswitching)
      (hAsym := hMag.antiChecker.asymptotic)
      (hNPbridge := hMag.antiChecker.npBridge)
      (n := n)
      (hn := hn)

/-- **Step 4 pipeline-aware PpolyReal final**.  Non-ex-falso replacement
for `NP_not_subset_PpolyReal_final`.  Takes the pipeline-aware
`MagnificationAssumptions_fromPipeline` package; conclusion is
genuinely derived, not ex-falso. -/
theorem NP_not_subset_PpolyReal_final_fromPipeline
  (hMagP : MagnificationAssumptions_fromPipeline)
  (n : Nat) (hn : hMagP.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyReal :=
  NP_not_subset_PpolyReal_final_with_provider_fromPipeline
    (hProviderP :=
      structuredLocalityProviderPartial_fromPipeline_of_supportBoundsFromPipeline
        hMagP.switching.boundsP)
    (hSemProv := hMagP.switching.semProv)
    (hAsym := hMagP.antiChecker.asymptotic)
    (hNPbridge := hMagP.antiChecker.npBridge)
    (n := n)
    (hn := hn)

/-- One-gate constant-false DAG used off the target asymptotic slice. -/
private def constFalseDag (n : Nat) : ComplexityInterfaces.DagCircuit n where
  gates := 1
  gate := fun _ => ComplexityInterfaces.DagGate.const false
  output := ComplexityInterfaces.DagWire.gate ⟨0, by simp⟩

@[simp] private theorem constFalseDag_size {n : Nat} :
    ComplexityInterfaces.DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.size]

@[simp] private theorem constFalseDag_eval {n : Nat}
    (x : ComplexityInterfaces.Bitstring n) :
    ComplexityInterfaces.DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, ComplexityInterfaces.DagCircuit.eval,
    ComplexityInterfaces.DagCircuit.eval.evalGateAt]

/-- Monotone padding used to restrict an asymptotic DAG witness to one slice. -/
private theorem dag_poly_bound_lift (n c : Nat) :
    n ^ c + c ≤ n ^ (c + 2) + (c + 2) := by
  by_cases hn : n = 0
  · subst hn
    cases c <;> simp
  · have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpow : n ^ c ≤ n ^ (c + 2) := by
      simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right c 2)
    have hc : c ≤ c + 2 := by omega
    exact Nat.add_le_add hpow hc

/--
Constructive asymptotic-to-fixed bridge from pointwise slice agreement at the
target length `partialInputLen p`.
-/
private theorem ppolyDAG_fixed_of_asymptotic_slice
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hSliceEq :
      ∀ x : Core.BitVec (partialInputLen p),
        gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
          gapPartialMCSP_Language p (partialInputLen p) x) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_AsymptoticLanguage spec) →
      ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hAsym
  rcases hAsym with ⟨w, _⟩
  rcases w.polyBound_poly with ⟨c, hc⟩
  refine ⟨{
    polyBound := fun n => n ^ (c + 2) + (c + 2)
    polyBound_poly := ?_
    family := fun m =>
      if hm : m = partialInputLen p then
        w.family m
      else
        constFalseDag m
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · refine ⟨c + 2, ?_⟩
    intro n
    rfl
  · intro m
    by_cases hm : m = partialInputLen p
    · have hTarget : w.polyBound m ≤ m ^ (c + 2) + (c + 2) := by
        exact le_trans (hc m) (dag_poly_bound_lift m c)
      exact by
        simpa [hm] using le_trans (w.family_size_le m) hTarget
    · have hConst :
        ComplexityInterfaces.DagCircuit.size (constFalseDag m) ≤
          m ^ (c + 2) + (c + 2) := by
        rw [constFalseDag_size]
        have hTwo : 2 ≤ c + 2 := by omega
        exact le_trans hTwo (Nat.le_add_left (c + 2) (m ^ (c + 2)))
      simpa [hm] using hConst
  · intro m x
    by_cases hm : m = partialInputLen p
    · cases hm
      have hAsymCorrect :
          ComplexityInterfaces.DagCircuit.eval
              (w.family (partialInputLen p)) x =
            gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x :=
        w.correct (partialInputLen p) x
      have hEq :
          gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
            gapPartialMCSP_Language p (partialInputLen p) x :=
        hSliceEq x
      simpa using Eq.trans hAsymCorrect hEq
    · have hFixedFalse : gapPartialMCSP_Language p m x = false := by
        simp [gapPartialMCSP_Language, hm]
      simp [hm, hFixedFalse]

/--
Compatible DAG-track final wrapper.

This route targets the canonical non-uniform class (`PpolyDAG`) and therefore
uses explicit assumptions:
1) `NP ⊄ PpolyDAG`
2) linear-route internal `P ⊆ PpolyDAG` closure contracts.
-/
theorem P_ne_NP_final_with_provider
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG)
  (hPpolyContracts :
    Complexity.Simulation.PsubsetPpolyCompiledRuntimeLinearOutputContracts) :
  ComplexityInterfaces.P_ne_NP := by
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts
      hPpolyContracts
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Active conditional final `P ≠ NP` wrapper.

This is the honest DAG-track endpoint:
it uses only DAG-side separation plus the internalized inclusion theorem.

AC0/magnification assumptions live on a separate route
(`NP_not_subset_PpolyFormula_final*` / `NP_not_subset_PpolyReal_final*`)
until an explicit bridge to DAG separation is formalized.
-/
theorem P_ne_NP_final_dag_only
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
  have hPDag : ComplexityInterfaces.P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_internal
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
      hNPDag
      hPDag

/--
Canonical eventual DAG route from the asymptotic anti-checker package.

This theorem is the mainline integration point for the non-vacuous eventual
carrier: all bridge and NP wiring are derived from `hAsym`, and the only
remaining mathematical debt is the family-specific `AsymptoticIsoStrongRoute`.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (hIso : AsymptoticIsoStrongRoute hAsym) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  let F : GapSliceFamilyEventually := eventualGapSliceFamily_of_asymptotic hAsym
  let bridge :
      AsymptoticDAGLanguageBridgeEventuallyAtCanonicalLengths F :=
    eventualCanonicalBridge_of_asymptotic hAsym
  have hNP : ComplexityInterfaces.NP bridge.L :=
    eventualCanonicalBridge_in_NP_of_asymptotic hAsym hNPbridge
  have hIsoFamily :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ β0 : Rat, 0 < β0 ∧
          ∃ κ : Nat → Rat → Nat,
            ∃ nIso : Rat → Nat,
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                ∀ C : DagCircuit (GapSliceFamilyEventually.encodedLen F n β),
                  ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (DagCircuit.size C) →
                  CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
                    ∃ yYes : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                      yYes ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
                      ValidEncoding (F.paramsOf n β) yYes ∧
                      ∃ D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)),
                        D.card ≤ κ n β ∧
                        ∀ z : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
                          (z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∨
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).No) →
                          ValidEncoding (F.paramsOf n β) z →
                          AgreeOnValues (p := F.paramsOf n β) D yYes z →
                            z ∈ (gapSliceOfParams (F.paramsOf n β)).Yes) ∧
              (∀ n : Nat, ∀ β : Rat,
                0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
                  F.Mof n (F.Tof n β) <
                    2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) := by
    intro hInDag
    exact isoFamily_withPromise_of_isoStrongFamilyEventually F hInDag (hIso hInDag)
  exact
    NP_not_subset_PpolyDAG_of_eventuallyIsolationEnvelopeWeakRouteEventually_atCanonicalLengths
      F bridge hNP hIsoFamily

/--
Anti-checker-only wrapper for the canonical eventual DAG route.

This avoids the legacy `MagnificationAssumptions` package and therefore does
not require the refuted formula-side support-bounds surface.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (hIso : AsymptoticIsoStrongRoute anti.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute
      (hAsym := anti.asymptotic)
      (hNPbridge := anti.npBridge)
      hIso

/--
Legacy package-shaped wrapper for the canonical eventual DAG route.

Prefer
`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`.
This wrapper is retained only for callers that still pass
`MagnificationAssumptions`.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withMagnification
  (hMag : MagnificationAssumptions)
  (hIso : AsymptoticIsoStrongRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
      (anti := hMag.antiChecker) hIso

/--
Companion `P ≠ NP` endpoint from the anti-checker-only canonical eventual DAG
route.
-/
theorem P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (hIso : AsymptoticIsoStrongRoute anti.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
      (anti := anti) hIso)

/--
Legacy package-shaped companion `P ≠ NP` endpoint from the canonical eventual
DAG route.
-/
theorem P_ne_NP_final_of_asymptotic_isoStrongRoute
  (hMag : MagnificationAssumptions)
  (hIso : AsymptoticIsoStrongRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker
      (anti := hMag.antiChecker) hIso

/--
Canonical eventual DAG route from witness-indexed promise-YES certificates on
the asymptotic anti-checker package.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
  (hRoute : AsymptoticPromiseYesCertificateRoute hAsym) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute
      hAsym
      hNPbridge
      (asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
        hAsym hRoute)

/--
Anti-checker-only wrapper for the promise-YES-certificate eventual route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute anti.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute
      anti.asymptotic
      anti.npBridge
      hRoute

/--
Legacy package-shaped wrapper for the promise-YES-certificate eventual route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withMagnification
  (hMag : MagnificationAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) hRoute

/--
Companion `P ≠ NP` endpoint from the anti-checker-only eventual
promise-YES-certificate route.
-/
theorem P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute anti.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
      anti hRoute)

/--
Legacy package-shaped companion `P ≠ NP` endpoint from the same eventual
promise-YES-certificate route.
-/
theorem P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) hRoute

/--
Concrete small-DAG witness extracted from one fixed-slice `InPpolyDAG` witness.

This keeps the direct fixed-slice routes independent from the empty legacy
`GapSliceFamily` carrier: source work can target one concrete asymptotic slice
`pAt n hn` without re-encoding it as a whole family.
-/
private def fixedSliceSmallDAGWitness_of_inPpolyDAG
    {p : GapPartialMCSPParams}
    (w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p)) :
    SmallDAGWitnessOnSlice p
      (fun _ s => s ≤ w.polyBound (Models.partialInputLen p)) 1 where
  C := w.family (Models.partialInputLen p)
  hSize := by
    exact w.family_size_le (Models.partialInputLen p)
  hCorrect := by
    constructor
    · intro x hxYes
      have hxLang :
          gapPartialMCSP_Language p (Models.partialInputLen p) x = true := by
        simpa [gapSliceOfParams] using hxYes
      exact (w.correct (Models.partialInputLen p) x).trans hxLang
    · intro x hxNo
      have hxLang :
          gapPartialMCSP_Language p (Models.partialInputLen p) x = false := by
        simpa [gapSliceOfParams] using hxNo
      exact (w.correct (Models.partialInputLen p) x).trans hxLang

/--
Single-slice promise-YES route on a concrete parameter object `p`.

For each hypothetical small-DAG witness for `gapPartialMCSP_Language p`, source
work only has to produce the already-standard witness-level object
`PromiseYesSubcubeCertificateAt`.
-/
def FixedSlicePromiseYesCertificateRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (PromiseYesSubcubeCertificateAt
        (fixedSliceSmallDAGWitness_of_inPpolyDAG w))

/--
Single-slice pairwise promise/value locality route on one concrete parameter
object `p`.

This is the nearest honest upstream source contract already present in the DAG
producer code: it packages both semantic forcing and same-set counting slack in
one witness-level object.
-/
def FixedSlicePromiseValueLocalityRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (PromiseValueLocalityPackageAt
        (fixedSliceSmallDAGWitness_of_inPpolyDAG w))

/--
Single-slice witness-indexed canonical easy-density route on one concrete
parameter object `p`.

This is the fixed-slice version of the density-first source surface: the source
theorem may work against the concrete size bound carried by one strict DAG
witness `w`, with no slice-family transport.
-/
def FixedSliceWitnessEasyDensityRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (CanonicalWitnessEasyDensitySourceAt
        (p := p)
        (fun _ s => s ≤ w.polyBound (Models.partialInputLen p)))

/--
Single-slice witness-uniform-lower route on one concrete parameter object `p`.
-/
def FixedSliceWitnessUniformLowerRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (WitnessUniformLowerSourceAt
        (p := p)
        (fun _ s => s ≤ w.polyBound (Models.partialInputLen p)))

/--
Single-slice quarter-bounded witness-transfer route on one concrete parameter
object `p`.

This is the minimal witness-level transfer surface needed by the counting
closure: produce `EasyImageTransferAt` together with the canonical quarter
bound on its epsilon.
-/
def FixedSliceTransferQuarterRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    ∃ tr : EasyImageTransferAt (fixedSliceSmallDAGWitness_of_inPpolyDAG w),
      tr.epsilon ≤ (1 / 4 : Rat)

/--
Restricted-model fallback route on one concrete parameter object `p`.

This asks only for the direct support-half/value-supported condition on the
concrete canonical DAG witness at the encoded slice length.
-/
def FixedSliceSupportHalfValueSupportedRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
    (DagCircuit.support W.C).card ≤ Models.Partial.tableLen p.n / 2 ∧
      (∀ i ∈ DagCircuit.support W.C,
        ∃ j : Fin (Models.Partial.tableLen p.n), tableValPos j = i)

/--
Single-slice strong-fallback slack route on one concrete parameter object `p`.

This is the accepted-family-side witness object already produced by the older
restriction/shrinkage pipeline: one encoded-coordinate restriction with direct
counting slack and local dependence for the concrete canonical DAG witness.
-/
def FixedSliceDAGStableRestrictionSlackRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (DAGStableRestrictionSlackPackageAt
        (fixedSliceSmallDAGWitness_of_inPpolyDAG w))

/--
Single-slice shrinkage-certificate route on one concrete parameter object `p`.

This is a more atomic source surface than the slack package: source work only
has to provide the shrinkage certificate for the general solver induced by the
concrete canonical DAG witness.
-/
def FixedSliceShrinkageCertificateRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (SmallDAGWitnessShrinkageCertificateAt
        (fixedSliceSmallDAGWitness_of_inPpolyDAG w))

/--
Single-slice restriction-data route on one concrete parameter object `p`.

This is the most decomposed strong-fallback source package currently available
in the DAG producer code: one restriction together with its numeric side data
and stability proof for the concrete canonical DAG witness.
-/
def FixedSliceRestrictionDataRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    Nonempty
      (SmallDAGWitnessRestrictionCertificateDataAt
        (fixedSliceSmallDAGWitness_of_inPpolyDAG w))

/--
Single-slice support-numeric route on one concrete parameter object `p`.

This fixes semantic extraction to the canonical support-based one and asks
source work only for the numeric side-data package on top of that extraction.
-/
def FixedSliceSupportNumericRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
    Nonempty
      (SmallDAGWitnessRestrictionNumericDataAt
        (smallDAGWitnessRestrictionExtractionAt_of_support W))

/--
Single-slice support-component route on one concrete parameter object `p`.

This is the most explicit live Route-A2 target currently available in the DAG
producer stack: prove the three numeric support-side inequalities directly on
the canonical support extraction of the concrete fixed-slice DAG witness.
-/
def FixedSliceSupportNumericComponentRoute
    (p : GapPartialMCSPParams) : Prop :=
  ∀ w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p),
    let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
    (DagCircuit.support W.C).card ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
      (DagCircuit.support W.C).card ≤
        Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial p) / 4 ∧
      (DagCircuit.support W.C).card *
          (Nat.log2
              ((ThirdPartyFacts.toFactsGeneralSolverPartial
                  (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
                ((DagCircuit.support W.C).card.succ) + 2) +
            (ThirdPartyFacts.toFactsGeneralSolverPartial
                (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth + 1)
        ≤
        Facts.LocalityLift.inputLen
          (ThirdPartyFacts.toFactsParamsPartial p) / 2

/--
Compile the stronger fixed-slice promise/value locality route to the weaker
fixed-slice promise-YES route.
-/
theorem fixedSlicePromiseYesCertificateRoute_of_fixedSlicePromiseValueLocalityRoute
    {p : GapPartialMCSPParams}
    (hPkg : FixedSlicePromiseValueLocalityRoute p) :
    FixedSlicePromiseYesCertificateRoute p := by
  intro w
  rcases hPkg w with ⟨pkg⟩
  exact ⟨promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt pkg⟩

/--
Compile the restricted-model support-half/value-supported fallback to the
fixed-slice promise-YES route.
-/
theorem fixedSlicePromiseYesCertificateRoute_of_fixedSliceSupportHalfValueSupportedRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceSupportHalfValueSupportedRoute p) :
    FixedSlicePromiseYesCertificateRoute p := by
  intro w
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨hHalf, hValue⟩
  exact ⟨promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported W hHalf hValue⟩

/--
Compile the fixed-slice restriction-data route to the corresponding
shrinkage-certificate route.
-/
theorem fixedSliceShrinkageCertificateRoute_of_fixedSliceRestrictionDataRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceRestrictionDataRoute p) :
    FixedSliceShrinkageCertificateRoute p := by
  intro w
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨data⟩
  exact ⟨smallDAGWitnessShrinkageCertificateAt_of_restrictionData W data⟩

/--
Compile the fixed-slice shrinkage-certificate route to the corresponding
strong-fallback slack route.
-/
theorem fixedSliceDAGStableRestrictionSlackRoute_of_fixedSliceShrinkageCertificateRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceShrinkageCertificateRoute p) :
    FixedSliceDAGStableRestrictionSlackRoute p := by
  intro w
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨cert⟩
  exact ⟨dagStableRestrictionSlackPackageAt_of_shrinkageCertificate W cert⟩

/--
Compile the fixed-slice support-numeric route to the corresponding
restriction-data route by using the canonical support extraction.
-/
theorem fixedSliceRestrictionDataRoute_of_fixedSliceSupportNumericRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceSupportNumericRoute p) :
    FixedSliceRestrictionDataRoute p := by
  intro w
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨num⟩
  exact
    ⟨smallDAGWitnessRestrictionCertificateDataAt_of_extractionAndNumeric
      (smallDAGWitnessRestrictionExtractionAt_of_support W) num⟩

/--
Compile the explicit fixed-slice support-component route to the corresponding
support-numeric route.
-/
theorem fixedSliceSupportNumericRoute_of_fixedSliceSupportNumericComponentRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceSupportNumericComponentRoute p) :
    FixedSliceSupportNumericRoute p := by
  intro w
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨hPolylog, hQuarter, hArith⟩
  have hSmallEnough :
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.size *
              (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card.succ
        , ℓ := (smallDAGWitnessRestrictionExtractionAt_of_support W).r.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfSmallDAGWitnessOnSlice W)).params.depth } := by
    simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
      smallDAGWitnessRestrictionExtractionAt_of_support] using hArith
  have hPolylogAlive :
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) := by
    simpa [smallDAGWitnessRestrictionExtractionAt_of_support] using hPolylog
  have hQuarterAlive :
      (smallDAGWitnessRestrictionExtractionAt_of_support W).aliveBound ≤
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 := by
    simpa [smallDAGWitnessRestrictionExtractionAt_of_support] using hQuarter
  exact
    ⟨smallDAGWitnessSupportNumericDataAt_of_components
      W hPolylogAlive hQuarterAlive hSmallEnough⟩

/--
Compile the stronger single-slice witness-uniform-lower route to the
single-slice witness-indexed canonical easy-density route.
-/
theorem fixedSliceWitnessEasyDensityRoute_of_fixedSliceWitnessUniformLowerRoute
    {p : GapPartialMCSPParams}
    (hUniform : FixedSliceWitnessUniformLowerRoute p) :
    FixedSliceWitnessEasyDensityRoute p := by
  intro w
  rcases hUniform w with ⟨src⟩
  exact
    ⟨canonicalWitnessEasyDensitySourceAt_of_witnessUniformLowerSourceAt src⟩

/--
Compile the single-slice witness-indexed canonical easy-density route to the
single-slice quarter-bounded witness-transfer route.
-/
theorem fixedSliceTransferQuarterRoute_of_fixedSliceWitnessEasyDensityRoute
    {p : GapPartialMCSPParams}
    (hDensity : FixedSliceWitnessEasyDensityRoute p) :
    FixedSliceTransferQuarterRoute p := by
  intro w
  rcases hDensity w with ⟨src⟩
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  refine ⟨easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt src W, ?_⟩
  let tr : EasyImageTransferAt W :=
    easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt src W
  have hQuarter : tr.epsilon ≤ (1 / 4 : Rat) := by
    simpa [tr] using src.hEpsQuarter
  simpa [W, tr]
    using hQuarter

/--
Compile the stronger single-slice witness-uniform-lower route directly to the
single-slice quarter-bounded witness-transfer route.
-/
theorem fixedSliceTransferQuarterRoute_of_fixedSliceWitnessUniformLowerRoute
    {p : GapPartialMCSPParams}
    (hUniform : FixedSliceWitnessUniformLowerRoute p) :
    FixedSliceTransferQuarterRoute p := by
  exact
    fixedSliceTransferQuarterRoute_of_fixedSliceWitnessEasyDensityRoute
      (fixedSliceWitnessEasyDensityRoute_of_fixedSliceWitnessUniformLowerRoute
        hUniform)

/--
Collapse one fixed slice once direct witness-level promise-YES certificates are
available for every hypothetical `InPpolyDAG` witness on that slice.
-/
theorem fixedSliceCollapse_of_fixedSlicePromiseYesCertificateRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSlicePromiseYesCertificateRoute p) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  intro hDag
  let w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p) :=
    Classical.choose hDag
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  let cert : PromiseYesSubcubeCertificateAt W :=
    Classical.choice (hRoute w)
  exact no_small_dag_solver_of_promiseYesSubcubeCertificateAt W cert

/--
Collapse one fixed slice once witness-level strong-fallback slack packages are
available for every hypothetical `InPpolyDAG` witness on that slice.
-/
theorem fixedSliceCollapse_of_fixedSliceDAGStableRestrictionSlackRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceDAGStableRestrictionSlackRoute p) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  intro hDag
  let w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p) :=
    Classical.choose hDag
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  let cert : DAGStableRestrictionSlackPackageAt W :=
    Classical.choice (hRoute w)
  exact no_small_dag_solver_of_dagStableRestrictionSlackPackageAt_via_acceptedFamily
    W cert

/--
Collapse one fixed slice once witness-level shrinkage certificates are
available for every hypothetical `InPpolyDAG` witness on that slice.
-/
theorem fixedSliceCollapse_of_fixedSliceShrinkageCertificateRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceShrinkageCertificateRoute p) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  exact
    fixedSliceCollapse_of_fixedSliceDAGStableRestrictionSlackRoute
      (fixedSliceDAGStableRestrictionSlackRoute_of_fixedSliceShrinkageCertificateRoute
        hRoute)

/--
Collapse one fixed slice once witness-level restriction data are available for
every hypothetical `InPpolyDAG` witness on that slice.
-/
theorem fixedSliceCollapse_of_fixedSliceRestrictionDataRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceRestrictionDataRoute p) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  exact
    fixedSliceCollapse_of_fixedSliceShrinkageCertificateRoute
      (fixedSliceShrinkageCertificateRoute_of_fixedSliceRestrictionDataRoute
        hRoute)

/--
Collapse one fixed slice once quarter-bounded witness-level transfer is
available for every hypothetical `InPpolyDAG` witness on that slice.
-/
theorem fixedSliceCollapse_of_fixedSliceTransferQuarterRoute
    {p : GapPartialMCSPParams}
    (hRoute : FixedSliceTransferQuarterRoute p) :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  intro hDag
  let w : ComplexityInterfaces.InPpolyDAG (gapPartialMCSP_Language p) :=
    Classical.choose hDag
  let W := fixedSliceSmallDAGWitness_of_inPpolyDAG w
  rcases hRoute w with ⟨tr, hQuarter⟩
  have hQuarterCount :
      (1 / 4 : Rat) <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat)) :=
    quarter_lt_one_sub_countRatio_of_circuit_bound_ok p
  have hEpsSmall :
      tr.epsilon <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat)) :=
    lt_of_le_of_lt hQuarter hQuarterCount
  exact no_small_dag_solver_of_easyImageTransferAt_of_counting W tr hEpsSmall

/--
Collapse the asymptotic DAG language once one fixed slice is known to avoid
`PpolyDAG`.

This is the shortest anti-checker-only integration route to DAG separation:
1. choose any concrete asymptotic slice `pAt n hn`,
2. prove fixed-slice collapse there,
3. transport it back to the asymptotic language using slice agreement.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (n : Nat) (hn : anti.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (anti.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  let p : GapPartialMCSPParams := anti.asymptotic.pAt n hn
  have hCollapseAsym :
      ComplexityInterfaces.PpolyDAG
        (gapPartialMCSP_AsymptoticLanguage anti.asymptotic.spec) → False :=
    fun hAsymDag =>
      hCollapseFixed
        (ppolyDAG_fixed_of_asymptotic_slice
          (spec := anti.asymptotic.spec)
          (p := p)
          (anti.asymptotic.sliceEq n hn)
          hAsymDag)
  exact
    ⟨gapPartialMCSP_AsymptoticLanguage anti.asymptotic.spec,
      anti.npBridge.strictAsymptotic,
      hCollapseAsym⟩

/--
Legacy package-shaped wrapper for the fixed-slice collapse route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hCollapseFixed

/--
Companion `P ≠ NP` endpoint from the anti-checker-only fixed-slice collapse
input.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
  (anti : AntiCheckerAssumptions)
  (n : Nat) (hn : anti.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (anti.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
      (anti := anti) (n := n) (hn := hn) hCollapseFixed)

/--
Legacy package-shaped companion `P ≠ NP` endpoint from the same fixed-slice
collapse input.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hCollapseFixed

/--
Asymptotic DAG separation from the direct fixed-slice promise-YES witness route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSlicePromiseYesCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
    (hMag := hMag) (n := n) (hn := hn)
  exact fixedSliceCollapse_of_fixedSlicePromiseYesCertificateRoute hRoute

/--
Companion `P ≠ NP` endpoint from the same fixed-slice promise-YES witness route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSlicePromiseYesCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the direct fixed-slice promise/value locality
route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hPkg :
    FixedSlicePromiseValueLocalityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSlicePromiseYesCertificateRoute_of_fixedSlicePromiseValueLocalityRoute
        hPkg)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice promise/value locality
route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hPkg :
    FixedSlicePromiseValueLocalityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute
      (hMag := hMag) (n := n) (hn := hn) hPkg)

/--
Asymptotic DAG separation from the restricted-model support-half/value-supported
fallback on one fixed slice.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportHalfValueSupportedRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSlicePromiseYesCertificateRoute_of_fixedSliceSupportHalfValueSupportedRoute
        hRoute)

/--
Companion `P ≠ NP` endpoint from the same restricted-model fixed-slice
fallback.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportHalfValueSupportedRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice strong-fallback slack route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceDAGStableRestrictionSlackRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
    (hMag := hMag) (n := n) (hn := hn)
  exact fixedSliceCollapse_of_fixedSliceDAGStableRestrictionSlackRoute hRoute

/--
Companion `P ≠ NP` endpoint from the same fixed-slice strong-fallback slack
route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceDAGStableRestrictionSlackRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice shrinkage-certificate route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceShrinkageCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceDAGStableRestrictionSlackRoute_of_fixedSliceShrinkageCertificateRoute
        hRoute)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice shrinkage-certificate
route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceShrinkageCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice restriction-data route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceRestrictionDataRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceRestrictionDataRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceShrinkageCertificateRoute_of_fixedSliceRestrictionDataRoute
        hRoute)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice restriction-data route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceRestrictionDataRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceRestrictionDataRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceRestrictionDataRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice support-numeric route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceRestrictionDataRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceRestrictionDataRoute_of_fixedSliceSupportNumericRoute hRoute)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice support-numeric route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the explicit fixed-slice support-component route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericComponentRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericComponentRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceSupportNumericRoute_of_fixedSliceSupportNumericComponentRoute
        hRoute)

/--
Companion `P ≠ NP` endpoint from the same explicit fixed-slice
support-component route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericComponentRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericComponentRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericComponentRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice quarter-bounded transfer route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceTransferQuarterRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
    (hMag := hMag) (n := n) (hn := hn)
  exact fixedSliceCollapse_of_fixedSliceTransferQuarterRoute hRoute

/--
Companion `P ≠ NP` endpoint from the same fixed-slice quarter-bounded transfer
route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceTransferQuarterRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceTransferQuarterRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute
      (hMag := hMag) (n := n) (hn := hn) hRoute)

/--
Asymptotic DAG separation from the fixed-slice witness-indexed canonical
easy-density route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hDensity :
    FixedSliceWitnessEasyDensityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceTransferQuarterRoute_of_fixedSliceWitnessEasyDensityRoute hDensity)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice witness-indexed canonical
easy-density route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hDensity :
    FixedSliceWitnessEasyDensityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute
      (hMag := hMag) (n := n) (hn := hn) hDensity)

/--
Asymptotic DAG separation from the fixed-slice witness-uniform-lower route.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hUniform :
    FixedSliceWitnessUniformLowerRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (fixedSliceTransferQuarterRoute_of_fixedSliceWitnessUniformLowerRoute
        hUniform)

/--
Companion `P ≠ NP` endpoint from the same fixed-slice witness-uniform-lower
route.
-/
theorem P_ne_NP_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hUniform :
    FixedSliceWitnessUniformLowerRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute
      (hMag := hMag) (n := n) (hn := hn) hUniform)

/--
Asymptotic DAG separation from the fixed-slice stable-restriction producer.

Compared with the older `_TM` wrappers, this route uses the global NP witness
already packaged in `MagnificationAssumptions` and therefore no longer needs a
separate fixed-slice TM witness.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
    (hMag := hMag) (n := n) (hn := hn)
  exact LowerBounds.not_ppolyDAG_of_dag_stableRestriction hStable

/--
Companion `P ≠ NP` endpoint from the same fixed-slice stable-restriction
producer.
-/
theorem P_ne_NP_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
      (hMag := hMag) (n := n) (hn := hn) hStable)

/--
Asymptotic DAG separation from the localized Route-B source-closure package on
one concrete asymptotic slice.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
    (hMag := hMag) (n := n) (hn := hn)
  exact LowerBounds.dag_stableRestriction_producer_of_sourceClosure hSrc

/--
Companion `P ≠ NP` endpoint from the same asymptotic fixed-slice
source-closure package.
-/
theorem P_ne_NP_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
      (hMag := hMag) (n := n) (hn := hn) hSrc)

/--
Asymptotic DAG separation from the named Route-B blocker on one concrete
asymptotic slice.
-/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
    (hMag := hMag) (n := n) (hn := hn)
  exact
    LowerBounds.dagRouteBSourceClosure_of_blocker
      (p := hMag.antiChecker.asymptotic.pAt n hn) hBlocker

/--
Companion `P ≠ NP` endpoint from the same asymptotic fixed-slice blocker.
-/
theorem P_ne_NP_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
      (hMag := hMag) (n := n) (hn := hn) hBlocker)

end Magnification
end Pnp3
