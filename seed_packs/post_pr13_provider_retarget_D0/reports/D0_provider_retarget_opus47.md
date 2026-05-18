# post-PR13 — provider retarget feasibility audit

Handle: `opus47`

Date: 2026-05-18.

Commit base: `1e0454f` (PR 13 squash on `main`).

## 1. Executive verdict

**`RETARGET_EXISTING_ROUTE`.**

Two non-refuted downstream consumers of the canonical asymptotic
infrastructure already exist in-tree and are wired into
`pnp3/Tests/CanonicalIntegrationTests.lean`:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`, consumed by
  `Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`;
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`,
  consumed by
  `Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`.

Both directly target `NP_not_subset_PpolyDAG` (the trust-root goal, not
the refuted `NP_not_subset_PpolyFormula` cone), neither imports
`FormulaCertificateProviderPartial`, and neither universally quantifies
over arbitrary `PpolyFormula` witnesses.  Both have a hypothesis surface
of the shape `∀ hInDag : (∀ n β, InPpolyDAG …), <structural payload>`,
which is the standard magnification "small DAG ⇒ structural
combinatorics" research direction — research-open, not formally refuted
in-repo as of `1e0454f`.

Caveat: the verdict is *retarget feasibility*, not closure.  The
structural-payload halves of these routes are research-open
mathematical content.  D0 cannot certify them as eventually closable.

The 7-session TM-verifier plan therefore retains value as **NP-side
infrastructure**: a TM witness `W : GapPartialMCSP_Asymptotic_TMWitness
canonicalAsymptoticSpec` discharges the asymptotic NP membership half
(`canonicalAsymptoticNPBridge_of_TM W` →
`canonicalAntiCheckerAssumptions_of_TM W`), which is consumed by the
non-refuted routes above as the `anti` parameter.  It does not by
itself close `NP_not_subset_PpolyDAG`; the iso-strong / promise-YES
hypothesis still has to be discharged by an independent mathematical
theorem.

## 2. What PR 13 killed

PR 13 added Probe 13 to
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`:

```
theorem false_of_FormulaCertificateProviderPartial
    (p : GapPartialMCSPParams)
    (hCert : Magnification.FormulaCertificateProviderPartial) : False
```

The refutation is a 3-line composition of already-landed lemmas:

1. `fixedSlice_gapPartialMCSP_in_PpolyFormula` (Probe 2,
   `FormulaSupportBoundsFalsifiabilityProbe.lean:218`) — for any `p`,
   the truth-table hardwiring of `gapPartialMCSP_Language p` at the
   single relevant input length `partialInputLen p` produces a
   `PpolyFormula` witness;
2. `abstractGapTargetedSingletonDensityPayload_of_internal_provider`
   (`LowerBounds/SingletonDensityContradiction.lean:1344`) — combined
   with the gap-target internal provider, this yields a non-empty
   `AbstractGapTargetedSingletonDensityPayload p`;
3. `false_of_abstractGapTargetedPayload_of_formulaCertificate`
   (`LowerBounds/SingletonDensityContradiction.lean:586`) — the payload
   + `hCert` + `hFormula` close `False` via
   `MCSPGapLocality.no_local_function_solves_mcsp`.

Root cause: `FormulaCertificateProviderPartial.cert` universally
quantifies over any `hFormula : PpolyFormula (gapPartialMCSP_Language p)`
and promises a small-locality stable restriction.  The universal
quantifier is satisfied by the truth-table-hardwired witness from
Probe 2, contradicting MCSP gap locality.  This is the same structural
failure that previously killed
`FormulaSupportRestrictionBoundsPartial`,
`FormulaSupportBoundsFromMultiSwitchingContract`,
`MagnificationAssumptions`, `FormulaSupportBoundsPartial_fromPipeline`,
and `MagnificationAssumptions_fromPipeline` (Probes 3, 4, 6, 7, 7b).

**Now ex-falso downstream wrappers** (each is a theorem of the form
`hCert → …`, and `hCert → False` is provable, so the conclusion is
vacuous):

- `i4_final_wiring_of_formulaCertificate`
  (`pnp3/Tests/BridgeLocalityRegression.lean:60`).
- `structuredLocalityProviderPartial_of_formulaCertificate`
  (`pnp3/Magnification/LocalityProvider_Partial.lean:3225`).
- `dag_stableRestrictionGoal_of_formulaCertificate`
  (`pnp3/LowerBounds/SingletonDensityContradiction.lean:2210`).
- `dag_stableRestriction_producer_of_formulaCertificate`
  (`pnp3/LowerBounds/SingletonDensityContradiction.lean:2228`).
- All transitive consumers of the above, including
  `canonical_NP_not_subset_PpolyFormula_of_formulaCertificate`
  (`pnp3/Tests/CanonicalIntegrationTests.lean:67`).

These remain in-project per the policy applied to the other ⚠ siblings
from sessions 59–67: they compile, they have warning docstrings, they
are exposed for the audit trail, and they must NOT be presented as
progress toward unconditional `NP ⊄ P/poly`.

## 3. What PR 13 did NOT kill

PR 13 only touched the `FormulaCertificateProviderPartial` lineage.  The
canonical asymptotic infrastructure is logically independent of that
predicate.  None of the following imports
`FormulaCertificateProviderPartial`, none of them quantifies over
arbitrary `PpolyFormula` witnesses, and none of them is refuted by the
existing falsifiability probes 1–13:

- `Magnification.canonicalAsymptoticSpec` (the minimal legal spec,
  `sYES = 1`, `sNO = 2`) and the per-slice parameter builder
  `canonicalAsymptoticParams n hn` — fully proved unconditionally.
- `Magnification.canonicalShannonBound`, `canonicalSliceEq` —
  unconditional Lean technical bridges.
- `Magnification.canonicalAsymptoticHAsym :
  AsymptoticFormulaTrackHypothesis` — **unconditional** fill of the
  type-data structure.
- `Magnification.canonicalAsymptoticNPBridge_of_TM W`,
  `canonicalAsymptoticData_of_TM W`,
  `canonicalAntiCheckerAssumptions_of_TM W` — strict NP packages
  parameterised by a single TM witness.
- `Magnification.decideAsymptotic`,
  `Magnification.decideAsymptotic_iff` — a computable Boolean decider
  pointwise equal to `gapPartialMCSP_AsymptoticLanguage canonicalSpec`,
  plus its correctness theorem.
- `Magnification.findCanonicalSlice`,
  `Magnification.findCanonicalSlice_eq_some_iff`,
  `Magnification.findCanonicalSlice_eq_none_iff`,
  `Magnification.decideYesAt1`, `Magnification.decideYesAt1_iff`.
- `Magnification.CanonicalAsymptoticVerifierComponents` and
  `CanonicalAsymptoticVerifierComponents.witness` — the
  components-track bridge to the TM-witness.
- `Magnification.canonicalAntiCheckerAssumptions_of_components`.
- `Models.is_consistent_iff_bool`,
  `Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen`,
  `Models.vecOfNat_bitVecToNat` — supporting decoder lemmas.

The supporting fact bank — Shannon counting, slice equality, decider
correctness, components-to-witness bridge — is purely combinatorial /
computational Lean infrastructure with no dependency on any refuted
predicate.

## 4. Existing possible replacement consumers

Audit of routes that consume `canonicalAsymptoticHAsym` or the
canonical TM-witness output, but do NOT consume
`FormulaCertificateProviderPartial`:

### 4.1 `AsymptoticIsoStrongRoute`

- Exact theorem: `Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`
  (`pnp3/Magnification/FinalResultMainline.lean:1059`).
- Required hypotheses:
  - `anti : AntiCheckerAssumptions` (canonical track supplies this
    from a TM witness `W`);
  - `hIso : AsymptoticIsoStrongRoute anti.asymptotic`.
- Avoids `FormulaCertificateProviderPartial`: **yes**.  The route's
  Prop is
  `∀ hInDag : (∀ n β, InPpolyDAG (gapPartialMCSP_Language …)),
    IsoStrongFamilyEventually …`.
  `FormulaCertificateProviderPartial` does not appear in the
  definition or its dependency closure.
- Avoids universal `PpolyFormula` quantification: **yes**.  The
  universal is over `hInDag : InPpolyDAG …`, not over
  `hFormula : PpolyFormula …`.  Truth-table hardwiring on a single
  slice does not produce a polynomial-size DAG family for the entire
  asymptotic family (per-slice 2^n truth-table DAG is size 2^N at
  input length N = 2·2^m, i.e. exponential), so Probe 2's hardwiring
  attack does not directly satisfy `hInDag`.
- Known NoGo risk: NOGO-000004 / NOGO-000006 / NOGO-000008 / NOGO-000009
  are filter-side barriers against syntactic `PpolyFormula` filters;
  they do **not** apply directly to the `InPpolyDAG` hypothesis or to
  the iso-strong family conclusion.  There is no
  `false_of_AsymptoticIsoStrongRoute` theorem in the repository.
- Verdict: **usable, hypothesis surface is research-open.**  Closing
  this route still requires producing
  `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic
  canonicalAsymptoticHAsym) hInDag` from
  `∀ n β, InPpolyDAG (gapPartialMCSP_Language …)`, which is the
  conventional magnification target ("small DAGs ⇒ iso-strong
  combinatorics").

### 4.2 `AsymptoticPromiseYesCertificateRoute`

- Exact theorem: `Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`
  (`pnp3/Magnification/FinalResultMainline.lean:1100`).
- Required hypotheses: as in 4.1 but with
  `hRoute : AsymptoticPromiseYesCertificateRoute anti.asymptotic`.
- Avoids `FormulaCertificateProviderPartial`: **yes**.
- Avoids universal `PpolyFormula` quantification: **yes**.  Universal
  is over `hInDag : InPpolyDAG …` and asks for the
  `PromiseYesSubcubeCertificateAt W` data per slice for sufficiently
  large `n`.
- Known NoGo risk: same as 4.1; `PromiseYesSubcubeCertificateAt` is a
  combinatorial certificate over partial truth tables, not over
  `PpolyFormula` witnesses, so syntactic-filter NoGos do not directly
  apply.  No `false_of_AsymptoticPromiseYesCertificateRoute` theorem.
- Verdict: **usable, hypothesis surface is research-open.**

### 4.3 `AsymptoticPromiseYesWeakRouteEventually`

- Exact theorem (downstream): the chain
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  (`pnp3/Magnification/FinalResultMainline.lean:348`) converts the
  weak route to 4.2 mechanically.
- Required hypothesis: `hRoute : AsymptoticPromiseYesWeakRouteEventually
  hAsym`.
- Avoids `FormulaCertificateProviderPartial`: **yes**.
- Avoids universal `PpolyFormula` quantification: **yes**.
- Verdict: **usable as upstream-of-4.2 entry point.**  Same
  research-open status as 4.2.

### 4.4 Optional sub-route surfaces

The `WeakRouteSurfaceTests.lean` file exposes additional intermediate
shapes (`promiseYesAcceptanceInvariantAt_of_strictDAGSemantics`, etc.)
that participate in 4.2's payload construction.  These are
combinatorial lemmas wired into the route, not independent consumers.
They are reused as-is and do not introduce a new universal-`PpolyFormula`
surface.

### 4.5 pnp4 frontier — `SearchMCSPWeakLowerBound`

- Exact structure: `Frontier.SearchMCSPWeakLowerBound`
  (`pnp4/Pnp4/Frontier/CompressionMagnification.lean`).
- Required hypotheses: `weakLowerBound : Prop` +
  `weakLowerBoundProof : weakLowerBound` +
  `magnifiesToVerifiedDAGSource : weakLowerBound →
  VerifiedNPDAGLowerBoundSource`.
- Avoids `FormulaCertificateProviderPartial`: **yes**.
- Avoids universal `PpolyFormula` quantification: **yes**.
- Known NoGo risk: this package is the longer-horizon
  search-MCSP / compression magnification interface.  The previous
  `fp3b8` D0 audit (handle `gpt55`) issued **RED-light** for designing a
  full Round 1 against it without a concrete weak-lower-bound source
  theorem, on the grounds that the decisive content is entirely in
  the magnification map.
- Verdict: **wrapper / interface-only.**  Not refuted, but not a
  retarget of the canonical asymptotic infrastructure either — the
  pnp4 search-MCSP interface is upstream of `VerifiedNPDAGLowerBoundSource`,
  not downstream of `canonicalAsymptoticHAsym`.  It is a separate
  research surface that the post-PR13 retarget does not feed.

### 4.6 Contract-expansion route

The `seed_packs/source_search_contract_expansion_*` D0 / R1A / R1B
chain investigated a runtime-aware codec / parser / prefix-language
contract-expansion approach.  None of those seed packs introduced a
downstream consumer of `canonicalAsymptoticHAsym`; the work targets
the upstream codec/parser interface for the asymptotic
`gapPartialMCSP_AsymptoticLanguage` decoder, not the magnification
output.

- Verdict: **upstream of canonical track, not a retarget candidate
  for D0.**  May be reusable in the TM-verifier plan if redirected
  (see section 7).

### 4.7 Summary table

| Consumer                                                     | Refuted? | Avoids `FormulaCertificateProviderPartial`? | Avoids universal `PpolyFormula`? | Verdict                                     |
| ------------------------------------------------------------ | -------- | ------------------------------------------- | -------------------------------- | ------------------------------------------- |
| `i4_final_wiring_of_formulaCertificate`                      | ✅ yes (PR 13) | ❌ no                                        | ❌ no                              | refuted (ex-falso wrapper)                  |
| `structuredLocalityProviderPartial_of_formulaCertificate`    | ✅ yes (PR 13) | ❌ no                                        | ❌ no                              | refuted                                     |
| `dag_stableRestrictionGoal_of_formulaCertificate`            | ✅ yes (PR 13) | ❌ no                                        | ❌ no                              | refuted                                     |
| `dag_stableRestriction_producer_of_formulaCertificate`       | ✅ yes (PR 13) | ❌ no                                        | ❌ no                              | refuted                                     |
| `AsymptoticIsoStrongRoute` (+ `_withAntiChecker` final)      | ❌ no    | ✅ yes                                       | ✅ yes                            | **usable, research-open**                   |
| `AsymptoticPromiseYesCertificateRoute` (+ `_withAntiChecker` final) | ❌ no    | ✅ yes                                       | ✅ yes                            | **usable, research-open**                   |
| `AsymptoticPromiseYesWeakRouteEventually`                    | ❌ no    | ✅ yes                                       | ✅ yes                            | usable upstream                              |
| `SearchMCSPWeakLowerBound` (pnp4)                            | ❌ no    | ✅ yes                                       | ✅ yes                            | wrapper; not a retarget of canonical track  |
| Contract-expansion codec/parser                              | n/a      | n/a (upstream)                              | n/a                              | upstream of canonical track                  |

## 5. New provider sketch

Because the verdict is `RETARGET_EXISTING_ROUTE`, this section is **not
applicable**.  No new provider contract is proposed in D0.

If a follow-up audit later finds that both `AsymptoticIsoStrongRoute`
and `AsymptoticPromiseYesCertificateRoute` are vacuously satisfied at
the canonical spec (`sYES = 1`, `sNO = 2`) — e.g., because the
canonical asymptotic language is in P/poly via a constructive in-repo
witness, and the routes' `hInDag` therefore admits a trivial
discharge — then a new provider sketch would be required and should be
opened as a separate D0.  D0 (this report) does not establish or
refute that vacuity.

## 6. Hardwiring audit (against the retarget verdict)

For each hardwiring NoGo, test whether the proposed retarget
(`AsymptoticIsoStrongRoute` / `AsymptoticPromiseYesCertificateRoute`
consumed by the `_withAntiChecker` mainline endpoints) is robust:

### 6.1 NOGO-000004 (`prefixAnd` log-width hardwiring)

- Original target: support-cardinality-only `PpolyFormula` provenance
  filters.
- Attack vector: a `prefixAnd n (Nat.log2 (n+1)) _` family is a
  polynomial-size formula whose syntactic support is `Nat.log2 (n+1)`
  (sublinear and unbounded), satisfying
  `FP3Attempt.InSupportFunctionalDiversity`.
- Robustness of retarget: the retargeted routes do not contain a
  `PpolyFormula` provenance filter at all; their hypothesis is
  `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language …)`, an
  *assumption* about DAG membership of the entire family.  Per-slice
  prefix-AND log-width hardwiring is a `PpolyFormula` construction that
  does not produce a polynomial-size DAG family asymptotically (it is
  per-slice).  **Robust.**

### 6.2 NOGO-000006 (arbitrary all-essential ttFormula payload)

- Original target: same support-cardinality-only filter, generalised
  attack with arbitrary `AllEssentialPayload F` and
  `FormulaCircuit.rename (embed _) (ttFormula (F n))`.
- Attack vector: `ttFormula` hardwiring of a per-slice Boolean
  function at width `Nat.log2 (n+1)` is admitted by syntactic-support
  filters.
- Robustness of retarget: per-slice `ttFormula` hardwiring does not
  give an asymptotic `InPpolyDAG` witness for the canonical
  `gapPartialMCSP_AsymptoticLanguage` (the canonical input length is
  `2·2^m`, so a `ttFormula`-shaped DAG at slice `m` has size
  `2^(2·2^m) = 2^N` exponential in `N`).  The retargeted route's
  hypothesis is about asymptotic DAG membership of the WHOLE family
  with a uniform polynomial size bound, which the
  `ttFormula`-hardwiring attack does not satisfy.  **Robust.**

### 6.3 NOGO-000008 (tautological-seed syntactic rewrite)

- Original target: syntactic-only `ProvenanceFilter_v2` candidates
  (V2-A and similar).
- Attack vector: conjoining a polynomial-size hardwiring witness with
  `x_0 ∨ ¬x_0` produces a semantically identical, syntactically
  distinct witness that survives any displayed-gate-count / OR-NOT
  filter.
- Robustness of retarget: the retargeted route has no syntactic
  `PpolyFormula` filter, so the rewrite attack has no surface to act
  on.  **Robust.**

### 6.4 NOGO-000009 (normalisation meta-barrier)

- Original target: structural-normalisation patches on V2-A
  syntactic filters.
- Attack vector: any normaliser that collapses tautological seeds also
  collapses the filter's own non-vacuity witness.
- Robustness of retarget: no syntactic filter, no normaliser.
  **Robust.**

### 6.5 PR 13 (`FormulaCertificateProviderPartial → False`)

- Original target: `FormulaCertificateProviderPartial`.
- Attack vector: truth-table hardwiring of `gapPartialMCSP_Language p`
  at the single relevant input length `partialInputLen p` gives a
  `PpolyFormula` witness; combined with the gap-target singleton-
  density payload it forces `False`.
- Robustness of retarget: the retargeted routes do not import or
  consume `FormulaCertificateProviderPartial`.  Their hypothesis is
  `∀ hInDag : (∀ n β, InPpolyDAG …), …`; the truth-table-hardwiring
  attack against `PpolyFormula` does not transfer because per-slice
  hardwiring is exponential-size as a DAG (see 6.2).  **Robust.**

### 6.6 Open hardwiring questions for the retarget

These are NOT existing NoGo entries.  They are NEW probes that a
follow-up D0 against the retarget should formalise:

1. Is `∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic
   canonicalAsymptoticHAsym).paramsOf n β))` provable in-repo from
   `P_subset_PpolyDAG_internal` alone?  If yes, the canonical-spec
   `hInDag` is vacuously dischargeable and the retarget is at risk of
   being trivially satisfied through the hypothesis side.
2. Does there exist a "canonical-asymptotic ttFormula-DAG twin"
   (i.e., an `InPpolyDAG` witness of `ttFormula`-hardwiring shape that
   wins on every slice but fails an iso-strong family construction)?
   This would be the asymptotic analogue of the PR 13 attack.
3. Is `IsoStrongFamilyEventually` invariant under a syntactic-DAG
   rewrite analogue of NOGO-000008?

These three probes are the natural successors of PR 13's audit
trail.  They are not in scope for D0 itself; they motivate the
follow-up D0 in section 8.

## 7. Recommendation on TMVerifier sessions

**`continue_only_as_reusable_NP_infrastructure`.**

Rationale:

- The 7-session plan in `pnp3/Docs/TMVerifier_Session_Plan.md`
  produces a `Models.GapPartialMCSP_Asymptotic_TMWitness
  canonicalAsymptoticSpec`, which is consumed by both
  `canonicalAsymptoticNPBridge_of_TM W` (refuted-cone consumer) AND
  `canonicalAntiCheckerAssumptions_of_TM W` (non-refuted consumer
  feeding the `_isoStrongRoute_withAntiChecker` /
  `_promiseYesCertificateRoute_withAntiChecker` endpoints).
- The same TM witness, fed via
  `canonicalAntiCheckerAssumptions_of_TM W`, is the AntiChecker payload
  for the non-refuted final endpoints.  This is the published
  OPS19/CJW20 fact "GapMCSP ∈ NP" — half of any honest magnification
  proof.
- However, **closing the TM-verifier alone does NOT close
  `NP_not_subset_PpolyDAG`** through the retargeted routes.  It only
  discharges the `AntiCheckerAssumptions` package.  The route
  hypothesis (`hIso` or `hRoute`) is the remaining research-open
  mathematical content.
- Therefore the TM-verifier work is reusable but not a closure path.
  Continuing it is justified, but only with explicit framing as
  reusable NP-side infrastructure, not as progress toward an
  unconditional `NP ⊄ P/poly`.

The previous TM-verifier framing — "Phase A is the entry point of a
plan that closes through `i4_final_wiring_of_formulaCertificate`" —
is dead.  The new framing is:

- The TM verifier discharges `AsymptoticNPPullback` (canonical track).
- `AsymptoticIsoStrongRoute` or `AsymptoticPromiseYesCertificateRoute`
  is the separately-required structural payload.
- Closure of `NP_not_subset_PpolyDAG` requires BOTH halves.

Recommendation tag: **`continue_only_as_reusable_NP_infrastructure`**.

`continue_full_speed` would be misleading, because the 7-session plan
was scoped against a refuted final wiring.  `stop_all_TMVerifier_sessions`
would discard work that is still useful for the NP-side half.
`continue_if_retarget_found` is satisfied by this report's verdict,
but section 8's next action ties the continuation explicitly to a
follow-up audit, not to immediate full-speed resumption.

## 8. Next action

**`open_existing_route_audit_D0`.**

Rationale.  The D0 verdict here is **retarget feasibility** based on:

- structural inspection of the `AsymptoticIsoStrongRoute` and
  `AsymptoticPromiseYesCertificateRoute` Props,
- absence of `false_of_…` theorems in the repo for either route,
- non-applicability of the hardwiring NoGo family (section 6).

That is a *negative-evidence* verdict.  Before resuming the
TM-verifier sessions under the new framing of section 7, an
independent D0 audit should formally establish:

1. Whether `∀ n β, InPpolyDAG (gapPartialMCSP_Language
   ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf
   n β))` is provable in-repo at the canonical spec (section 6.6,
   probe 1).  If yes, the retarget's `hInDag` is dischargeable
   internally and the route may be vacuously satisfied through its
   hypothesis surface.
2. Whether an asymptotic `ttFormula`-DAG-twin attack exists (section
   6.6, probe 2).
3. Whether `IsoStrongFamilyEventually` admits a syntactic-DAG
   tautological-rewrite analogue (section 6.6, probe 3).
4. The exact non-vacuity status of
   `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic
   canonicalAsymptoticHAsym) hInDag` and
   `PromiseYesSubcubeCertificateAt W` at canonical params.

That audit is a markdown-only D0.  Only if it returns
GREEN-light should TM-verifier sessions resume.

Suggested seed pack name for the follow-up:
`seed_packs/asymptotic_isostrong_route_audit_D0/`.

Recommendation tag: **`open_existing_route_audit_D0`**.

`merge_only_documentation_and_stop` is too conservative: a usable
retarget exists.  `resume_TMVerifier_with_new_consumer` is too
aggressive: the retarget's non-vacuity has not been formally audited
yet.  `close_canonical_route` would discard reusable infrastructure.
`open_new_provider_D0` is reserved for the case where no existing
consumer is usable, which is not the situation here.

## 9. Audit trail summary

- D0 verdict: `RETARGET_EXISTING_ROUTE`.
- TMVerifier verdict: `continue_only_as_reusable_NP_infrastructure`.
- Next action: `open_existing_route_audit_D0`.
- Forbidden scope: no Lean code, no source/spec/JSONL/known_guards edits,
  no trust-root edits, no `ResearchGapWitness`, no
  `VerifiedNPDAGLowerBoundSource`, no `SourceTheorem`, no `gap_from`, no
  endpoint, no `P ≠ NP` claim.  All preserved.
- Scope violations: none.
