# D0 asymptotic route audit — AsymptoticIsoStrongRoute / PromiseYes route

Task: `asymptotic_isostrong_route_audit_D0`  
Handle: `gpt55`  
Branch observed: `work` (user prompt requested `main`; repository checkout was already on `work`)  
Commit before: `1e0454f92b126815b095952e6135b43fce894f6f`  
Scope: Markdown-only audit report. No Lean code, JSONL, NoGoLog, spec, guard, endpoint, or source-theorem edits.

## Required-reading status

Read directly:

- `RESEARCH_CONSTITUTION.md`.
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`.
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`.
- `pnp3/Tests/CanonicalIntegrationTests.lean`.
- `pnp3/Magnification/FinalResultMainline.lean`.
- `pnp3/Magnification/FinalResultWeakRoutes.lean`.
- `pnp3/Tests/WeakRouteSurfaceTests.lean`.
- `outputs/nogolog.jsonl`.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- `pnp3/RefutedPredicates/Registry.lean`.

Missing from checkout:

- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md` was requested but is not present in this checkout. I searched under `seed_packs` and the repository for `D0_provider_retarget_opus47.md`; no match was found. The audit therefore uses the in-repo PR13 formal refutation context in `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` and related registry/audit-route files.

---

## 1. Executive verdict

**YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS**

Rationale:

- The route is not currently shown vacuous or refuted: its endpoint hypotheses are explicit route assumptions, not provider typeclasses or refuted `MagnificationAssumptions`/support-bounds packages.
- The suspicious part is the universal `hInDag` premise. I did not find an in-repo theorem proving the relevant canonical gap-partial-MCSP slice language is in `P`, and fixed-slice truth-table hardwiring does not automatically yield asymptotic `PpolyDAG` because the hardwired table is polynomial only in a fixed input length and may be exponential over the slice family.
- However, the route is still close to the main lower-bound gap: assuming every hypothetical small-DAG family yields an eventual isolation/YES-subcube certificate is essentially a lower-bound source obligation. It should remain open only with targeted hInDag and hardwiring-twin probes.

---

## 2. Exact route definitions

### 2.1 `AsymptoticIsoStrongRoute`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, definition at lines 218–227.
- **Theorem/name:** `def AsymptoticIsoStrongRoute`.
- **Definition summary:** For a fixed `hAsym : AsymptoticFormulaTrackHypothesis`, the route says that for every slice-wise DAG-inclusion hypothesis
  `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))`,
  one can produce `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic hAsym) hInDag`.
- **Full dependency surface from the definition:**
  - `AsymptoticFormulaTrackHypothesis`.
  - `eventualGapSliceFamily_of_asymptotic hAsym`.
  - `ComplexityInterfaces.InPpolyDAG`.
  - `gapPartialMCSP_Language`.
  - `IsoStrongFamilyEventually`.
  - The imported files of `FinalResultMainline.lean`: `Magnification.Bridge_to_Magnification_Partial`, `Magnification.AsymptoticFormulaCollapse`, `Magnification.Facts_Magnification_Partial`, `Magnification.LocalityProvider_Partial`, `Magnification.PipelineStatements_Partial`, `LowerBounds.DAGStableRestrictionProducer`, `LowerBounds.RouteBSourceClosure`, `LowerBounds.AsymptoticDAGBarrier`, `LowerBounds.SingletonDensityContradiction`, `Models.Model_PartialMCSP`, `Complexity.Interfaces`, `Complexity.PpolyFormula_from_PpolyDAG_FixedSlice`, `Complexity.PsubsetPpolyDAG_Internal`, and `Complexity.Simulation.Circuit_Compiler`.
- **Imports `FormulaCertificateProviderPartial`?** Not directly in the statement. The file imports `Magnification.LocalityProvider_Partial`, where the old formula-provider universe lives, but the route statement itself does **not** mention `FormulaCertificateProviderPartial` and its endpoint comments explicitly avoid legacy/refuted support-bounds wiring.

### 2.2 `AsymptoticPromiseYesCertificateRoute`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, definition at lines 238–256.
- **Theorem/name:** `def AsymptoticPromiseYesCertificateRoute`.
- **Definition summary:** For every `hInDag` of the same slice-wise `InPpolyDAG` shape, there must exist `β0 > 0` and thresholds `nCert : Rat → Nat` such that for all sufficiently large canonical slices and all sufficiently small positive `β`, every `SmallDAGWitnessOnSlice` at epsilon `1` has a nonempty `PromiseYesSubcubeCertificateAt W`.
- **Full dependency surface from the definition:**
  - Everything listed for `AsymptoticIsoStrongRoute`, plus:
  - `ppolyDAGSizeBoundOnSlicesEventually`.
  - `SmallDAGWitnessOnSlice`.
  - `PromiseYesSubcubeCertificateAt`.
  - `Nonempty` witness packaging.
- **Imports `FormulaCertificateProviderPartial`?** Not in the statement. Same caveat: `FinalResultMainline.lean` imports older partial/provider modules transitively, but this route surface does not quantify over or consume `FormulaCertificateProviderPartial`.

### 2.3 `AsymptoticPromiseYesWeakRouteEventually`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, definition at lines 265–282.
- **Theorem/name:** `def AsymptoticPromiseYesWeakRouteEventually`.
- **Definition summary:** For every slice-wise `hInDag`, there exist `ε > 0` and `β0 > 0` such that for every sufficiently small positive `β` there is an eventual threshold `n0 ≥ F.N0`; beyond that threshold, `SmallDAGImpliesPromiseYesSubcubeAtEventually` holds for the asymptotic family and the `ppolyDAGSizeBoundOnSlicesEventually` size predicate derived from `hInDag`.
- **Full dependency surface from the definition:**
  - `AsymptoticFormulaTrackHypothesis`.
  - `eventualGapSliceFamily_of_asymptotic hAsym`.
  - `ComplexityInterfaces.InPpolyDAG`.
  - `gapPartialMCSP_Language`.
  - `ppolyDAGSizeBoundOnSlicesEventually`.
  - `SmallDAGImpliesPromiseYesSubcubeAtEventually`.
- **Imports `FormulaCertificateProviderPartial`?** Not in the statement. No direct route dependency on `FormulaCertificateProviderPartial` was found.

### 2.4 `IsoStrongFamilyEventually`

- **File / line:** `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`, definition at lines 1078–1104.
- **Theorem/name:** `def IsoStrongFamilyEventually`.
- **Definition summary:** For a `GapSliceFamilyEventually` and a slice-wise `hInDag`, the source must provide:
  - `β0 > 0`,
  - a coordinate-budget function `κ : Nat → Rat → Nat`,
  - a threshold function `nIso : Rat → Nat`,
  - such that every sufficiently large/small-β small DAG `C` that is correct on the promise has a valid YES center `yYes` and a value-coordinate set `D` with `D.card ≤ κ n β`; every valid encoding agreeing with `yYes` on `D` is forced into the YES side;
  - and the same `κ` satisfies the counting slack `F.Mof n (F.Tof n β) < 2 ^ (tableLen - κ n β)`.
- **Full dependency surface from the definition:**
  - `GapSliceFamilyEventually`.
  - `ComplexityInterfaces.InPpolyDAG`.
  - `gapPartialMCSP_Language`.
  - `ppolyDAGSizeBoundOnSlicesEventually`.
  - `DagCircuit`, `DagCircuit.size`.
  - `CorrectOnPromiseSlice`.
  - `gapSliceOfParams`, `ValidEncoding`, `AgreeOnValues`.
  - `Finset (Fin tableLen)`, `F.Mof`, `F.Tof`.
  - File import chain starts at `LowerBounds.AsymptoticDAGBarrierInterfaces`; no formula-provider route is needed by the statement.
- **Imports `FormulaCertificateProviderPartial`?** No direct import or statement dependency found.

### 2.5 `PromiseYesSubcubeCertificateAt`

- **File / line:** `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`, structure at lines 2480–2504.
- **Theorem/name:** `structure PromiseYesSubcubeCertificateAt`.
- **Definition summary:** For a fixed `W : SmallDAGWitnessOnSlice p SizeBound ε`, the certificate contains:
  - a concrete valid YES center `yYes`,
  - proof `hYes : yYes ∈ (GapPartialMCSPPromise p).Yes`,
  - proof `hValidYes : ValidEncoding p yYes`,
  - a semantic value-coordinate set `S`,
  - direct counting slack `circuitCountBound p.n (p.sNO - 1) < 2 ^ (tableLen p.n - S.card)`,
  - and one-sided promise acceptance: all valid promise-relevant completions agreeing with `yYes` on `S` are accepted by `W.C`.
- **Full dependency surface from the definition:**
  - `GapPartialMCSPParams`.
  - `SmallDAGWitnessOnSlice`.
  - `GapPartialMCSPPromise`.
  - `ValidEncoding`.
  - `ValueCoordinateSet`.
  - `circuitCountBound`, `Partial.tableLen`.
  - `AgreeOnValues`.
  - `DagCircuit.eval W.C`.
  - File imports: `Mathlib.Data.Fintype.EquivFin`, `Complexity.Promise`, `Counting.Count_EasyFuncs`, `LowerBounds.AcceptedFamilyBarrier`, `LowerBounds.SingletonDensityContradiction`, `LowerBounds.AsymptoticDAGBarrier`, `ThirdPartyFacts.PartialLocalityLift`.
- **Imports `FormulaCertificateProviderPartial`?** No direct import or statement dependency found. The file imports `SingletonDensityContradiction`, which contains some formula-certificate refutation context elsewhere, but this structure itself is DAG-witness/certificate-native.

---

## 3. Endpoint wiring

### 3.1 `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1057–1065.
- **Type:** `AntiCheckerAssumptions → AsymptoticIsoStrongRoute anti.asymptotic → NP_not_subset_PpolyDAG`.
- **Wiring:** Thin wrapper around `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute`, supplying `anti.asymptotic` and `anti.npBridge`.
- **Classification:** `conditional`, `canonical candidate route`.
- **Reason:** It needs an explicit `AntiCheckerAssumptions` package and a route proof. It is not zero-argument and not a closed P-vs-NP claim.

### 3.2 `P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1071–1077.
- **Type:** `AntiCheckerAssumptions → AsymptoticIsoStrongRoute anti.asymptotic → P_ne_NP`.
- **Wiring:** Applies `P_ne_NP_final_dag_only` to the DAG separation endpoint above.
- **Classification:** `conditional`, `canonical candidate route`.
- **Reason:** Conditional companion endpoint only. It is acceptable as a conditional integration surface but must not be advertised as unconditional progress without the route source and anti-checker package.

### 3.3 `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1098–1106.
- **Type:** `AntiCheckerAssumptions → AsymptoticPromiseYesCertificateRoute anti.asymptotic → NP_not_subset_PpolyDAG`.
- **Wiring:** Calls `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute`, which first converts the promise-YES route into `AsymptoticIsoStrongRoute` via `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
- **Classification:** `conditional`, `canonical candidate route`, with `suspicious` audit marker until promise-YES non-vacuity is probed.
- **Reason:** It is cleaner than the refuted formula-provider channel, but the route hypothesis is strong and witness-indexed.

### 3.4 `P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File / line:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1112–1118.
- **Type:** `AntiCheckerAssumptions → AsymptoticPromiseYesCertificateRoute anti.asymptotic → P_ne_NP`.
- **Wiring:** Applies `P_ne_NP_final_dag_only` to the promise-YES DAG-separation wrapper.
- **Classification:** `conditional`, `canonical candidate route`, with `suspicious` audit marker until promise-YES non-vacuity is probed.
- **Reason:** Same as above; conditional endpoint only, not refuted by PR13 as currently stated.

---

## 4. `hInDag` triviality audit

**Critical question:** Can the route's assumption

```lean
hInDag : ∀ n β, InPpolyDAG (...)
```

or its equivalent be proved in-repo from existing facts?

### 4.1 `P_subset_PpolyDAG_internal`

- The repository has a no-arg inclusion theorem `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG` in `pnp3/Complexity/Simulation/Circuit_Compiler.lean` lines 599–608.
- This theorem can prove `InPpolyDAG L` only after a proof that the relevant language `L` is in `P`.
- I did not find a theorem proving `gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)` is in `P` for every `n β`.

### 4.2 Any theorem proving `gapPartialMCSP_Language` in `P`

- Search found fixed-slice truth-table formula hardwiring for `PpolyFormula`, not a polynomial-time decider theorem for `gapPartialMCSP_Language p`.
- `gapPartialMCSP_Language` is noncomputable and slice-shaped: it returns false off the exact `partialInputLen p` and otherwise decodes the partial table and checks the YES predicate. The definition is at `pnp3/Models/Model_PartialMCSP.lean` lines 641–654.
- The canonical decider module proves a decidable/spec-aligned decision procedure for the canonical `sYES = 1` asymptotic language, not a general theorem that every canonical gap-partial-MCSP slice family is in `P` or `InPpolyDAG`.

### 4.3 Truth-table hardwiring witnesses

- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` defines `ttFormula` and proves `ttFormula_eval`; it also proves `fixedSlice_gapPartialMCSP_in_PpolyFormula (p)` by hardwiring exactly one input length and using a constant false circuit elsewhere.
- That proof is formula-side and fixed-slice. It does not directly provide a DAG-family witness of polynomial size across the asymptotic family.

### 4.4 Fixed-slice vs asymptotic family mismatch

- The fixed-slice hardwired formula can choose one enormous circuit for one fixed `partialInputLen p`; its polynomial bound can hide that fixed constant.
- The route's `hInDag` is uniform over all slice indices `n` and all `β` for the varying family `paramsOf n β`.
- Hardwiring the full truth table of the language at canonical input length `N = 2 * 2^m` would require size on the order of `2^N` in the obvious representation, which is not polynomial in `N`. The fixed-slice trick does not scale to a single asymptotic `PpolyDAG` family unless additional structure is exploited.

### 4.5 Parser / canonical infrastructure

- `CanonicalAsymptoticDecider.lean` contains executable canonical-slice discovery (`findCanonicalSlice`) and a decision procedure for the canonical `sYES = 1` asymptotic language; e.g. `findCanonicalSlice` is at lines 127–134, and `decideAsymptotic` is tied to `Partial.inputLen`/`decodePartial` around lines 195–207.
- This infrastructure supports the NP/verifier/canonical-route plumbing, but I did not find it proving the full canonical gap language is in `P`, nor producing a `PpolyDAG` witness for `hInDag`.

**Verdict:** **hInDag_not_trivial**

This is an audit verdict, not a formal impossibility theorem. A Lean probe should still check the exact canonical instantiation because `sYES = 1` is unusually simple.

---

## 5. Hardwiring twin audit

**Question:** Can one build an asymptotic `InPpolyDAG` witness for the canonical gap-partial-MCSP language using truth-table/table-hardwiring, analogously to NOGO-000006?

### Analysis

- NOGO-000006 is formula-side/log-width: arbitrary all-essential payloads are hardwired by `ttFormula` on a logarithmic-width window and then renamed into the ambient variables. Since `2^log n` is polynomial in the ambient width, that attack remains polynomial-size.
- For the canonical gap-partial-MCSP slice, the input length is `N = Partial.inputLen m = 2 * 2^m`. A naive truth-table hardwire of a Boolean language over `N` input bits has size exponential in `N`, not polynomial in `N`.
- The fixed-slice `PpolyFormula` proof avoids this by freezing one slice; the polynomial bound absorbs the fixed circuit size. The asymptotic route does not freeze a single slice.
- A subtler hardwiring twin could exploit the canonical `sYES = 1` structure. The canonical decider comments say the YES predicate at `sYES = 1` can be checked by size-1 candidate enumeration, suggesting a small algorithm may exist for YES recognition. But this is not the same as truth-table hardwiring and must be proved through parser/decider-to-DAG infrastructure if used.

**Verdict:** **hardwiring_does_not_transfer**

Meaning: the known NOGO-000006 truth-table payload mechanism does not directly transfer to an asymptotic `PpolyDAG` witness because of the input-length exponent. This does **not** rule out a different `sYES = 1` algorithmic triviality attack; that belongs to an `hInDag`/canonical-decider Lean probe.

---

## 6. IsoStrong route audit

### What `IsoStrongFamilyEventually` demands

It demands a uniform eventual isolation package: for every sufficiently large canonical slice and every small enough positive `β`, any small DAG solver that is correct on the promise must expose a YES center and a small semantic coordinate set `D`; agreement with that center on `D` forces valid encodings into YES, and the same coordinate budget satisfies the counting inequality.

### Could it be trivially true?

Unclear but not obviously. It quantifies over all small correct-on-promise DAGs derived under `hInDag`. A trivial proof would need to choose a small enough coordinate set and prove the semantic forcing and counting slack. Taking `D` as all value coordinates makes forcing easy but destroys slack. Taking `D` empty or small gives slack but not forcing. The definition deliberately couples the semantic and numeric halves.

### Could it be impossible?

Possibly, if canonical `sYES = 1` creates too few/too rigid YES centers or if there are small DAG solvers whose accepted region does not align with a small YES-forcing subcube. I found no in-repo contradiction proving impossibility.

### Does it require new lower-bound content?

Yes. It is effectively a family-specific small-DAG-to-isolation theorem. The endpoint comments call it the remaining mathematical debt for the non-vacuous eventual DAG route.

### Is it close to the original main gap?

Yes. The route transforms hypothetical slice-wise `InPpolyDAG` witnesses into an isolation/counting contradiction at canonical lengths. Proving it appears comparable to proving a real lower-bound transfer, not mere API plumbing.

**Verdict:** **likely_as_hard_as_main_gap**

---

## 7. PromiseYes route audit

### What `PromiseYesSubcubeCertificateAt W` demands

For a concrete small-DAG witness `W`, it demands a valid YES center, a semantic value-coordinate set `S`, a direct counting slack inequality, and acceptance by `W.C` on every valid promise-relevant completion agreeing with the YES center on `S`.

### Does canonical `sYES = 1` make it trivial or impossible?

- It may make YES membership more explicit: the canonical track sets `sYES n = 1` and `sNO n = 2` in `canonicalAsymptoticSpec` and per-slice params.
- It does not by itself make `PromiseYesSubcubeCertificateAt W` trivial because the certificate is tied to the behavior of an arbitrary small DAG witness `W` and must prove one-sided acceptance over an entire agreement subcube.
- It also does not look obviously impossible from the definitions: a correct-on-promise solver must accept YES inputs, but the subcube assertion extends acceptance to all valid promise-relevant completions agreeing on `S`; selecting `S` with enough slack is the hard part.

### Does it require selecting subcubes with nontrivial density/provenance?

Yes. The route requires choosing `S` so that both semantic acceptance and the counting slack hold. Existing split helpers (`PromiseYesAcceptanceInvariantAt`, slack/budget compilers, Q1/Q2 split providers) show the API expects separate semantic and numeric provenance, not a free witness.

### Can it be attacked by hardwiring?

The fixed-slice formula hardwiring attacks do not directly refute this DAG witness-indexed certificate route. A possible analogue would be a small DAG witness whose accepted set is adversarially shaped to defeat all small `S`, but producing such a witness under the route's size/correctness constraints is a new targeted self-attack, not currently in the NoGoLog.

**Verdict:** **promising_nontrivial**

This means promising as a non-vacuous audit target, not as established mathematical progress.

---

## 8. NoGo cross-check

### PR13 `FormulaCertificateProviderPartial` refutation

- **Status:** **does not apply directly**.
- **Reason:** PR13 proves `FormulaCertificateProviderPartial` is inconsistent by combining fixed-slice truth-table formula hardwiring with the existing gap-target payload contradiction. The asymptotic IsoStrong/PromiseYes routes do not quantify over `FormulaCertificateProviderPartial`.
- **Possible analogue:** If a future bridge reconstructs a universal formula-certificate provider or a refuted support-bounds payload from these route assumptions, the route would become audit-only/refuted.

### NOGO-000004 prefixAnd

- **Status:** **possible analogue**.
- **Reason:** NOGO-000004 shows a support-cardinality filter can admit log-width prefix-AND hardwiring. The current routes are not support-cardinality filters, but any proposed proof of `IsoStrongFamilyEventually` via support-size/provenance-only criteria should be checked against this pattern.

### NOGO-000006 arbitrary ttFormula payload

- **Status:** **possible analogue; hardwiring does not directly transfer**.
- **Reason:** NOGO-000006 is the strongest warning against support-only filters. However, its polynomiality relies on log-width payloads; a full canonical slice has input length `N = 2 * 2^m`, so naive truth-table hardwiring is exponential in `N`.

### NOGO-000008 syntax rewrite

- **Status:** **possible analogue**.
- **Reason:** If the route proof tries to exclude hardwiring by displayed syntax/gate-shape/provenance, tautological rewrite attacks may reappear. No direct statement in the current route depends on syntax-only filtering.

### NOGO-000009 normalisation meta-barrier

- **Status:** **possible analogue**.
- **Reason:** If a future self-attack or proof patch relies on structural normalisation of syntactic filters, NOGO-000009 warns that normalisation can collapse the route's own non-vacuity witnesses. It does not directly refute the DAG/certificate statements.

### Support-bounds refutations

- **Status:** **does not apply directly**.
- **Reason:** Support-bounds refutations target formula-side support-bounds and provider-backed compatibility routes. `FinalResultAuditRoutes.lean` marks those as legacy/audit/refuted; the current anti-checker routes are deliberately outside that package.
- **Possible analogue:** Any bridge from PromiseYes/IsoStrong back to the refuted formula support-bounds claims would refute the route.

### `MagnificationAssumptions` refutations

- **Status:** **does not apply directly**.
- **Reason:** `false_of_MagnificationAssumptions` and `false_of_MagnificationAssumptions_fromPipeline` target old switching/support-bounds packages. The audited endpoints consume `AntiCheckerAssumptions` plus route hypotheses, not `MagnificationAssumptions`.

---

## 9. Should TMVerifier sessions resume?

**yes_resume_as_np_infrastructure**

Rationale: TMVerifier work supplies the canonical NP pullback/anti-checker infrastructure. It does not by itself close the lower-bound route, but it is useful infrastructure and not invalidated by this audit. It should be reported as NP infrastructure only, not as lower-bound progress.

---

## 10. Recommended next action

**open_hInDag_triviality_probe**

Rationale: Before spending effort proving IsoStrong/PromiseYes source statements, the route should be stress-tested at the exact canonical instantiation: can `hInDag` be derived from the canonical `sYES = 1` decider plus `proved_P_subset_PpolyDAG_internal`, or from a DAG hardwiring construction? A positive result would make the route much more suspicious; a negative/failure report would sharpen the non-vacuity case.

---

## 11. What would count as progress?

Concrete next theorem/report that would change route status:

1. **Route becomes RED:** a Lean theorem or structured failure report showing that the canonical route assumption `hInDag` is derivable in-repo, for example by proving the relevant canonical family language is in `P` and applying `Complexity.Simulation.proved_P_subset_PpolyDAG_internal`, or by constructing a polynomial-size DAG family for the canonical slices directly.
2. **Route becomes GREEN/YELLOW-stronger:** a Lean probe demonstrating that known fixed-slice truth-table hardwiring cannot inhabit the asymptotic `hInDag` shape, plus a self-attack report failing to construct a small DAG adversarial witness against `PromiseYesSubcubeCertificateAt W` under the route's size/correctness hypotheses.
3. **PromiseYes route specifically progresses:** a theorem at the canonical instantiation proving a Q1 semantic invariant (`PromiseYesAcceptanceInvariantAt W`) and a matching Q2 slack/budget theorem for every sufficiently large `W`, without importing `FormulaCertificateProviderPartial`, support-bounds refuted routes, `MagnificationAssumptions`, or NoGo audit artifacts.
4. **IsoStrong route specifically progresses:** a theorem proving `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym) hInDag` from a clearly non-refuted, DAG-native source obligation weaker than the final lower-bound endpoint.

---

## Commands run

Required searches:

```bash
rg -n "AsymptoticIsoStrongRoute|IsoStrongFamilyEventually|PromiseYesSubcubeCertificateAt|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually" pnp3
```

```bash
rg -n "FormulaCertificateProviderPartial|RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions" pnp3/Magnification pnp3/LowerBounds pnp3/Tests
```

Additional audit commands:

```bash
find .. -name AGENTS.md -print
cat AGENTS.md
git status --short
git rev-parse HEAD
git branch --show-current
find seed_packs -path '*post_pr13*' -type f -maxdepth 5 -print
find . -path '*D0_provider_retarget_opus47.md' -print
sed -n '1,220p' RESEARCH_CONSTITUTION.md
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '200,430p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '1000,1120p'
nl -ba pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean | sed -n '1070,1128p'
nl -ba pnp3/LowerBounds/DAGStableRestrictionProducer.lean | sed -n '2470,2510p'
rg -n "canonicalAsymptoticHAsym|canonicalAntiCheckerAssumptions|canonicalSliceEq|sYES|sNO|GapPartialMCSP_Asymptotic_TMWitness|gapPartialMCSP_Asymptotic_in_NP" pnp3/Magnification/CanonicalAsymptoticTrackData.lean pnp3/Magnification/CanonicalAsymptoticDecider.lean pnp3/Tests/CanonicalIntegrationTests.lean pnp3/Magnification/FinalResultWeakRoutes.lean pnp3/Tests/WeakRouteSurfaceTests.lean
nl -ba outputs/nogolog.jsonl | rg "NOGO-000004|NOGO-000006|NOGO-000008|NOGO-000009|support-bounds|FormulaCertificateProviderPartial|MagnificationAssumptions"
python3 - <<'PY'
import json
for i,line in enumerate(open('outputs/nogolog.jsonl'),1):
    obj=json.loads(line)
    if obj.get('id') in {'NOGO-000006','NOGO-000008'}:
        print('LINE',i,'ID',obj['id'])
        for k in ['candidate_id','failure_class','formal_witness','structural_pattern','why_generalizes','notes']:
            print(k+':', obj.get(k,''))
        print()
PY
rg -n "P_subset_PpolyDAG_internal|gapPartialMCSP_Language.*InP|InPpolyDAG.*gapPartialMCSP_Language|gapPartialMCSP.*P\\b|ttFormula|truth.*table|hardwire" pnp3/Complexity pnp3/Models pnp3/Magnification pnp3/LowerBounds pnp3/Tests
rg -n "proved_P_subset_PpolyDAG_internal|P_subset_PpolyDAG_internal|P_subset_PpolyDAG" pnp3
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '1,25p;550,620p'
rg -n "parser|Parser|parse|decode|encoding|Encoding|Partial.inputLen|inputLen" pnp3/Models pnp3/Complexity pnp3/Magnification/CanonicalAsymptoticDecider.lean
```

Required check:

```bash
./scripts/check.sh
```

---

## Scope violations

none
