# D0 asymptotic route audit — GPT-5.5

Task: `asymptotic_isostrong_route_audit_D0`  
Handle: `gpt55`  
Branch observed: `work` (worker prompt requested `main`; no checkout was performed)  
Commit before: `1e0454f92b126815b095952e6135b43fce894f6f`

## 0. Reading status and scope

### Required reading completed

- `RESEARCH_CONSTITUTION.md`
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
- `pnp3/Tests/CanonicalIntegrationTests.lean`
- `pnp3/Magnification/FinalResultMainline.lean`
- `pnp3/Magnification/FinalResultWeakRoutes.lean`
- `pnp3/Tests/WeakRouteSurfaceTests.lean`
- `outputs/nogolog.jsonl`
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
- `pnp3/RefutedPredicates/Registry.lean`

### Required reading missing from checkout

The requested post-PR13 report path was not present in this checkout:

- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`

I searched under `seed_packs` for matching `D0_provider_retarget` / `post_pr13` paths and found no file. This report therefore treats the in-repo Lean refutation registry and Probe 13 as the authoritative post-PR13 context.

### Scope classification

This is **Infrastructure / audit-only** work. It does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, does not create a `ResearchGapWitness`, does not add a `SourceTheorem`, and does not claim an endpoint.

## 1. Executive verdict

**YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS**

Reason: the asymptotic route is not obviously refuted by the PR13 `FormulaCertificateProviderPartial` failure, because the anti-checker endpoints avoid the legacy `MagnificationAssumptions` / support-bounds route and consume DAG-side `InPpolyDAG` hypotheses. It is also not green: the source obligations (`IsoStrongFamilyEventually` and `PromiseYesSubcubeCertificateAt` uniformly over all hypothetical slice DAG witnesses) are extremely strong and sit close to the main lower-bound gap. A targeted Lean probe should first test whether the `hInDag` family can be manufactured from existing parser/decider infrastructure or from a table-hardwiring analogue.

## 2. Exact route definitions

### 2.1 `AsymptoticIsoStrongRoute`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Definition name / lines: `def AsymptoticIsoStrongRoute`, lines 218--227.
- Summary of exact shape:
  - Input: `hAsym : AsymptoticFormulaTrackHypothesis`.
  - Quantifies over every slice-indexed DAG-membership family
    `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))`.
  - Requires `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic hAsym) hInDag`.
- Full dependency surface in the statement:
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `GapSliceFamilyEventually.paramsOf`
  - `ComplexityInterfaces.InPpolyDAG`
  - `Models.gapPartialMCSP_Language`
  - `IsoStrongFamilyEventually`
- Does it import `FormulaCertificateProviderPartial`?
  - The definition itself does **not** mention `FormulaCertificateProviderPartial`.
  - The file imports `Magnification.LocalityProvider_Partial`, which defines/exports formula-provider infrastructure, so there is transitive ambient availability. However, this route definition's statement surface is DAG/anti-checker shaped, not provider-shaped.

### 2.2 `AsymptoticPromiseYesCertificateRoute`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Definition name / lines: `def AsymptoticPromiseYesCertificateRoute`, lines 238--256.
- Summary of exact shape:
  - Input: `hAsym : AsymptoticFormulaTrackHypothesis`.
  - Quantifies over every same `hInDag : ∀ n β, InPpolyDAG (...)` family.
  - Requires existence of `β0 > 0` and `nCert : Rat → Nat` such that for all sufficiently large `n` and small positive `β`, every `SmallDAGWitnessOnSlice` at ε = 1 has `Nonempty (PromiseYesSubcubeCertificateAt W)`.
- Full dependency surface in the statement:
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `ComplexityInterfaces.InPpolyDAG`
  - `gapPartialMCSP_Language`
  - `SmallDAGWitnessOnSlice`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `PromiseYesSubcubeCertificateAt`
  - rational cutoffs `β0`, `nCert`
- Does it import `FormulaCertificateProviderPartial`?
  - The statement does **not** mention it.
  - Same file-level caveat: `FinalResultMainline.lean` imports `Magnification.LocalityProvider_Partial`, but the route's formal dependency surface is not the PR13 provider.

### 2.3 `AsymptoticPromiseYesWeakRouteEventually`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Definition name / lines: `def AsymptoticPromiseYesWeakRouteEventually`, lines 265--282.
- Summary of exact shape:
  - Input: `hAsym : AsymptoticFormulaTrackHypothesis`.
  - Quantifies over every same `hInDag` family.
  - Requires existence of `ε > 0`, `β0 > 0`, and for each small positive `β` a threshold `n0 ≥ F.N0`, after which `SmallDAGImpliesPromiseYesSubcubeAtEventually F (ppolyDAGSizeBoundOnSlicesEventually F hInDag) n β ε` holds.
- Full dependency surface in the statement:
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `ComplexityInterfaces.InPpolyDAG`
  - `gapPartialMCSP_Language`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `SmallDAGImpliesPromiseYesSubcubeAtEventually`
- Does it import `FormulaCertificateProviderPartial`?
  - Not in the statement. Same ambient import caveat as above.

### 2.4 `IsoStrongFamilyEventually`

- File: `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
- Definition name / lines: `def IsoStrongFamilyEventually`, lines 1078--1104.
- Summary of exact shape:
  - Inputs: `F : GapSliceFamilyEventually` and `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))`.
  - Requires `β0 > 0`, a coordinate budget `κ : Nat → Rat → Nat`, and threshold `nIso : Rat → Nat`.
  - For all sufficiently large `n` and small positive `β`, every small DAG `C` that is correct on the promise slice must admit a valid YES center `yYes` and coordinate set `D` with `D.card ≤ κ n β` such that every valid completion agreeing with `yYes` on `D` is in the YES side.
  - Also requires counting slack `F.Mof n (F.Tof n β) < 2 ^ (tableLen - κ n β)`.
- Full dependency surface in the statement:
  - `GapSliceFamilyEventually`
  - `ComplexityInterfaces.InPpolyDAG`
  - `gapPartialMCSP_Language`
  - `DagCircuit`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `CorrectOnPromiseSlice`
  - `gapSliceOfParams`
  - `ValidEncoding`
  - `AgreeOnValues`
  - `Finset (Fin tableLen)` coordinate sets
  - family numerics `Mof`, `Tof`, `tableLen`
- Does it import `FormulaCertificateProviderPartial`?
  - No direct import. The file imports only `LowerBounds.AsymptoticDAGBarrierInterfaces`; the statement is DAG-native.

### 2.5 `PromiseYesSubcubeCertificateAt`

- File: `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- Structure name / lines: `structure PromiseYesSubcubeCertificateAt`, lines 2480--2503.
- Summary of exact shape:
  - Input: a witness `W : SmallDAGWitnessOnSlice p SizeBound ε`.
  - Provides a concrete valid YES center `yYes`.
  - Provides semantic value coordinates `S : ValueCoordinateSet p`.
  - Provides slack `circuitCountBound p.n (p.sNO - 1) < 2 ^ (Partial.tableLen p.n - S.card)`.
  - Provides one-sided promise acceptance: every valid YES/NO completion agreeing with `yYes` on `S` is accepted by `W.C`.
- Full dependency surface in the statement:
  - `GapPartialMCSPParams`
  - `SmallDAGWitnessOnSlice`
  - `GapPartialMCSPPromise.Yes/No`
  - `ValidEncoding`
  - `ValueCoordinateSet`
  - `AgreeOnValues`
  - `Models.circuitCountBound`
  - `Models.Partial.tableLen`
  - `DagCircuit.eval W.C`
- Does it import `FormulaCertificateProviderPartial`?
  - No direct dependency in this structure. The file imports `LowerBounds.SingletonDensityContradiction` and `ThirdPartyFacts.PartialLocalityLift`, and later sections contain compatibility with formula/support-bounds routes, but this structure is itself DAG/witness-native.

## 3. Endpoint wiring

### 3.1 `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Lines: 1057--1065.
- Shape: `(anti : AntiCheckerAssumptions) → AsymptoticIsoStrongRoute anti.asymptotic → NP_not_subset_PpolyDAG`.
- Wiring: unwraps `anti.asymptotic` and `anti.npBridge`, then calls `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute`.
- Classification: **conditional; canonical candidate route**.
- Audit note: not directly refuted by PR13 because the theorem comment explicitly says it avoids legacy `MagnificationAssumptions` and does not require the refuted formula-side support-bounds surface.

### 3.2 `P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Lines: 1071--1077.
- Shape: `(anti : AntiCheckerAssumptions) → AsymptoticIsoStrongRoute anti.asymptotic → P_ne_NP`.
- Wiring: applies `P_ne_NP_final_dag_only` to the previous DAG separation theorem.
- Classification: **conditional; canonical candidate route; audit-sensitive**.
- Audit note: the result is not an unconditional claim because it still has explicit `anti` and `hIso` arguments.

### 3.3 `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Lines: 1098--1106.
- Shape: `(anti : AntiCheckerAssumptions) → AsymptoticPromiseYesCertificateRoute anti.asymptotic → NP_not_subset_PpolyDAG`.
- Wiring: calls `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute`, which itself routes through `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute` and then the iso-strong endpoint.
- Classification: **conditional; canonical candidate route; suspicious until the certificate obligation is self-attacked**.

### 3.4 `P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- File: `pnp3/Magnification/FinalResultMainline.lean`
- Lines: 1112--1118.
- Shape: `(anti : AntiCheckerAssumptions) → AsymptoticPromiseYesCertificateRoute anti.asymptotic → P_ne_NP`.
- Wiring: applies `P_ne_NP_final_dag_only` to the promise-YES DAG endpoint.
- Classification: **conditional; canonical candidate route; audit-sensitive**.

### 3.5 Canonical test wiring

`pnp3/Tests/CanonicalIntegrationTests.lean` confirms that, after a `GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`, the canonical iso-strong and promise-YES assumptions plug into these endpoints. The tests at lines 85--100 expose canonical iso-strong DAG and `P_ne_NP` wrappers, and lines 103--120 expose canonical promise-YES wrappers.

## 4. `hInDag` triviality audit

Critical question: can the route assumption

```lean
hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (...))
```

be proved in-repo from existing facts?

### 4.1 `P_subset_PpolyDAG_internal`

The internal theorem currently present is not a closed `P ⊆ PpolyDAG` theorem. `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean` defines `PpolyStraightLine`, proves `ppolyDAG_of_ppolyStraightLine`, and proves only:

```lean
P_subset_PpolyDAG_of_P_subset_PpolyStraightLine :
  P_subset_PpolyStraightLine → P_subset_PpolyDAG
```

So a trivial `hInDag` would still need a proof that each slice language is in `P` plus a proof of `P_subset_PpolyStraightLine` or another bridge.

### 4.2 Any theorem proving `gapPartialMCSP_Language` in `P`

I found fixed/asymptotic NP/TM witness infrastructure, but not a theorem of the form `ComplexityInterfaces.P (gapPartialMCSP_Language p)` for arbitrary canonical slices. `Model_PartialMCSP.lean` exposes `gapPartialMCSP_in_NP_TM` as an NP-side abbreviation, not a P-side membership proof. The canonical decider is computable for `sYES = 1`, but it is a decider for the global asymptotic canonical language and is packaged toward an NP/TM witness, not presently a `P` proof for every slice.

### 4.3 Truth-table hardwiring witnesses

There is abundant formula-side truth-table hardwiring infrastructure and NoGo history, but I did not find an in-repo theorem constructing `InPpolyDAG (gapPartialMCSP_Language p)` by hardwiring each entire canonical slice. This matters because a per-slice full truth table over canonical input length `N = 2 * 2^m` has size about `2^N`, not polynomial in `N`, so it should not automatically inhabit `PpolyDAG`.

### 4.4 Fixed-slice versus asymptotic family mismatch

A fixed slice is finite, so it is classically decidable/hardwirable as a finite Boolean function. But `InPpolyDAG` is a language-family witness with polynomial size as a function of input length. The route's `hInDag` requires such a witness for each language `gapPartialMCSP_Language (F.paramsOf n β)`, not merely one large circuit for one input length. Fixed-slice table hardwiring does not immediately give a polynomial family across all input lengths of that language.

### 4.5 Parser/decider infrastructure

The canonical decider file gives a computable canonical asymptotic decider and a `CanonicalAsymptoticVerifierComponents` bridge. In particular, `decideAsymptotic` returns false off canonical lengths and enumerates only size-1 circuits at canonical length; `CanonicalAsymptoticVerifierComponents` packages a TM whose acceptance matches that decider. This is NP/TM-verifier infrastructure, not currently a direct `PpolyDAG` construction for every slice language.

### Verdict

**hInDag_not_trivial**

Caveat: this is an audit verdict, not a proof of nontriviality. The next probe should explicitly try to derive the `hInDag` family from `decideAsymptotic` and the internal P-to-DAG plumbing. If that succeeds, the route likely turns red.

## 5. Hardwiring twin audit

Question: can one build an asymptotic `InPpolyDAG` witness for the canonical gapPartialMCSP language using truth-table/table hardwiring?

### Size calculation

For canonical slice parameter `m`, the encoded input length is

```text
N = Partial.inputLen m = 2 * Partial.tableLen m = 2 * 2^m.
```

A naive truth-table hardwire for the induced Boolean function on `N` input bits has roughly `2^N` rows. Measured against `N`, that is exponential, not polynomial. Thus the formula-side NOGO pattern based on log-width or syntactic support hardwiring does **not** automatically transfer to a full DAG-side `PpolyDAG` witness for the canonical language.

### DAG-side analogue of NOGO-000006

NOGO-000006 is about arbitrary all-essential log-width truth-table payloads satisfying a formula support-cardinality filter. A DAG-side analogue would need a polynomial-size DAG family whose payload is hardwired only on `O(log N)` input coordinates while still deciding the canonical slice language. The canonical gap language depends on decoded partial truth-table content across `2^m = N/2` semantic cells, so the simple log-width payload shape does not decide the real canonical language unless the route accidentally quantifies over arbitrary payloads. The current `hInDag` target is the fixed `gapPartialMCSP_Language (paramsOf n β)`, not an arbitrary payload language.

### Verdict

**hardwiring_does_not_transfer**

Caveat: a more subtle DAG twin could still exist via the canonical `sYES = 1` semantics. Because size-1 consistency has a compact characterization (constant/input candidates), the canonical language may be algorithmically easier than general MCSP. That should be tested through `open_hInDag_triviality_probe`, not assumed.

## 6. IsoStrong route audit

### What `IsoStrongFamilyEventually` demands

It demands an eventual, uniform isolation package for every sufficiently small correct DAG solver on every sufficiently large canonical slice. Concretely, for each small correct DAG `C`, one must find a valid YES center `yYes` and a bounded coordinate set `D` such that every valid input agreeing with `yYes` on `D` is forced into the YES side, plus a counting slack inequality.

### Could it be trivially true?

Not visibly. The condition applies to every correct small DAG under the `hInDag`-derived size bound and requires semantic forcing into YES. The trivial set `D = univ` would make forcing easy, but the slack inequality would become impossible or useless because `2^(tableLen - D.card)` collapses. A tiny `D` is required by the slack, and such a `D` is exactly the hard content.

### Could it be impossible?

Possibly for canonical `sYES = 1, sNO = 2`, because YES instances are partial tables consistent with a constant or one input literal, while NO instances are far from every size-1 circuit. The route asks for subcube-like YES forcing around every small correct solver. This could fail if there are correct solvers whose accepted region around YES centers cannot be captured by small semantic coordinate sets, or if valid YES centers are too sparse under the needed slack.

### Does it require new lower-bound content?

Yes. It appears to be close to the lower-bound/magnification gap: it converts hypothetical small-DAG correctness into an eventual isolation property that powers the counting contradiction. No existing in-repo theorem supplies it unconditionally for the canonical family.

### Is it close to the original main gap?

Yes. The route is designed precisely to supply the missing non-vacuous source content for `NP_not_subset_PpolyDAG`. It is likely not an easy infrastructure lemma.

### Verdict

**likely_as_hard_as_main_gap**

## 7. PromiseYes route audit

### What `PromiseYesSubcubeCertificateAt W` demands

For a concrete small-DAG witness `W`, it demands:

1. a valid YES center `yYes`,
2. a semantic coordinate set `S`,
3. slack `circuitCountBound p.n (p.sNO - 1) < 2^(tableLen - S.card)`, and
4. one-sided acceptance: every valid promise input agreeing with `yYes` on `S` is accepted by `W.C`.

### Does canonical `sYES = 1` make it trivial or impossible?

Neither is obvious. `sYES = 1` makes YES centers structurally simple: they are partial tables consistent with a size-1 circuit (constant false, constant true, or an input projection). That helps candidate selection. But the certificate must work relative to an arbitrary correct small DAG witness `W`, and the coordinate set must be small enough for the slack inequality. A full table agreement set would be trivial but destroys slack.

### Does it require selecting subcubes with nontrivial density/provenance?

Yes. The heart of the route is selecting semantic coordinates whose agreement defines a dense-enough region that is still forced into the YES side and accepted by `W.C`. The certificate is one-sided and witness-indexed, which is less overbroad than the refuted formula provider, but it still needs a real provenance/density argument.

### Can it be attacked by hardwiring?

A direct formula-hardwiring attack does not apply because the target is a DAG witness for the fixed gap language. However, it can be attacked by trying to instantiate `W` with a compact algorithmic/hardwired solver for canonical `sYES = 1`. If such a `W` exists and lacks the required small-coordinate YES subcube, the promise route is false. Conversely, if every such `W` admits the certificate for elementary reasons, the route may be too weak but still nontrivial to formalize.

### Verdict

**promising_nontrivial**

This verdict is relative to the iso-strong route: the promise-YES certificate target is narrower and witness-indexed, so it is the better first proof/search surface. It is not green; it needs targeted self-attacks.

## 8. NoGo cross-check

### PR13 `FormulaCertificateProviderPartial` refutation

- Status: **does not apply directly; possible analogue**.
- Probe 13 in `FormulaSupportBoundsFalsifiabilityProbe.lean` proves `false_of_FormulaCertificateProviderPartial`. The current anti-checker routes do not take `FormulaCertificateProviderPartial`, and the endpoint comment says the anti-checker wrapper avoids legacy `MagnificationAssumptions` and the refuted support-bounds surface.
- Analogue risk: if `PromiseYesSubcubeCertificateAt` is later derived from formula support-bounds/provider machinery, that derivation would be audit-only/refuted.

### NOGO-000004 prefixAnd

- Status: **possible analogue**.
- This is formula support-cardinality hardwiring by a log-width prefix conjunction. It does not directly decide the canonical gap language, but it warns against coordinate-count-only provenance filters.

### NOGO-000006 arbitrary ttFormula payload

- Status: **possible analogue, not direct**.
- Arbitrary log-width truth-table payloads defeat formula-side support filters. A DAG analogue would need a compact payload solver for the actual canonical gap language. Naive full truth-table hardwiring is exponential in canonical input length `N`, so the direct transfer fails.

### NOGO-000008 syntax rewrite

- Status: **does not apply directly**.
- This attacks syntactic-only formula provenance filters via tautological seed rewrites. The current route obligations are semantic DAG/coordinate certificates, not syntactic formula filters.
- Analogue risk: any future syntactic DAG provenance filter would need the same rewrite self-attack.

### NOGO-000009 normalisation meta-barrier

- Status: **does not apply directly**.
- This closes a structural-normalizer patch for V2 formula filters. Current route does not rely on such a normalizer.

### Support-bounds refutations

- Status: **does not apply directly to the route statements; applies to derivations through old provider stack**.
- The support-bounds probes refute broad formula-side assumptions and `MagnificationAssumptions`. The anti-checker endpoints are intentionally separated from those assumptions.

### `MagnificationAssumptions` refutations

- Status: **does not apply directly**.
- `pnp3/RefutedPredicates/Registry.lean` lists `MagnificationAssumptions`, `MagnificationAssumptions_fromPipeline`, and `FormulaCertificateProviderPartial` as refuted predicates. The audited endpoints consume `AntiCheckerAssumptions`, not `MagnificationAssumptions`.

## 9. Should TMVerifier sessions resume?

**yes_resume_as_np_infrastructure**

Reason: the canonical track still needs the TM-verifier witness to close the NP pullback cleanly. `CanonicalAsymptoticTrackData.lean` states that the TM-verifier witness is the mathematical gap for unconditionally closing the canonical NP pullback, and `CanonicalAsymptoticDecider.lean` reduces the verifier task to a typed component package. This work is NP infrastructure, not a lower-bound claim, and it remains useful regardless of whether the iso-strong/promise route later turns red.

## 10. Recommended next action

**open_hInDag_triviality_probe**

Rationale: before investing in iso-strong or promise-YES proof attempts, test the most dangerous failure mode: whether canonical `sYES = 1` plus the computable decider/parser stack can manufacture the quantified `hInDag` family. If `hInDag` is in-repo trivial, the route becomes suspicious/red. If not, the promise-YES route is the better L0 target.

## 11. What would count as progress?

A concrete next result that changes route status would be one of the following:

1. **Red-changing theorem/report:** a Lean probe deriving
   `∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf n β))`
   from existing canonical decider/parser/P-to-DAG infrastructure. This would make `hInDag` effectively trivial and force a route redesign.
2. **Yellow-to-green evidence:** a Lean probe proving that naive full truth-table/table-hardwiring cannot satisfy the `PpolyDAG` size polynomial for canonical input length `N = 2 * 2^m`, plus a report enumerating remaining compact-solver attacks.
3. **Promise route progress:** for canonical `sYES = 1`, a theorem constructing `PromiseYesSubcubeCertificateAt W` for a sharply delimited class of non-hardwired `SmallDAGWitnessOnSlice` records, with an explicit anti-hardwiring lemma showing why log-width/ttFormula payload attacks do not instantiate that class.

The immediate recommendation is item 1: open the `hInDag` triviality probe.

## Commands run

```text
find .. -name AGENTS.md -print
cat AGENTS.md
git status --short
git rev-parse --abbrev-ref HEAD
git rev-parse HEAD
sed -n '1,220p' RESEARCH_CONSTITUTION.md
sed -n '1,260p' seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md
find seed_packs -path '*D0_provider_retarget*' -type f -print | head -20
find seed_packs -maxdepth 3 -type d -name 'post_pr13*' -print
find seed_packs -maxdepth 3 -type f | sed -n '1,120p'
rg -n "AsymptoticIsoStrongRoute|IsoStrongFamilyEventually|PromiseYesSubcubeCertificateAt|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually" pnp3
rg -n "FormulaCertificateProviderPartial|RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions" pnp3/Magnification pnp3/LowerBounds pnp3/Tests
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '200,430p;990,1130p;1145,1175p'
nl -ba pnp3/Magnification/FinalResultWeakRoutes.lean | sed -n '1,220p'
nl -ba pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean | sed -n '1070,1106p'
nl -ba pnp3/LowerBounds/DAGStableRestrictionProducer.lean | sed -n '2460,2525p'
head -60 pnp3/Magnification/FinalResultMainline.lean
head -80 pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean
head -50 pnp3/LowerBounds/DAGStableRestrictionProducer.lean
nl -ba pnp3/Complexity/PsubsetPpolyDAG_Internal.lean | sed -n '1,220p'
rg -n "gapPartialMCSP_Language.*ComplexityInterfaces\.P|ComplexityInterfaces\.P.*gapPartialMCSP_Language|GapPartialMCSP.*P\b|in_P|InP" pnp3 | head -100
wc -l outputs/nogolog.jsonl
rg -n "NOGO-000004|NOGO-000006|NOGO-000008|NOGO-000009|FormulaCertificateProviderPartial|support|MagnificationAssumptions" outputs/nogolog.jsonl pnp3/RefutedPredicates/Registry.lean pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean
python3 - <<'PY'
import json
for line in open('outputs/nogolog.jsonl'):
    d=json.loads(line)
    if d['id'] in {'NOGO-000004','NOGO-000006','NOGO-000008','NOGO-000009'}:
        print(d['id'], d.get('candidate_id'))
        print('class',d.get('failure_class'))
        print('pattern',d.get('structural_pattern','')[:800])
        print('formal',d.get('formal_witness'))
        print()
PY
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '1,45p;138,210p;230,280p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,90p;125,170p;190,230p;690,740p'
nl -ba pnp3/Tests/CanonicalIntegrationTests.lean | sed -n '70,125p'
```

`./scripts/check.sh` was run after writing this report; see final worker output for pass/fail status.
