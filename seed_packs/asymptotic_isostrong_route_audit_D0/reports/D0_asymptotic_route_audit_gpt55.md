# D0 — Non-vacuity audit for `AsymptoticIsoStrongRoute` / Promise-YES route

Task: `asymptotic_isostrong_route_audit_D0`  
Handle: `gpt55`  
Branch observed: `work` (user prompt requested `main`; repository checkout reports `work`)  
Commit before: `1e0454f92b126815b095952e6135b43fce894f6f`

## 1. Executive verdict

**YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS**

The route is not currently proved vacuous or hardwired.  It is also not a green route: the endpoint still assumes the full asymptotic iso-strong or Promise-YES source obligation, and the only safe classification is a conditional canonical-candidate route requiring targeted self-attacks.

Key reasons:

- The active endpoint assumptions quantify over an `hInDag` family of per-slice `InPpolyDAG` witnesses and then demand nontrivial isolation/YES-subcube consequences for every sufficiently large canonical slice.
- Existing in-repo hardwiring refutations attack formula-provider/provenance/support routes, not the DAG-side asymptotic route directly.
- Fixed-slice truth-table hardwiring exists for `PpolyFormula`, but that fixed-slice theorem does not immediately become a polynomial-size asymptotic `PpolyDAG` family at canonical input length `N = 2 * 2^m`.
- The canonical track has `sYES = 1`, `sNO = 2`; this makes the Promise-YES route numerically delicate and worthy of an L0 probe, but does not by itself prove triviality or impossibility.

## 2. Exact route definitions

### `AsymptoticIsoStrongRoute`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Location:** definition `AsymptoticIsoStrongRoute`, lines 218--227.
- **Definition summary:** for a supplied `hAsym : AsymptoticFormulaTrackHypothesis`, it requires that for every per-slice DAG-membership family
  ```lean
  hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))
  ```
  the eventual canonical slice family satisfies `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic hAsym) hInDag`.
- **Full dependency surface visible in the definition:**
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `ComplexityInterfaces.InPpolyDAG`
  - `Models.gapPartialMCSP_Language`
  - `IsoStrongFamilyEventually`
- **Imports `FormulaCertificateProviderPartial`?** The definition does **not** mention `FormulaCertificateProviderPartial`.  Its file imports `Magnification.LocalityProvider_Partial`, where `FormulaCertificateProviderPartial` is defined, so the file's import closure includes that refuted provider infrastructure, but this definition's dependency surface does not consume it.

### `AsymptoticPromiseYesCertificateRoute`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Location:** definition `AsymptoticPromiseYesCertificateRoute`, lines 238--256.
- **Definition summary:** for every per-slice `hInDag`, it requires a positive `β0` and threshold function `nCert`; for all sufficiently large canonical slices and all `0 < β < β0`, every `SmallDAGWitnessOnSlice` at epsilon `1` must have `Nonempty (PromiseYesSubcubeCertificateAt W)`.
- **Full dependency surface visible in the definition:**
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `ComplexityInterfaces.InPpolyDAG`
  - `Models.gapPartialMCSP_Language`
  - `SmallDAGWitnessOnSlice`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `PromiseYesSubcubeCertificateAt`
- **Imports `FormulaCertificateProviderPartial`?** Same as above: no direct mention in the definition; file import closure includes `LocalityProvider_Partial` via `FinalResultMainline.lean` imports.

### `AsymptoticPromiseYesWeakRouteEventually`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Location:** definition `AsymptoticPromiseYesWeakRouteEventually`, lines 265--282.
- **Definition summary:** for every per-slice `hInDag`, it requires positive `ε` and `β0`; for every `0 < β < β0`, eventually every slice satisfies `SmallDAGImpliesPromiseYesSubcubeAtEventually` for the canonical family and the size bound derived from `hInDag`.
- **Full dependency surface visible in the definition:**
  - `AsymptoticFormulaTrackHypothesis`
  - `eventualGapSliceFamily_of_asymptotic`
  - `ComplexityInterfaces.InPpolyDAG`
  - `Models.gapPartialMCSP_Language`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `SmallDAGImpliesPromiseYesSubcubeAtEventually`
- **Imports `FormulaCertificateProviderPartial`?** No direct use; same transitive file-import caveat as above.

### `IsoStrongFamilyEventually`

- **File:** `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
- **Location:** definition `IsoStrongFamilyEventually`, lines 1078--1104.
- **Definition summary:** given a `GapSliceFamilyEventually` and per-slice `hInDag`, it asks for a positive `β0`, a coordinate budget `κ`, and thresholds `nIso`; for every sufficiently large slice, every correctly solving small DAG circuit must yield a valid YES center `yYes` and coordinate set `D` with `D.card ≤ κ n β`, such that every valid completion agreeing with `yYes` on `D` is itself in the YES set, plus a counting slack inequality `F.Mof n (F.Tof n β) < 2 ^ (tableLen - κ n β)`.
- **Full dependency surface visible in the definition:**
  - `GapSliceFamilyEventually`
  - `ComplexityInterfaces.InPpolyDAG`
  - `Models.gapPartialMCSP_Language`
  - `DagCircuit`, `DagCircuit.size`
  - `ppolyDAGSizeBoundOnSlicesEventually`
  - `CorrectOnPromiseSlice`
  - `gapSliceOfParams`
  - `Bitstring`, `ValidEncoding`, `AgreeOnValues`, `Finset`
- **Imports `FormulaCertificateProviderPartial`?** No direct import in `AsymptoticDAGBarrierTheorems.lean`; this is a lower-bound DAG-barrier theorem file importing `LowerBounds.AsymptoticDAGBarrierInterfaces`.

### `PromiseYesSubcubeCertificateAt`

- **File:** `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- **Location:** structure `PromiseYesSubcubeCertificateAt`, lines 2480--2503.
- **Definition summary:** for a `SmallDAGWitnessOnSlice W`, it packages one valid YES center `yYes`, a semantic value-coordinate set `S`, direct counting slack, and a one-sided promise-acceptance condition saying every valid YES/NO completion agreeing with `yYes` on `S` is accepted by `W.C`.
- **Full dependency surface visible in the definition:**
  - `GapPartialMCSPParams`
  - `SmallDAGWitnessOnSlice`
  - `Core.BitVec`, `Models.partialInputLen`
  - `GapPartialMCSPPromise p`.Yes/No
  - `ValidEncoding`
  - `ValueCoordinateSet`
  - `Models.circuitCountBound`, `Models.Partial.tableLen`
  - `AgreeOnValues`
  - `DagCircuit.eval`
- **Imports `FormulaCertificateProviderPartial`?** No direct mention.  `DAGStableRestrictionProducer.lean` imports `LowerBounds.SingletonDensityContradiction`, which contains compatibility theorems taking `Magnification.FormulaCertificateProviderPartial`; therefore its broader import closure may see the provider, but the structure itself is DAG-native and does not consume it.

## 3. Endpoint wiring

### `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File/location:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1057--1065.
- **Inputs:** `anti : AntiCheckerAssumptions` and `hIso : AsymptoticIsoStrongRoute anti.asymptotic`.
- **Wiring:** forwards `anti.asymptotic`, `anti.npBridge`, and `hIso` to the generic asymptotic iso-strong theorem.
- **Classification:** **conditional canonical candidate route**.  It is not audit-only by shape, because it avoids `MagnificationAssumptions` and support-bounds providers.  It remains conditional because `AntiCheckerAssumptions` and `hIso` are supplied hypotheses.

### `P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File/location:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1071--1077.
- **Inputs:** same anti-checker package and iso-strong route.
- **Wiring:** applies `P_ne_NP_final_dag_only` to the DAG separation produced above.
- **Classification:** **conditional canonical candidate route**, but it must not be reported as an unconditional P-vs-NP claim.  It is a conditional endpoint only.

### `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File/location:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1098--1106.
- **Inputs:** `anti : AntiCheckerAssumptions` and `hRoute : AsymptoticPromiseYesCertificateRoute anti.asymptotic`.
- **Wiring:** forwards to the generic Promise-YES certificate route, which in turn converts the certificate route into the iso-strong route.
- **Classification:** **conditional canonical candidate route / suspicious enough for targeted self-attack**.  It is not currently refuted, but it is closer to the old certificate-provider shape and should be probed for vacuity/hardwiring analogues.

### `P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File/location:** `pnp3/Magnification/FinalResultMainline.lean`, lines 1112--1118.
- **Inputs:** same anti-checker package and Promise-YES route.
- **Wiring:** applies `P_ne_NP_final_dag_only` after the Promise-YES DAG separation theorem.
- **Classification:** **conditional canonical candidate route / suspicious enough for targeted self-attack**.  It is not refuted in-repo, but it is not an unconditional result.

## 4. `hInDag` triviality audit

**Critical question:** can the route assumption

```lean
hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (...))
```

be proved in-repo from existing facts?

### Checks

- **`P_subset_PpolyDAG_internal`:** the active internal inclusion theorem `proved_P_subset_PpolyDAG_internal` proves `P_subset_PpolyDAG`, but using it for `hInDag` would require proving each fixed language `gapPartialMCSP_Language (paramsOf n β)` is in `P`.  I found the inclusion route, but not a theorem giving `P (gapPartialMCSP_Language p)` for arbitrary `p`.
- **Any theorem proving `gapPartialMCSP_Language` in `P`:** the canonical decider infrastructure proves a computable Boolean decider for the canonical **asymptotic** language and correctness against `gapPartialMCSP_AsymptoticLanguage`, not a `ComplexityInterfaces.P` theorem for every fixed `gapPartialMCSP_Language p`.
- **Truth-table hardwiring witnesses:** there is a fixed-slice formula hardwiring theorem `fixedSlice_gapPartialMCSP_in_PpolyFormula p`; it proves `PpolyFormula (gapPartialMCSP_Language p)` by `ttFormula` at the single relevant length and constant false elsewhere.  It does not directly produce `InPpolyDAG`, though formula-to-DAG conversion could be a future probe.
- **Fixed-slice vs asymptotic family mismatch:** the formula hardwiring theorem is per fixed `p`; `hInDag` is a family indexed by all `n, β` whose induced size bounds are later used at canonical slice lengths.  Even if each fixed slice can be hardwired, a uniform asymptotic `PpolyDAG` bound must be polynomial in the input length of that fixed language, and the route's contradiction relies on how these per-slice witnesses induce `ppolyDAGSizeBoundOnSlicesEventually`.
- **pnp3/pnp4 parser infrastructure:** canonical parser/decider code can identify canonical lengths `N = Partial.inputLen m`, returns false off canonical lengths, and decides the canonical asymptotic language.  It does not close `hInDag`.

### Verdict

**hInDag_not_trivial**

I did not find an in-repo proof of the full per-slice `hInDag` assumption from existing facts.  The strongest available attack is fixed-slice formula hardwiring, not a completed DAG-side asymptotic `InPpolyDAG` family.

## 5. Hardwiring twin audit

**Question:** can one build an asymptotic `InPpolyDAG` witness for canonical gapPartialMCSP using truth-table/table-hardwiring, analogous to `NOGO-000006`?

### Size analysis

For canonical slice parameter `m`, the canonical input length is

```text
N = Partial.inputLen m = 2 * Partial.tableLen m = 2 * 2^m.
```

A full truth-table hardwiring circuit for an arbitrary language on inputs of length `N` has size roughly exponential in `N` (one branch per input string), i.e. about `2^N`, not polynomial in `N`.  Therefore the direct per-canonical-length truth-table hardwiring attack **does not transfer** to `PpolyDAG`.

The old formula fixed-slice witness avoids this by treating `p` as fixed and placing a single huge circuit at one fixed input length; its polynomial bound can choose a constant exponent depending on that fixed circuit size.  That does not automatically produce a single asymptotic family over growing canonical lengths.

A subtler DAG hardwiring twin might use the semantic structure of GapMCSP with `sYES = 1` and `sNO = 2`, or compile the canonical decider into polynomial-size DAGs.  No such theorem is present in the required files.

### Verdict

**hardwiring_does_not_transfer**

Direct truth-table/table hardwiring is too large relative to canonical input length `N = 2 * 2^m`.  A possible structured-decider/P-membership attack remains worth a targeted `hInDag` probe, but the `NOGO-000006` arbitrary log-width ttFormula payload does not directly refute this DAG route.

## 6. IsoStrong route audit

### What `IsoStrongFamilyEventually` demands

It demands eventual, uniform-in-small-`β` isolation content.  For every sufficiently large slice and every small DAG solver that is correct on the promise, one must extract:

1. a valid YES center `yYes`,
2. a coordinate set `D` of size bounded by `κ n β`,
3. a semantic forcing clause: every valid completion agreeing with `yYes` on `D` is in the YES set,
4. a counting slack inequality strong enough to contradict the number of low-complexity NO-side objects.

### Could it be trivially true?

Not obviously.  Choosing `D = univ` makes the forcing clause easy but usually destroys the slack inequality.  Choosing `D = ∅` would require every valid completion to be YES, which is false for normal promise slices.  Thus the definition contains a real tension between semantic forcing and counting slack.

### Could it be impossible?

Possibly, especially for the canonical `sYES = 1`, `sNO = 2` regime, but impossibility is not proved in-repo.  The strongest concern is that forcing all valid completions agreeing on a small coordinate set into YES may be nearly equivalent to the original lower-bound/magnification bottleneck.

### Does it require new lower-bound content?

Yes.  It asks for a structural consequence of every hypothetical small-DAG solver; this is not supplied by the existing canonical parser/decider infrastructure.

### Is it close to the original main gap?

Yes.  It is intentionally a narrowed source obligation that, once supplied, gives `NP_not_subset_PpolyDAG`; therefore it is close to the main gap and should be treated as mainline only if it reduces `VerifiedNPDAGLowerBoundSource`/`SearchMCSPWeakLowerBound`-style obligations rather than merely repackaging them.

### Verdict

**likely_as_hard_as_main_gap**

The route appears nontrivial but very strong.  It is not currently vacuous; it also does not look like a low-effort source theorem.

## 7. PromiseYes route audit

### What `PromiseYesSubcubeCertificateAt W` demands

For a fixed `SmallDAGWitnessOnSlice W`, it requires a valid YES center `yYes`, a semantic coordinate set `S`, slack

```lean
circuitCountBound p.n (p.sNO - 1) < 2 ^ (Partial.tableLen p.n - S.card)
```

and one-sided promise acceptance: every valid YES/NO completion agreeing with `yYes` on `S` is accepted by the solver circuit `W.C`.

### Does canonical `sYES = 1` make it trivial or impossible?

It does not make it obviously trivial.  A YES center means a partial table consistent with a size-1 circuit.  Such centers exist, but the certificate must also find a coordinate set whose agreement subcube is accepted by an arbitrary correct small-DAG witness and whose size preserves the slack.  It is also not obviously impossible, because the acceptance condition is one-sided and centered on YES.

### Does it require selecting subcubes with nontrivial density/provenance?

Yes.  The route must choose subcubes with enough semantic control to force acceptance while leaving enough free coordinates for the counting slack.  This is precisely the type of selection where prior formula-side provenance filters failed, so a DAG-native self-attack is necessary.

### Can it be attacked by hardwiring?

The direct fixed-slice truth-table hardwiring attack does not transfer to the asymptotic `PpolyDAG` setting.  However, the Promise-YES route is closer to certificate-provider language than the iso-strong route, and the universal quantification over all small-DAG witnesses should be checked for a DAG-side analogue of arbitrary payload/hardwired-witness attacks.

### Verdict

**promising_nontrivial**

This is the more concrete source target than the iso-strong route.  It is still conditional and should be attacked, but I do not find a direct refutation.

## 8. NoGo cross-check

| NoGo / refutation | Status against this route | Notes |
| --- | --- | --- |
| PR13 `FormulaCertificateProviderPartial` refutation | **does not apply directly** | The active definitions do not consume `FormulaCertificateProviderPartial`; the PR13 refutation is formula-provider-specific and derives contradiction from universal quantification over `PpolyFormula` witnesses. |
| `NOGO-000004` prefixAnd | **possible analogue** | Shows syntactic/provenance filters can be satisfied by log-width hardwiring.  The asymptotic DAG route is semantic and not support-cardinality-only, so this is not a direct refutation. |
| `NOGO-000006` arbitrary ttFormula payload | **possible analogue / does not apply directly** | Arbitrary log-width formula payloads refute formula support-diversity filters.  Direct full truth-table hardwiring over canonical length is exponential in `N`; a structured DAG analogue would require a new probe. |
| `NOGO-000008` syntax rewrite | **does not apply directly** | The audited route is not a purely syntactic formula-filter candidate. |
| `NOGO-000009` normalisation meta-barrier | **does not apply directly** | Same reason: no V2 syntactic normaliser/filter is used here. |
| support-bounds refutations | **does not apply directly** | Existing support-bounds/MagnificationAssumptions routes are explicitly refuted/audit-only; the anti-checker route avoids those assumptions. |
| `MagnificationAssumptions` refutations | **does not apply directly** | The endpoint inputs are `AntiCheckerAssumptions` plus route obligations, not the legacy `MagnificationAssumptions` package. |

## 9. Should TMVerifier sessions resume?

**yes_resume_as_np_infrastructure**

The canonical track still needs the TM/verifier witness to close the NP pullback infrastructure.  Resuming TMVerifier work is useful as NP infrastructure, but it should not be advertised as progress on the DAG lower-bound source obligation itself.

## 10. Recommended next action

**open_promiseYes_route_probe_L0**

The Promise-YES route is concrete enough to probe now: try to either construct a DAG-side hardwiring/counterexample witness against `PromiseYesSubcubeCertificateAt` or prove that the direct hardwiring family cannot satisfy the certificate requirements with the required slack.

## 11. What would count as progress?

A concrete next result that would change route status:

```text
L0 Promise-YES non-vacuity/self-attack report:
For the canonical family (`sYES = 1`, `sNO = 2`), either
  (A) exhibit a formal/informal-but-parameter-complete DAG-side hardwiring witness W
      and show `PromiseYesSubcubeCertificateAt W` is impossible for infinitely many canonical slices, or
  (B) prove a Lean lemma/report-level theorem that the known fixed-slice truth-table hardwiring attacks cannot provide `SmallDAGWitnessOnSlice` with polynomial `ppolyDAGSizeBoundOnSlicesEventually` at canonical length `N = 2 * 2^m`, and identify the remaining semantic source obligation precisely.
```

This would convert the current yellow status either toward red (if an analogue exists) or toward green/nonvacuous (if the plausible hardwiring attacks are ruled out and only genuine lower-bound content remains).

## Required command log

Commands run:

```bash
rg -n "AsymptoticIsoStrongRoute|IsoStrongFamilyEventually|PromiseYesSubcubeCertificateAt|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually" pnp3
```

```bash
rg -n "FormulaCertificateProviderPartial|RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions" pnp3/Magnification pnp3/LowerBounds pnp3/Tests
```

```bash
./scripts/check.sh
```

Additional inspection commands used included `sed`, `nl -ba`, `rg`, `find`, and a short `python3` JSONL reader for `outputs/nogolog.jsonl`.

## Scope violations

None.  This report is Markdown-only.  No Lean source, JSONL, NoGoLog, spec, or known-guards files were edited.
