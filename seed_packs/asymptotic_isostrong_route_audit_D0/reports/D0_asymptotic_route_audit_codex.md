# D0 — non-vacuity audit for AsymptoticIsoStrongRoute / PromiseYes route

Task: `asymptotic_isostrong_route_audit_D0`  
Handle: `codex`  
Branch observed: `work` (user prompt says `main`; repository checkout was already on `work`)  
Commit before: `1e0454f92b126815b095952e6135b43fce894f6f`

## Required-reading note

I read the requested in-repo files that exist on this checkout:

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

The requested post-PR13 retarget report path
`seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`
does not exist in this checkout.  I searched under `seed_packs/` and found no
`post_pr13_provider_retarget_D0` seed pack.  This audit therefore treats the
formal Lean files and the PR13 refutation registry/probe as canonical.

---

## 1. Executive verdict

**YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS**

Reason: the two asymptotic routes are not currently proved from the refuted
`FormulaCertificateProviderPartial` predicate and are not obviously killed by
the fixed-slice truth-table hardwiring failures.  However, they are very strong
conditional assumptions: both universally quantify over an asymptotic
`hInDag : ∀ n β, InPpolyDAG (...)` surface and demand source-side structure for
all sufficiently large canonical slices.  I did not find an in-repo proof that
`hInDag` is trivial for the canonical family, but this absence should be turned
into a targeted Lean/search probe before promoting either route.

---

## 2. Exact route definitions

### `AsymptoticIsoStrongRoute`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Definition:** `def AsymptoticIsoStrongRoute` at lines 218–227.
- **Statement summary:** for a fixed `hAsym : AsymptoticFormulaTrackHypothesis`,
  every supplied family membership witness
  `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))`
  must yield `IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic hAsym) hInDag`.
- **Full dependency surface visible from the statement:**
  - `AsymptoticFormulaTrackHypothesis`;
  - `eventualGapSliceFamily_of_asymptotic`;
  - `ComplexityInterfaces.InPpolyDAG`;
  - `gapPartialMCSP_Language`;
  - `IsoStrongFamilyEventually`.
- **Does the defining file import `FormulaCertificateProviderPartial`?**
  Indirectly/at module level, yes in the sense that `FinalResultMainline.lean`
  imports `Magnification.LocalityProvider_Partial`, the home of
  `FormulaCertificateProviderPartial`.  The route statement itself does **not**
  mention `FormulaCertificateProviderPartial`.

### `AsymptoticPromiseYesCertificateRoute`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Definition:** `def AsymptoticPromiseYesCertificateRoute` at lines 238–256.
- **Statement summary:** for each `hInDag` family witness, there are `β0 > 0`
  and a threshold function `nCert` such that for every sufficiently large
  canonical slice and every `SmallDAGWitnessOnSlice` at the canonical
  `ppolyDAGSizeBoundOnSlicesEventually` size surface, there is a nonempty
  `PromiseYesSubcubeCertificateAt W`.
- **Full dependency surface visible from the statement:**
  - `AsymptoticFormulaTrackHypothesis`;
  - `eventualGapSliceFamily_of_asymptotic`;
  - `ComplexityInterfaces.InPpolyDAG`;
  - `gapPartialMCSP_Language`;
  - `SmallDAGWitnessOnSlice`;
  - `ppolyDAGSizeBoundOnSlicesEventually`;
  - `PromiseYesSubcubeCertificateAt`;
  - arithmetic side conditions `0 < β`, `β < β0`, and
    `n ≥ max hAsym.N0 (nCert β)`.
- **Does the defining file import `FormulaCertificateProviderPartial`?**
  Module-level yes via `Magnification.LocalityProvider_Partial`; statement-level
  no.

### `AsymptoticPromiseYesWeakRouteEventually`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Definition:** `def AsymptoticPromiseYesWeakRouteEventually` at lines 265–282.
- **Statement summary:** for every `hInDag`, there is an `ε > 0` and `β0 > 0`
  such that for every small `β`, beyond some `n0 ≥ F.N0`, all later slices
  satisfy `SmallDAGImpliesPromiseYesSubcubeAtEventually` under
  `ppolyDAGSizeBoundOnSlicesEventually`.
- **Full dependency surface visible from the statement:**
  - `AsymptoticFormulaTrackHypothesis`;
  - `eventualGapSliceFamily_of_asymptotic`;
  - `ComplexityInterfaces.InPpolyDAG`;
  - `gapPartialMCSP_Language`;
  - `ppolyDAGSizeBoundOnSlicesEventually`;
  - `SmallDAGImpliesPromiseYesSubcubeAtEventually`.
- **Does the defining file import `FormulaCertificateProviderPartial`?**
  Module-level yes via `Magnification.LocalityProvider_Partial`; statement-level
  no.

### `IsoStrongFamilyEventually`

- **File:** `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
- **Definition:** `def IsoStrongFamilyEventually` at lines 1078–1104.
- **Statement summary:** for a `GapSliceFamilyEventually F` and an `hInDag`
  family witness, there must exist `β0 > 0`, a coordinate budget `κ`, and a
  threshold `nIso` such that all sufficiently large slices and all small DAG
  circuits `C` satisfying the canonical size bound and promise correctness admit
  a valid YES center `yYes` and a coordinate set `D` with `D.card ≤ κ n β`.
  Every valid completion agreeing with `yYes` on `D` must be a YES instance, and
  the global counting slack `F.Mof n (F.Tof n β) < 2^(tableLen - κ n β)` must hold.
- **Full dependency surface visible from the statement:**
  - `GapSliceFamilyEventually`;
  - `ComplexityInterfaces.InPpolyDAG`;
  - `gapPartialMCSP_Language`;
  - `ppolyDAGSizeBoundOnSlicesEventually`;
  - `DagCircuit`, `DagCircuit.size`;
  - `CorrectOnPromiseSlice`;
  - `gapSliceOfParams`;
  - `ValidEncoding`;
  - `AgreeOnValues`;
  - `GapSliceFamilyEventually.encodedLen`, `.tableLen`, `.paramsOf`, `.Mof`, `.Tof`, `.N0`.
- **Does the defining file import `FormulaCertificateProviderPartial`?**
  No direct import was found in this file's definition surface.  It lives under
  `LowerBounds`, not the formula-provider module.

### `PromiseYesSubcubeCertificateAt`

- **File:** `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- **Definition:** `structure PromiseYesSubcubeCertificateAt` at lines 2480–2509.
- **Statement summary:** for a concrete `SmallDAGWitnessOnSlice W`, provide a
  valid YES center `yYes`, a value-coordinate set `S`, direct counting slack
  `circuitCountBound p.n (p.sNO - 1) < 2^(Partial.tableLen p.n - S.card)`, and
  one-sided promise acceptance: every valid YES/NO completion agreeing with the
  center on `S` is accepted by `W.C`.
- **Full dependency surface visible from the statement:**
  - `GapPartialMCSPParams`;
  - `SizeBound : Rat → Nat → Prop` and `ε : Rat`;
  - `SmallDAGWitnessOnSlice`;
  - `Core.BitVec`, `Models.partialInputLen`;
  - `GapPartialMCSPPromise`, `.Yes`, `.No`;
  - `ValidEncoding`;
  - `ValueCoordinateSet`;
  - `Models.circuitCountBound`, `Models.Partial.tableLen`;
  - `AgreeOnValues`;
  - `DagCircuit.eval`.
- **Does the defining file import `FormulaCertificateProviderPartial`?**
  No direct dependency is visible from this statement.  This is a DAG-side
  certificate structure.

---

## 3. Endpoint wiring

### `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Theorem:** lines 1057–1065.
- **Wiring:** takes `anti : AntiCheckerAssumptions` and
  `hIso : AsymptoticIsoStrongRoute anti.asymptotic`, then invokes
  `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute` with
  `anti.asymptotic` and `anti.npBridge`.
- **Classification:** **canonical candidate route**, but **conditional**.  It is
  anti-checker-only and avoids `MagnificationAssumptions`, but it is not closed;
  it still assumes `hIso` and the anti-checker/NP bridge package.

### `P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Theorem:** lines 1071–1077.
- **Wiring:** applies `P_ne_NP_final_dag_only` to the previous
  `NP_not_subset_PpolyDAG` endpoint.
- **Classification:** **canonical candidate route**, **conditional**.  Not an
  unconditional P-vs-NP claim because it takes `anti` and `hIso` arguments.

### `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Theorem:** lines 1098–1106.
- **Wiring:** takes `anti : AntiCheckerAssumptions` and
  `hRoute : AsymptoticPromiseYesCertificateRoute anti.asymptotic`, then invokes
  `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute`; that
  theorem reduces the promise-YES route to the iso-strong route via
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
- **Classification:** **canonical candidate route**, **conditional**.  It is
  slightly more source-friendly than the direct iso-strong route, but still
  demands a strong witness-indexed certificate source.

### `P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

- **File:** `pnp3/Magnification/FinalResultMainline.lean`
- **Theorem:** lines 1112–1118.
- **Wiring:** applies `P_ne_NP_final_dag_only` to the previous promise-YES
  `NP_not_subset_PpolyDAG` endpoint.
- **Classification:** **canonical candidate route**, **conditional**.  Not
  refuted by the PR13 provider refutation, but not closed.

### Shared endpoint caveat

`P_ne_NP_final_dag_only` itself is honest DAG-side wiring: it derives
`P_ne_NP` from a supplied `NP_not_subset_PpolyDAG` plus the internal
`proved_P_subset_PpolyDAG_internal` theorem.  Therefore the risk is not in this
last wrapper; the risk is entirely in whether the assumed asymptotic route is
non-vacuous and not hardwired.

---

## 4. `hInDag` triviality audit

Critical question: can the route assumption

```lean
hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (...))
```

be proved in-repo from existing facts?

### Checks

- **`P_subset_PpolyDAG_internal`:**
  The repository has `Complexity.Simulation.proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG` in
  `pnp3/Complexity/Simulation/Circuit_Compiler.lean` lines 602–608.  This only
  yields `PpolyDAG L` for languages already known to be in `P`; it does not by
  itself prove the fixed-slice gap MCSP languages are in `P`.
- **Any theorem proving `gapPartialMCSP_Language` in `P`:**
  I searched for direct `gapPartialMCSP_Language`-in-`P` surfaces and did not
  find one.  The canonical decider infrastructure gives a Boolean decider for
  the canonical `sYES = 1` asymptotic language and a conditional TM witness
  bridge, but I did not find a theorem packaging each fixed-slice
  `gapPartialMCSP_Language (F.paramsOf n β)` as `ComplexityInterfaces.P`.
- **Truth-table hardwiring witnesses:**
  Existing PR13 support/provenance refutations hardwire formula-side witnesses.
  The registry explicitly says `FormulaCertificateProviderPartial` is refuted
  because its universal `PpolyFormula` quantification is satisfied by a
  truth-table hardwiring witness.  This does not immediately transfer to
  `PpolyDAG` for an asymptotic family because the size budget is polynomial in
  the actual input length.
- **Fixed-slice vs asymptotic family mismatch:**
  For a fixed `p`, a language over a fixed length can often be artificially
  treated/hardwired in ways that do not provide a uniform polynomial-size family
  over all input lengths.  The asymptotic route asks for all `n β` in a single
  family-shaped premise, so fixed-slice hardwiring is not automatically a proof
  of `hInDag`.
- **Parser/TM infrastructure:**
  `CanonicalAsymptoticDecider.lean` defines `decideAsymptotic` and proves the
  decidability/correctness side of the canonical language; it leaves the concrete
  TM witness as the remaining engineering obligation.  This helps NP
  infrastructure, not a P-membership theorem for every fixed-slice language.

### Verdict

**hInDag_not_trivial**

I found no in-repo theorem that derives the exact `hInDag` family premise for
canonical gapPartialMCSP slices from `proved_P_subset_PpolyDAG_internal` or from
parser/decider infrastructure.  This should still receive a dedicated Lean
probe because the route definitions intentionally quantify over `hInDag`, and a
hidden fixed-slice-to-family bridge would be route-ending.

---

## 5. Hardwiring twin audit

Question: can one build an asymptotic `InPpolyDAG` witness for the canonical
gapPartialMCSP language using truth-table/table hardwiring, analogous to
NOGO-000006?

### Size analysis

For canonical MCSP parameter `m`, the partial-truth-table input length is

```text
N = 2 * 2^m
```

A complete table-hardwired decider over all inputs of this slice can require a
table of size about `2^N`, because the language input is itself a length-`N`
partial truth table.  `PpolyDAG` allows size polynomial in `N`, not polynomial in
`2^N`.  Thus the naive per-slice truth-table hardwiring that kills formula-side
provider predicates does **not** automatically fit the DAG-family budget.

There are smaller special cases for canonical `sYES = 1`: `decideYesAt1`
enumerates `m + 2` size-1 candidate circuits and checks consistency.  But that
is an algorithmic/semantic decider for the canonical YES predicate, not the same
as arbitrary table-hardwiring of a black-box language slice.  It may support NP
or eventual decidability infrastructure; it does not by itself give the
route's `hInDag` family witness unless packaged through a `P` theorem and the
P-to-PpolyDAG compiler.

### Verdict

**hardwiring_does_not_transfer**

The known truth-table hardwiring attacks are dangerous analogues but do not
currently transfer to an asymptotic `PpolyDAG` witness at canonical input length
`N = 2 * 2^m`; naive full-table hardwiring is exponential in `N`.

---

## 6. IsoStrong route audit

### What `IsoStrongFamilyEventually` demands

It demands eventual, uniform isolation data for every sufficiently large small-
DAG-correct promise solver: a YES center, a bounded value-coordinate set, an
agreement-implies-YES property, and a counting slack inequality.  The demand is
made under the canonical `ppolyDAGSizeBoundOnSlicesEventually F hInDag` size
surface.

### Could it be trivially true?

Not obviously.  The route is universally quantified over every `hInDag`, but
once an `hInDag` is supplied the theorem must handle every sufficiently large
small DAG solver satisfying the derived size bound and promise correctness.  The
required coordinate isolation appears semantic and lower-bound-like, not a mere
record constructor.

### Could it be impossible?

Possibly.  The property is strong: it says small DAG solvers imply very
structured YES subcubes with enough complement budget.  A future adversarial
probe could try to construct a small solver whose accepted region has no such
bounded-coordinate YES-centered structure, or show the counting slack cannot be
met for canonical parameters.

### Does it require new lower-bound content?

Yes.  It is essentially a source theorem for converting hypothetical small-DAG
solvers into a contradiction.  Existing generic wrappers do not supply the
`IsoStrongFamilyEventually` witness.

### Is it close to the original main gap?

Yes.  If established for the canonical anti-checker track and paired with the
NP/TM bridge, it reaches `NP_not_subset_PpolyDAG`.  It is therefore close to the
main DAG lower-bound gap, not merely formula/AC0 side-track work.

### Verdict

**likely_as_hard_as_main_gap**

The route looks non-vacuous, but the required isolation property is so strong
that it is probably close to the central lower-bound obligation rather than a
near-term mechanical bridge.

---

## 7. PromiseYes route audit

### What `PromiseYesSubcubeCertificateAt W` demands

For a concrete small-DAG witness `W`, it demands:

1. one valid YES center `yYes`;
2. a value-coordinate set `S`;
3. direct counting slack against `circuitCountBound p.n (p.sNO - 1)`;
4. one-sided promise acceptance: every valid YES/NO completion agreeing with
   `yYes` on `S` is accepted by `W.C`.

### Does canonical `sYES = 1` make it trivial or impossible?

It does not make it trivially true.  Canonical `sYES = 1` makes the YES side
small-circuit consistency with constants/inputs particularly explicit, and the
canonical decider enumerates `m + 2` size-1 candidates.  But
`PromiseYesSubcubeCertificateAt W` still requires a subcube on which the
specific solver circuit `W.C` accepts all promise-relevant completions agreeing
with the chosen YES center, plus nontrivial counting slack.

It also is not obviously impossible from the definition alone: a solver that is
correct on the promise must accept YES instances, so the center is accepted.
The missing content is the extension from a point to a controlled subcube with
sufficient slack.

### Does it require selecting subcubes with nontrivial density/provenance?

Yes.  The certificate is witness-indexed and semantic.  A source theorem must
select `S` with enough complement budget and prove the solver accepts all
promise-relevant completions agreeing on `S`.  This is exactly where hardwiring,
natural-proof, and provenance-style self-attacks should be aimed.

### Can it be attacked by hardwiring?

The formula-side arbitrary truth-table payload attack does not directly produce
a `PpolyDAG` family witness.  However, a **DAG-side analogue** could attack the
route by producing a small correct solver with an accepted YES set that resists
any bounded-coordinate certificate.  I did not find such an analogue formalized.

### Verdict

**promising_nontrivial**

This is the more concrete route target.  It is not currently refuted and not
obviously trivial, but it needs a focused self-attack/probe around canonical
`sYES = 1`, witness-indexed subcube selection, and small-DAG adversaries.

---

## 8. NoGo cross-check

| NoGo / refutation | Status against these routes | Reason |
| --- | --- | --- |
| PR13 `FormulaCertificateProviderPartial` refutation | **does not apply directly** | The audited route statements do not assume `FormulaCertificateProviderPartial`; they are anti-checker/DAG-side statements. Module-level imports include `LocalityProvider_Partial`, but the statement surfaces are independent. |
| NOGO-000004 `prefixAnd` | **possible analogue** | It warns that syntactic/support filters can be evaded by hardwired shapes. The current routes are semantic DAG/promise subcube routes, so the exact prefix-AND attack is not direct, but the adversarial-witness mindset applies. |
| NOGO-000006 arbitrary `ttFormula` payload | **possible analogue** | Direct formula truth-table hardwiring does not fit `PpolyDAG` asymptotic size bounds, but a DAG-side small-solver payload resisting certificates would be analogous. Needs a targeted probe. |
| NOGO-000008 syntax rewrite | **does not apply directly** | The audited routes do not rely on displayed formula syntax filters. It remains relevant as a warning against future syntactic certificate/provenance side conditions. |
| NOGO-000009 normalisation meta-barrier | **does not apply directly** | The audited routes are not V2-A syntactic-normaliser filters. It is a caution only if a future PromiseYes proof imports syntactic normalisation. |
| Support-bounds refutations | **does not apply directly** | The routes do not consume `FormulaSupportBoundsPartial`, `FormulaSupportBoundsFromMultiSwitchingContract`, or `MagnificationAssumptions`. |
| `MagnificationAssumptions` refutations | **does not apply directly** | The endpoint wrappers explicitly use `AntiCheckerAssumptions`, not the refuted `MagnificationAssumptions` package. |

Overall NoGo status: no listed NoGo directly refutes the route, but the route
is not cleared.  The correct next NoGo-style check is a DAG-side hardwiring or
`hInDag` triviality probe.

---

## 9. Should TMVerifier sessions resume?

**yes_resume_as_np_infrastructure**

Reason: the canonical TM verifier supports the NP pullback/anti-checker package,
which is independent infrastructure.  It should not be advertised as closing
P-vs-NP or as proving the route, but it remains useful for making the canonical
endpoint assumptions concrete.

---

## 10. Recommended next action

**open_promiseYes_route_probe_L0**

Rationale: `PromiseYesSubcubeCertificateAt` is the sharper and more testable
source target.  A Level-0 probe can attack canonical `sYES = 1` subcube
certificates for concrete small DAG witnesses without adding endpoints or
claiming lower-bound progress.

---

## 11. What would count as progress?

A concrete next result that would change route status:

> A Lean probe/report for the canonical `sYES = 1, sNO = 2` family showing one
> of the following:
>
> 1. **Positive:** a theorem that every canonical small-DAG promise witness at
>    the `ppolyDAGSizeBoundOnSlicesEventually` surface yields a
>    `PromiseYesSubcubeCertificateAt W` with explicit `S` and slack, for a
>    nontrivial initial parameter regime; or
> 2. **Negative:** a formal counterexample family of small correct DAG witnesses
>    for which no bounded-coordinate `PromiseYesSubcubeCertificateAt W` can
>    exist; or
> 3. **Triviality:** a theorem deriving the exact route `hInDag` premise for the
>    canonical family from existing P/parser/compiler facts.

The first would move the PromiseYes route toward non-vacuous mainline status.
The second would likely downgrade/close it.  The third would force a re-audit of
both routes for possible vacuity or hardwiring.

---

## Command log

Commands required by the task and used by this audit:

```bash
rg -n "AsymptoticIsoStrongRoute|IsoStrongFamilyEventually|PromiseYesSubcubeCertificateAt|AsymptoticPromiseYesCertificateRoute|AsymptoticPromiseYesWeakRouteEventually" pnp3

rg -n "FormulaCertificateProviderPartial|RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions" pnp3/Magnification pnp3/LowerBounds pnp3/Tests
```

Additional read/search commands used:

```bash
find .. -name AGENTS.md -print
cat AGENTS.md
git status --short --branch
git rev-parse HEAD
git branch --show-current
sed -n '1,220p' RESEARCH_CONSTITUTION.md
find seed_packs -path '*post_pr13*' -type f -maxdepth 5 -print
find seed_packs/asymptotic_isostrong_route_audit_D0 -maxdepth 4 -type f -print
rg -n "provider_retarget|post_pr13|FormulaCertificateProviderPartial" seed_packs pnp3 outputs RESEARCH_CONSTITUTION.md
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '205,430p'
nl -ba pnp3/Magnification/FinalResultMainline.lean | sed -n '1000,1120p'
nl -ba pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean | sed -n '1074,1105p'
nl -ba pnp3/LowerBounds/DAGStableRestrictionProducer.lean | sed -n '2475,2515p'
nl -ba pnp3/Magnification/CanonicalAsymptoticTrackData.lean | sed -n '1,260p'
nl -ba pnp3/Magnification/CanonicalAsymptoticDecider.lean | sed -n '1,220p'
nl -ba pnp3/Tests/CanonicalIntegrationTests.lean | sed -n '1,150p'
rg -n "proved_P_subset_PpolyDAG_internal|P_subset_PpolyDAG_internal|gapPartialMCSP.*_in_P|PartialMCSP.*P" pnp3
nl -ba pnp3/Complexity/Simulation/Circuit_Compiler.lean | sed -n '585,625p'
tail -n 80 outputs/nogolog.jsonl
rg -n "NOGO-000004|NOGO-000006|NOGO-000008|NOGO-000009|FormulaCertificateProviderPartial|support|MagnificationAssumptions" outputs/nogolog.jsonl pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean pnp3/RefutedPredicates/Registry.lean
nl -ba pnp3/RefutedPredicates/Registry.lean | sed -n '111,130p'
nl -ba pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean | sed -n '575,615p'
```

Final validation command:

```bash
./scripts/check.sh
```
