# Iso-strong conclusion audit D0

## 1. Status

**OPEN — D0 audit only.**

This seed pack is markdown-only.  No Lean code.  No source edits.  No
`SourceTheorem`, `ResearchGapWitness`, `gap_from`, endpoint, or
`P ≠ NP` claim.

## 2. Why this exists

The audit chain so far:

1. PR 13 / Probe 13: `FormulaCertificateProviderPartial → False`.
2. `seed_packs/post_pr13_provider_retarget_D0` (opus47): `RETARGET_EXISTING_ROUTE`.
3. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55, PR #1378): `YELLOW`.
4. `seed_packs/hInDag_triviality_probe_D0` (gpt55, PR #1383): `YELLOW_INCONCLUSIVE`.
5. `seed_packs/hInDag_triviality_probe_L0` (gpt55, PR #1388):
   `RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`.  Landed
   `pnp3/Tests/HInDagTrivialityProbe.lean` — per-slice truth-table DAG
   hardwiring satisfies the original `∀ hInDag, ...` quantification.
6. `seed_packs/global_hInDag_contract_repair_D0` (codex53, PR #1396):
   `REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS`.  Proposed
   `GlobalAsymptoticDAGWitness` structure carrying a single shared
   `(coeff, exponent)` polynomial bound.
7. `seed_packs/global_hInDag_contract_L0` (gpt55, PR #1404):
   `RED_GLOBAL_CONTRACT_CORE_LANDED`.  Landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with all four
   pieces: `GlobalAsymptoticDAGWitness`, `globalPolyDAGSizeBound`,
   `AsymptoticPromiseYesWeakRouteEventually_global`,
   `globalWitness_to_hInDag` forward projection.

After PR #1404, the hardwiring loophole is structurally closed at the
contract level.  The next question is **conclusion-side**: even with
the global contract in place, what does the route's conclusion
(`IsoStrongFamilyEventually F (projected hInDag)` or equivalently
the body of `AsymptoticPromiseYesWeakRouteEventually_global`) actually
reduce to at the canonical instantiation?

This seed pack opens that audit.  It is the **third strategic
question** in the post-PR13 chain:

- Q1 (closed in L0 #1388): is the hypothesis `hInDag` non-trivially
  restrictive? ⇒ NO, hardwiring satisfies it.
- Q2 (closed in D0 #1396 + L0 #1404): can the hypothesis be repaired
  to be non-trivial via global contract? ⇒ YES, the
  `GlobalAsymptoticDAGWitness` structure suffices.
- **Q3 (this seed pack): is the conclusion-side non-vacuous and
  research-meaningful under the repaired hypothesis at canonical
  `sYES=1, sNO=2`?**

## 3. The technical setup

### Definition under audit

`IsoStrongFamilyEventually` at
`pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`:

```lean
def IsoStrongFamilyEventually
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    Prop :=
  ∃ β0 : Rat, 0 < β0 ∧
    ∃ κ : Nat → Rat → Nat,
      ∃ nIso : Rat → Nat,
        -- Conjunct (a): YES-isolation under size bound
        (∀ n β, 0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          ∀ C : DagCircuit (encodedLen F n β),
            ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1 (size C) →
            CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
              ∃ yYes ∈ Yes ∧ ValidEncoding ∧
              ∃ D : Finset (Fin (tableLen F n β)), D.card ≤ κ n β ∧
                ∀ z, ValidEncoding z →
                  AgreeOnValues D yYes z → z ∈ Yes) ∧
        -- Conjunct (b): counting slack
        (∀ n β, 0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) < 2^(tableLen F n β - κ n β))
```

The prover chooses `β0`, `κ`, `nIso`.  Then for every sufficiently large
slice and every "small" correct-on-promise DAG, the prover must
exhibit a YES center `yYes` and a small coordinate set `D` such that
the agreement subcube is entirely in YES, plus a counting slack
inequality.

### Hardwired-by-global-witness setup

For canonical `hAsym := canonicalAsymptoticHAsym` and a
`W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`, the
projection `globalWitness_to_hInDag W` (from PR #1404) gives
`hInDag : ∀ n β, InPpolyDAG (slice n β)` whose `polyBound` at the
active length is `size (W.family activeLen)`, polynomial in
`activeLen = encodedLen F n β` because of `W.size_bound`.

So `ppolyDAGSizeBoundOnSlicesEventually F (globalWitness_to_hInDag W)
n β 1 (size C)` reduces to `size C ≤ size (W.family activeLen)
≤ W.coeff * activeLen^W.exponent + W.coeff`.

"Small DAG correct on promise" then means polynomial-size DAG
deciding the canonical slice correctly.  This is the **genuine
magnification regime** — DAGs of polynomial size in `N = 2 · 2^m`.

### What canonical YES/NO look like at `sYES=1, sNO=2`

- YES instances at slice `m`: partial truth tables consistent with
  some size-1 circuit.  Size-1 circuits are exactly:
  - `Circuit.const false`
  - `Circuit.const true`
  - `Circuit.input i` for `i : Fin m`
  Total: `m + 2` distinct size-1 functions on `m` inputs.
- NO instances at slice `m`: partial truth tables not consistent with
  any size-≤ 2 circuit.

`circuitCountBound m (sNO - 1) = circuitCountBound m 1 = m + 2` for
canonical.  So `Mof n (Tof n β) = m + 2` at canonical (where `m = max n N0`).

The counting slack `m + 2 < 2^(tableLen - |D|) = 2^(2^m - |D|)`
is satisfied for `|D| < 2^m - log_2(m + 2) ≈ 2^m - O(log m)`.  So
`κ n β = 2^m - log_2(m + 2) - 1` (or thereabouts) works for the slack.

But `κ n β` is the bound on `|D|` set by the prover.  The slack is
easy to achieve; the hard part is the YES-isolation conjunct (a).

## 4. Central question

Under the **global** route Prop
`AsymptoticPromiseYesWeakRouteEventually_global canonicalAsymptoticHAsym`,
or equivalently under the original Prop evaluated at the projected
hInDag from a natural `GlobalAsymptoticDAGWitness` instance (where
"natural" means the polynomial-size DAG family compiled from
`decideAsymptotic` via the multi-session TM-verifier plan): what
does the conclusion-side reduce to?

Concretely: at canonical `sYES = 1, sNO = 2`, for every polynomial-size
DAG `C : DagCircuit (2 · 2^m)` that correctly decides
`gapPartialMCSP_Language (canonicalAsymptoticParams m)` on the
promise, can the prover always exhibit a YES center `yYes` and a
coordinate set `D` with `|D| ≤ κ n β` such that:

1. `yYes ∈ Yes` (i.e., yYes is a partial truth table consistent with
   some size-1 circuit);
2. `ValidEncoding yYes`;
3. Every `z` with `ValidEncoding z ∧ AgreeOnValues D yYes z` is in
   `Yes`;
4. AND `m + 2 < 2^(2^m - |D|)`?

## 5. Possible verdicts

End the report with exactly one of:

- **`GREEN_CONCLUSION_PROVABLE_FOR_TRIVIAL_REASONS`** — The conclusion
  is derivable by a structurally trivial construction (e.g., a
  constant `yYes` + small `D` works without needing any property of
  `C` beyond promise-correctness).  This would mean the route Prop is
  trivially true at canonical, and `NP_not_subset_PpolyDAG` would be
  derivable from a structurally-trivial route — which is a
  refutation pattern (third one in the chain after
  `FormulaCertificateProviderPartial → False` and the per-slice
  hardwiring of L0 #1388).  Consequence: canonical track is closed,
  `_global` route is inconsistent at canonical.
- **`RED_CONCLUSION_REFUTABLE`** — There exists a polynomial-size
  DAG `C` correct on canonical promise for which NO YES-isolation
  with the required counting slack exists.  This refutes the
  `_global` route at canonical: `AsymptoticPromiseYesWeakRouteEventually_global
  canonicalAsymptoticHAsym → False`.  Consequence: canonical track
  closed as inconsistent, similar to PR 13's pattern but at the
  conclusion level.
- **`YELLOW_CONCLUSION_RESEARCH_OPEN`** — The conclusion is a
  meaningful combinatorial / circuit-complexity question with no
  obvious resolution from existing repo infrastructure.  Real
  research-open content.  Route is a legitimate research target.
- **`INCONCLUSIVE_NEEDS_LEAN_PROBE`** — D0 markdown cannot decide
  between GREEN/RED/YELLOW; an L0 Lean probe is required to settle.
  Report must identify the precise probe target.

## 6. Audit targets (read-only)

- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually`,
  `SmallDAGImpliesPromiseYesSubcubeAtEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:70–104`
  (`GapSliceFamilyEventually`, `encodedLen`, `tableLen`).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (`canonicalAsymptoticSpec` with `sYES = 1, sNO = 2`;
  `canonicalAsymptoticParams`; `canonicalAsymptoticHAsym`).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the L0-landed
  `GlobalAsymptoticDAGWitness` + `globalPolyDAGSizeBound` +
  `AsymptoticPromiseYesWeakRouteEventually_global` +
  `globalWitness_to_hInDag`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `gapPartialMCSP_AsymptoticLanguage`,
  `partialInputLen`, `Partial.tableLen`,
  `GapPartialMCSPPromise.Yes/No`).
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
  (relevant: `ValueCoordinateSet`, `AgreeOnValues`, the
  promise-YES structures).
- `pnp3/Magnification/FinalResultMainline.lean:218–282`
  (the three routes — `AsymptoticIsoStrongRoute`,
  `AsymptoticPromiseYesCertificateRoute`,
  `AsymptoticPromiseYesWeakRouteEventually`).

## 7. Forbidden scope

- No Lean code.
- No edits outside this seed pack.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## 8. Allowed scope

- One markdown report at
  `seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_<HANDLE>.md`.
- Optional failure notes under `failures/`.
