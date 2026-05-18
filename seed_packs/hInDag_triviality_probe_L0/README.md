# hInDag triviality probe — L0

## 1. Status

**OPEN — L0 Lean probe.**

This is **not** a markdown-only seed pack.  L0 authorises one Lean file
at the staging path `pnp3/Tests/HInDagTrivialityProbe.lean`, ≤ 200 LOC,
under the hygiene constraints in section 6 of the worker prompt.

No mainline Lean edits.  No `SourceTheorem`, `ResearchGapWitness`,
`gap_from`, endpoint, or `P ≠ NP` claim.

## 2. Why this exists

The chain so far:

1. PR 13 proved `FormulaCertificateProviderPartial → False` (Probe 13).
2. `seed_packs/post_pr13_provider_retarget_D0` (opus47) recommended
   `RETARGET_EXISTING_ROUTE` onto the DAG-side consumers
   `AsymptoticIsoStrongRoute` and `AsymptoticPromiseYesCertificateRoute`.
3. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55) returned
   `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` and named the
   decisive next probe: `open_hInDag_triviality_probe`.
4. `seed_packs/hInDag_triviality_probe_D0` (gpt55) returned
   `YELLOW_INCONCLUSIVE`: no D0-scope markdown probe can settle the
   question; the blocking construction is

   ```lean
   theorem canonicalAsymptotic_in_P :
     Pnp3.ComplexityInterfaces.P
       (Pnp3.Models.gapPartialMCSP_AsymptoticLanguage
         Pnp3.Magnification.canonicalAsymptoticSpec)
   ```

   or equivalently a concrete `CanonicalAsymptoticVerifierComponents`
   inhabitant.  The repo's TM-Verifier Session Plan estimates this at
   ~800–1500 LOC over 7 sessions — **out of L0 scope**.

This seed pack opens the L0 probe with **two** attack routes:

- **L0-A (preferred, ≤ 200 LOC)**: a direct DAG truth-table hardwiring
  construction at fixed slice — the DAG analogue of the existing
  `fixedSlice_gapPartialMCSP_in_PpolyFormula` in
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:218`.

- **L0-B (out of scope; report-only)**: the `buildCanonicalVerifierComponents`
  multi-session TM construction.  L0 must NOT attempt this.  If the
  worker concludes only L0-B can settle the probe, the verdict is
  `INCONCLUSIVE_NEEDS_FULL_SESSION`.

## 3. The L0-A attack route

### Statement target

The exact theorem the worker should land at
`pnp3/Tests/HInDagTrivialityProbe.lean`:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      ComplexityInterfaces.InPpolyDAG
        (Models.gapPartialMCSP_Language
          ((Magnification.eventualGapSliceFamily_of_asymptotic
              Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

### The construction

For each fixed slice parameter `p := (eventualGapSliceFamily_of_asymptotic
canonicalAsymptoticHAsym).paramsOf n β`, the language
`gapPartialMCSP_Language p` is:

- `false` on every input length `m ≠ partialInputLen p`;
- some specific Boolean function on `Bitstring (partialInputLen p)`.

So the family witnessing `InPpolyDAG (gapPartialMCSP_Language p)` is:

- `family m := constFalseDag m` (the existing private helper at
  `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1399`, which the
  worker can re-define locally) if `m ≠ partialInputLen p`;
- `family (partialInputLen p) := <DNF DAG hardwiring the truth table>`.

The polynomial bound is:

- `polyBound m := 1` if `m ≠ partialInputLen p`;
- `polyBound (partialInputLen p) := <constant K_p ≥ DAG size>`.

The key observation for `polyBound_poly` (the `∃ c, ∀ n, polyBound n ≤
n ^ c + c` clause): for fixed `p`, `partialInputLen p` is a specific
natural number, so `polyBound` returns a fixed natural number at exactly
one input length and `1` everywhere else.  This is bounded by any
`c ≥ K_p`, so the polynomial bound exists trivially with `c := K_p`.

### Why the existing `fixedSlice_gapPartialMCSP_in_PpolyFormula` can't be reused

That theorem lives in `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:218`,
which imports `Magnification.LocalityProvider_Partial` —
the home of `FormulaCertificateProviderPartial` (refuted by PR 13) and
the support-bounds family of refuted predicates.  Importing that file
from a new probe is forbidden by the post-PR13 hygiene policy.

The worker must build a small standalone DAG truth-table construction
in the new file, importing only:

- `Complexity.Interfaces`
- `Models.Model_PartialMCSP`
- `Magnification.CanonicalAsymptoticTrackData`
- `Magnification.CanonicalAsymptoticDecider` (optional, only if the
  decider lemmas help the eval proof)

and **NOT** importing:

- `Magnification.LocalityProvider_Partial`
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
- any file under `pnp3/RefutedPredicates/`
- any other refuted-predicate carrier.

## 4. Critical structural caveat

**L0-A success does NOT imply RED for the iso-strong / promise-YES
routes.**

If the worker successfully lands `hInDag_for_canonicalAsymptoticHAsym`,
the hypothesis surface of every consumer of `canonicalAsymptoticHAsym`
collapses — `∀ hInDag, …` reduces to instantiation at the hardwired
witness.

But the conclusion under the hardwired witness is:

```lean
IsoStrongFamilyEventually
  (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
  hInDag_for_canonicalAsymptoticHAsym
```

and `ppolyDAGSizeBoundOnSlicesEventually F hInDag` derived from the
hardwired `polyBound = K_p` becomes a per-slice constant bound at the
ACTIVE length.  At canonical slice `m`, the active input length is
`N = Partial.inputLen m = 2 · 2^m`, and the truth-table DNF DAG has
size on the order of `2^N · N`, doubly-exponential in `m`.  The "small
DAG" predicate then admits **every** DAG of size `≤ 2^N`, which is
essentially every DAG correctly deciding the language on the canonical
slice (modulo the promise restriction).

So under hardwired `hInDag`, the iso-strong conclusion becomes:

> for every DAG that correctly decides `gapPartialMCSP_Language` on
> the promise at sufficiently large slices, produce a YES center +
> bounded coordinate set + counting slack.

This is a **different, harder** combinatorial obligation than the
original "small polynomial-size DAG" version.  It is neither
automatically true nor automatically false.

The L0 probe report must explicitly address this caveat and choose one
of the following follow-up paths:

1. The structural conclusion under hardwired `hInDag` remains
   research-open → `RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`.
2. The structural conclusion under hardwired `hInDag` is provably
   refutable → `RED_HINDAG_TRIVIAL_AND_CONCLUSION_REFUTED` (this
   would close the iso-strong route entirely).
3. The structural conclusion under hardwired `hInDag` is provably
   easy → `RED_HINDAG_TRIVIAL_AND_CONCLUSION_TRIVIAL` (the route is
   vacuous in the formal sense).
4. The worker cannot decide between (1), (2), (3) in L0 scope →
   `GREEN_HINDAG_TRIVIAL_CONCLUSION_NEEDS_NEW_PROBE`.

L0 does NOT need to discharge the conclusion-side question — only to
land `hInDag_for_canonicalAsymptoticHAsym` and **classify** what the
hardwired witness does to the route Prop.

## 5. Audit targets

Read-only context the worker must inspect:

- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (`canonicalAsymptoticHAsym`, `canonicalAsymptoticParams`)
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `Partial.inputLen`,
  `eventualGapSliceFamily_of_asymptotic`)
- `pnp3/Complexity/Interfaces.lean`
  (`DagCircuit`, `DagGate`, `DagWire`, `InPpolyDAG` struct)
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1399–1411`
  (`constFalseDag` reference implementation)
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:130–165`
  (`ttFormula` recursive truth-table construction — TEMPLATE ONLY;
  do not import)
- `pnp3/Magnification/FinalResultMainline.lean:218–282`
  (`AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`,
  `AsymptoticPromiseYesWeakRouteEventually`)

## 6. Allowed scope

- ONE Lean file: `pnp3/Tests/HInDagTrivialityProbe.lean`, ≤ 200 LOC,
  with the hygiene constraints in WORKER section 7.
- ONE markdown report:
  `seed_packs/hInDag_triviality_probe_L0/reports/L0_hindag_triviality_<HANDLE>.md`.
- Optional failure notes under
  `seed_packs/hInDag_triviality_probe_L0/failures/`.

## 7. Forbidden scope

- No edits to any mainline Lean file outside the staging path.
- No edits to `pnp3/RefutedPredicates/`, `pnp3/Magnification/`,
  `pnp3/LowerBounds/`, `pnp3/Complexity/`, `pnp3/Models/`,
  `pnp3/ThirdPartyFacts/`, `pnp3/Spec/`, or `pnp4/`.
- No imports of `Magnification.LocalityProvider_Partial`,
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, or any
  file under `pnp3/RefutedPredicates/`.
- No `axiom`, `opaque`, `noncomputable def` (unless using `Classical.choice`
  on a strictly bounded existential and explicitly justified),
  `Fact`, `Provider`, `Payload`, `Default`, `Source`, `Witness`, `Gap`
  in any declaration name.
- No `sorry`, `admit`, or `native_decide`.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or
  `P ≠ NP` claim.

## 8. Verdicts

End the report with **exactly one** of:

- **`RED_HINDAG_TRIVIAL_AND_CONCLUSION_TRIVIAL`** — L0-A lands AND the
  worker can show the resulting iso-strong / promise-YES conclusion
  under the hardwired hInDag is itself trivially discharged.  The
  route is vacuous in the formal sense and the canonical asymptotic
  retarget closes.

- **`RED_HINDAG_TRIVIAL_AND_CONCLUSION_REFUTED`** — L0-A lands AND
  the worker can show the resulting conclusion is provably false.
  The route is **inconsistent at the canonical instantiation** and
  must be closed; the post-PR13 retarget verdict must be updated to
  `DESIGN_NEW_PROVIDER` or `CLOSE_CANONICAL_ROUTE`.

- **`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`** — L0-A lands.  The
  hInDag premise is trivial, but the resulting structural conclusion
  is research-open.  The route remains a valid target with a sharpened
  obligation.

- **`GREEN_HINDAG_TRIVIAL_CONCLUSION_NEEDS_NEW_PROBE`** — L0-A lands,
  but the worker cannot decide the conclusion-side question in L0
  scope.  Next: open a new D0/L0 to audit `IsoStrongFamilyEventually`
  / `PromiseYesSubcubeCertificateAt` under the hardwired hInDag.

- **`INCONCLUSIVE_NEEDS_FULL_SESSION`** — L0-A does not fit in 200 LOC,
  or the DNF DAG construction requires substantial infrastructure
  (e.g. `DagCircuit.rename`, gate-index management, eval-correctness
  proofs over recursive constructions).  L0 cannot land
  `hInDag_for_canonicalAsymptoticHAsym`.  Next: a multi-session L1
  Lean probe targeting either L0-A or `buildCanonicalVerifierComponents`.

## 9. Required output sections

The report at
`seed_packs/hInDag_triviality_probe_L0/reports/L0_hindag_triviality_<HANDLE>.md`
must contain:

1. Executive verdict.
2. Required-reading inventory.
3. Statement landed (or attempted) in the staging file.
4. Construction summary (≤ 1 page).
5. Hygiene audit (imports, declarations, no-refuted-predicate proof).
6. Caveat audit (section 4 of this README) — explicit classification
   of what hardwired hInDag does to the route Prop.
7. NoGo cross-check.
8. Verdict-specific consequence (which downstream audits must be
   updated and how).
9. Scope statement.
10. Commands run.
