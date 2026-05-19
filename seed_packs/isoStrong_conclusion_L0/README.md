# Iso-strong conclusion L0 probe

## 1. Status

**OPEN — L0 Lean probe.**

This is NOT a markdown-only seed pack.  L0 authorises ONE Lean file at
the staging path `pnp3/Tests/IsoStrongConclusionProbe.lean`, ≤ 300 LOC,
under the hygiene constraints in WORKER section 7.

No mainline Lean edits.  No `SourceTheorem`, `ResearchGapWitness`,
`gap_from`, endpoint, or `P ≠ NP` claim.  No trust-root edits.

## 2. Why this exists

The audit chain (most recent first):

1. PR #1407 (`isoStrong_conclusion_audit_D0`, codex53):
   `INCONCLUSIVE_NEEDS_LEAN_PROBE`.  All 4 D0 worker variants
   converged on this verdict.  Markdown audit cannot decide whether
   the conclusion-side `IsoStrongFamilyEventually F (projected hInDag)`
   is trivially provable, refutable, or research-open at canonical
   `sYES = 1, sNO = 2`.
2. PR #1404 (`global_hInDag_contract_L0`, gpt55): landed
   `GlobalAsymptoticDAGWitness` contract + projection
   `globalWitness_to_hInDag`.
3. PR #1396 (`global_hInDag_contract_repair_D0`, codex53):
   proposed the contract.
4. Earlier post-PR13 chain.

After PR #1407, the conclusion-side question requires a Lean probe.
This seed pack opens that probe.

## 3. The two probe directions

The conclusion-side question is whether the body of
`AsymptoticPromiseYesWeakRouteEventually_global canonicalAsymptoticHAsym`
or equivalently `IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`
is provable at canonical `sYES = 1, sNO = 2`.

### Direction P (positive)

Target theorem at staging path:

```lean
theorem isoStrong_conclusion_positive_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)
```

If this lands, the canonical route Prop is provable at canonical,
meaning the route delivers `NP_not_subset_PpolyDAG` from
structurally-trivial content.  **Interpretation: route is vacuous in
the formal sense.**  Canonical track closes as a fourth refutation
pattern in the chain after `FormulaCertificateProviderPartial → False`,
the per-slice hardwiring of L0 #1388, and the contract-but-trivial
observation from L0 #1404.

### Direction N (structural negation)

Target theorem at staging path:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

This is a **structural** negation: for **every** witness `W`, the
conclusion fails.  It does NOT require constructing a concrete `W`
instance (that would be multi-session TM-verifier work, out of L0
scope).  Instead, it requires a structural argument showing that
at canonical sYES=1, sNO=2, no `(yYes, D)` pair satisfies the
forcing condition with the required counting slack, regardless of
which polynomial-size DAG family `W.family` provides.

**Interpretation:** route is **inconsistent** at canonical.
Canonical track closes as a different refutation pattern.

### Note on `∃ W, ¬...`

The narrower target `∃ W, ¬ IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`
also refutes the route, but **requires constructing a concrete `W`** —
which means producing a `GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`
inhabitant.  Since the canonical asymptotic language is in P
(via `decideAsymptotic`), such a `W` exists, but its construction
is the multi-session TM-verifier obligation (~800–1500 LOC).
**This is OUT of L0 scope.**  The L0 may only target the
**universally-quantified** negation in Direction N.

## 4. Strategy guidance

Before writing Lean, the worker should think which direction to
attempt:

### Indicators favouring Direction P (try positive)

- The forcing condition `∀ z, ValidEncoding z ∧ AgreeOnValues D yYes z
  → z ∈ Yes` can be discharged by choosing yYes and D structurally so
  that the agreement subcube is contained in YES.
- If `yYes = encodePartial T_const_false` (encoding of const-false
  partial truth table) and `D = full ValueCoordinateSet`, then by
  `ValidEncoding z = encodePartial (decodePartial z)` plus full
  agreement of value coordinates, `z = yYes`, so trivially `z ∈ Yes`.
  But the slack inequality fails for `|D| = full`.
- The "tradeoff" is between forcing (large D) and slack (small D).
- The slack inequality `m + 2 < 2^(2^m - |D|)` is satisfied for
  `|D| ≤ 2^m - 4` (since `m + 2 ≤ 2^4 = 16` for `m ≤ 14`, growing
  slower than `2^(2^m - |D|)`).  So `|D|` can be very large
  (`≈ 2^m - O(log m)`).
- At very large `|D|`, only `O(log m)` value coordinates are free in
  the agreement subcube.  Whether all valid encodings agreeing on
  the rest are in YES depends on the structure of size-1 functions.

### Indicators favouring Direction N (try negative)

- For canonical `sYES = 1`, there are exactly `m + 2` size-1 Boolean
  functions (`const false`, `const true`, `Circuit.input i` for
  `i : Fin m`).
- The YES set at slice `m` is the union of `m + 2` "consistency
  classes" — partial tables consistent with one of these `m + 2`
  functions.
- For any yYes ∈ YES (say consistent with size-1 function f), the
  agreement subcube contains partial tables that differ from yYes at
  positions outside D.  If `|D| < 2^m`, there exist free positions
  where the value can flip.  Most flips produce partial tables
  inconsistent with f.
- If the free positions allow more than `m + 2` distinct partial
  tables, then by pigeonhole, some agreement-subcube member is not
  in YES.
- Number of distinct agreement-subcube members = `2^(2^m - |D|)`
  (free value coordinates) × number of valid mask configurations.
- For slack `m + 2 < 2^(2^m - |D|)`, by pigeonhole, at least one
  agreement-subcube member is not in YES.
- This SUGGESTS Direction N has a clean structural argument.

The Direction N argument seems more tractable structurally.  Worker
may want to try Direction N first.

## 5. Possible verdicts

End the L0 report with **exactly one** of:

- **`GREEN_CONCLUSION_PROVEN`** — Direction P landed kernel-checked.
  Route is formally vacuous at canonical.  Canonical track closes
  as fourth refutation pattern.
- **`RED_CONCLUSION_REFUTED`** — Direction N landed kernel-checked.
  Route is formally inconsistent at canonical.  Canonical track
  closes inconsistent.
- **`YELLOW_PARTIAL_LANDING`** — A partial Lean result landed (e.g.,
  proof for fixed small `n` slices, or under an extra hypothesis,
  or a key sub-lemma toward Direction N) but the full probe theorem
  does not fit in 300 LOC.  Report identifies the specific L1
  sub-targets.
- **`INCONCLUSIVE_NEEDS_L1`** — No Lean theorem lands.  Report
  identifies the specific blocking lemmas and infrastructure for L1
  multi-session probe.

## 6. Anti-hardwiring caveat

The probe must NOT rely on:

- Truth-table hardwiring of `W.family` (per the L0 #1388 result,
  this is the per-slice hardwiring that the global contract was
  designed to block).
- Constructing concrete `W` via Classical.choice on a non-effective
  existential (would smuggle in unbounded power).
- Importing or referencing refuted predicates (per Rule 16).

The probe SHOULD use:

- Generic `W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`
  as an opaque input (do not unfold W's fields beyond
  `W.size_bound` and `W.decides_global` as needed).
- Canonical `sYES = 1, sNO = 2` numeric facts.
- Standard mathlib Nat / pigeonhole / counting lemmas.

## 7. Audit targets (read-only context)

- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually` — the conclusion under audit).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:25–35`
  (`GapSlice`, `CorrectOnPromiseSlice`, `gapSliceOfParams`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:70–104`
  (`GapSliceFamilyEventually`, `encodedLen`, `tableLen`).
- `pnp3/LowerBounds/MCSPGapLocality.lean:148–165`
  (`ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (canonical spec, params, hAsym; `canonicalShannonBound`).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the L0 contract:
  `GlobalAsymptoticDAGWitness`, `globalPolyDAGSizeBound`,
  `AsymptoticPromiseYesWeakRouteEventually_global`,
  `globalWitness_to_hInDag`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `gapPartialMCSP_AsymptoticLanguage`,
  `partialInputLen`, `Partial.tableLen`, `circuitCountBound`,
  `Promise.Yes/No`).
- `seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_codex53.md`
  (the D0 report that motivated this L0).

## 8. Forbidden scope

- No edits outside `pnp3/Tests/IsoStrongConclusionProbe.lean` and
  the seed pack's `reports/` + `failures/` directories.
- No mainline Lean edits.
- No imports of `Magnification.LocalityProvider_Partial`,
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, or any
  file under `pnp3/RefutedPredicates/`.
- No `axiom`, `opaque` (unless using `Classical.choice` on a
  strictly bounded existential, justified in docstring), `Fact`,
  `Provider`, `Payload`, `Default`, `Source`, `Witness`, `Gap` in
  declaration names other than the unavoidable
  `GlobalAsymptoticDAGWitness` parameter type (per the L0 #1404
  exception clause carried forward).
- No `sorry`, `admit`, `native_decide`.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## 9. Allowed scope

- ONE Lean file at `pnp3/Tests/IsoStrongConclusionProbe.lean`,
  ≤ 300 LOC.
- ONE markdown report at
  `seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_<HANDLE>.md`.
- Optional failure notes under
  `seed_packs/isoStrong_conclusion_L0/failures/`.
