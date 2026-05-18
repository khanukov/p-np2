# Worker prompt — hInDag triviality probe D0

Branch: `main` (base).  Develop on a worker branch.

Task type: **markdown-first**.  Lean allowed **only** under verdict
`INCONCLUSIVE_NEEDS_LEAN` with the constraints in section "Allowed L0
Lean (conditional)" below.

## Context

The chain so far:

1. PR 13 proved `FormulaCertificateProviderPartial → False` and
   recorded it as `Probe 13` in
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
2. The post-PR13 retarget D0
   (`seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`)
   recommended `RETARGET_EXISTING_ROUTE`: replumb the canonical
   asymptotic infrastructure onto the non-refuted DAG-side consumers
   `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
   `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`.
3. The asymptotic iso-strong / promise-YES non-vacuity D0
   (`seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md`)
   returned `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` and named
   the decisive next probe: `open_hInDag_triviality_probe`.

This worker task **is** that probe.

## Central question

Can

```lean
∀ n β,
  ComplexityInterfaces.InPpolyDAG
    (Models.gapPartialMCSP_Language
      ((Magnification.eventualGapSliceFamily_of_asymptotic
          Magnification.canonicalAsymptoticHAsym).paramsOf n β))
```

be proved in-repo on `main` (commit `72ea5e4` or later) **without**:

- introducing new mainline Lean source files;
- importing any refuted predicate
  (`FormulaCertificateProviderPartial`,
   `FormulaSupportRestrictionBoundsPartial`,
   `FormulaSupportBoundsPartial_fromPipeline`,
   `MagnificationAssumptions[_fromPipeline]`,
   `FormulaSupportBoundsFromMultiSwitchingContract`);
- assuming a hypothesis;
- changing `canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalAsymptoticHAsym`, or any trust-root surface?

## Required reading

Read these files before writing the report.  Do not edit them.

- `RESEARCH_CONSTITUTION.md`
- `STATUS.md`
- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_route_audit_gpt55.md`
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
  (in particular `decideAsymptotic`, `decideAsymptotic_iff`,
  `decideYesAt1`, `findCanonicalSlice` and their `_iff` companions)
- `pnp3/Complexity/Interfaces.lean`
  (definitions of `P`, `NP`, `PpolyDAG`, `PpolyFormula`, `InPpolyDAG`)
- `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`
  (`PpolyStraightLine`, `P_subset_PpolyDAG_of_P_subset_PpolyStraightLine`)
- `pnp3/Complexity/Simulation/Circuit_Compiler.lean`
  (`proved_P_subset_PpolyDAG_internal` and its proof shape)
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `Partial.inputLen`,
  `eventualGapSliceFamily_of_asymptotic`)
- `pnp3/Magnification/FinalResultMainline.lean`
  (definitions of `AsymptoticIsoStrongRoute`,
  `AsymptoticPromiseYesCertificateRoute`,
  `AsymptoticPromiseYesWeakRouteEventually`, lines 218–282)
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
  (Probe 2 truth-table hardwiring + Probe 13 refutation)
- `pnp3/RefutedPredicates/Registry.lean`
- `outputs/nogolog.jsonl` (NOGO-000004, NOGO-000006, NOGO-000008,
  NOGO-000009)

If a required reading path has moved or is absent, record that fact in
the report and continue from available context.

## Goal

Produce **exactly one** report at:

```text
seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_<HANDLE>.md
```

Replace `<HANDLE>` with the worker handle (e.g. `gpt55`, `codex`,
`opus47`).

If the probe verdict is `INCONCLUSIVE_NEEDS_LEAN`, **additionally**
land one Lean file at the staging path

```text
pnp3/Tests/HInDagTrivialityProbe.lean
```

with the constraints in section "Allowed L0 Lean (conditional)" below.

No other repository file may be added or edited.

## Attack routes the report must address

The report must explicitly check or rule out **each** of the three
attack routes below.  All three must be attempted before issuing a
verdict.  A `RED` verdict requires at least one route to close.  A
`GREEN` verdict requires all three to be ruled out with a structural
reason (not "I could not find a theorem").

### Route 1 — P-membership + `proved_P_subset_PpolyDAG_internal`

Goal: prove `ComplexityInterfaces.P (gapPartialMCSP_Language p)` for
every canonical slice `p = ((eventualGapSliceFamily_of_asymptotic
canonicalAsymptoticHAsym).paramsOf n β)`, then chain through the
existing repo bridge

```
proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG
```

to obtain `InPpolyDAG (gapPartialMCSP_Language p)`.

Report sub-tasks:

- Search `pnp3/` for any in-repo theorem of the shape
  `ComplexityInterfaces.P (gapPartialMCSP_Language _)` or
  `ComplexityInterfaces.P (gapPartialMCSP_AsymptoticLanguage _)`.
  Cite file + line + exact statement, or record absence.
- Locate the exact bridge: which intermediate predicate
  (`P_subset_PpolyStraightLine`?) does the in-repo compiler require?
  Cite file + line.
- Estimate the gap: how many Lean lines would close the chain if a
  `decideAsymptotic`-based decider proof were added?

### Route 2 — canonical decider + P-to-DAG compiler

Goal: feed `Magnification.decideAsymptotic` (with
`decideAsymptotic_iff` for correctness) into the existing P-to-DAG
compiler.

Report sub-tasks:

- Identify the compiler's exact input shape (TM, straight-line
  program, `Decidable` instance, or other) and confirm whether
  `decideAsymptotic` already satisfies it.
- Verify that `decideAsymptotic`'s implementation is polynomial-time
  on canonical input lengths `N = 2 · 2^m`.  Cite the relevant lemmas
  or note their absence.
- Note that `decideAsymptotic` returns `false` off canonical lengths
  (per `decideAsymptotic_of_not_canonical`), which means the compiler
  must handle the off-canonical case via the same path as the trivial
  constant-false circuit.

### Route 3 — direct algorithmic argument from `sYES=1, sNO=2`

Heuristic record (worker must validate or refute):

- `canonicalAsymptoticSpec` sets `sYES n = 1`, `sNO n = 2`.
- `decideYesAt1 m T` at
  `pnp3/Magnification/CanonicalAsymptoticDecider.lean:107` checks
  consistency of a partial truth table `T` against each of `m + 2`
  size-1 circuit candidates:
  - `Circuit.const false`,
  - `Circuit.const true`,
  - `Circuit.input i` for `i : Fin m`.
- Each consistency check is `O(2^m)` bit operations on the partial
  table (one pass over the table's `2^m` rows checking the candidate
  output against the partial value).
- Canonical input length at slice `m` is `N = Partial.inputLen m =
  2 · 2^m` (= 2 × table-length for the partial table encoding).
- Total decider work: `(m + 2) · 2^m + O(1)` bit operations =
  `O(N · log N)` measured in `N`, i.e. **polynomial in `N`**.
- `decideAsymptotic` at off-canonical lengths returns `false` in
  `O(N)` (via `findCanonicalSlice`).

Report sub-task: confirm or refute the polynomial-time argument above
by tracing the actual Lean implementation of `decideAsymptotic`
and `decideYesAt1`.  If polynomial-time is confirmed, identify the
**exact missing intermediate theorem** between
"`decideAsymptotic` is poly-time" and `InPpolyDAG
(gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec)`.

If that intermediate theorem already exists in the repo, the probe
closes RED.  If it does not exist but is a small addition (≤ 200 LOC),
the probe should escalate to `INCONCLUSIVE_NEEDS_LEAN` and propose
the minimal addition.  If the intermediate theorem requires
substantive new mathematics, the probe closes YELLOW.

## Required report sections

The report must contain all of these sections, in this order:

1. **Executive verdict** — exactly one of `RED_HINDAG_TRIVIALLY_PROVABLE`,
   `GREEN_HINDAG_NOT_TRIVIALLY_PROVABLE`, `YELLOW_INCONCLUSIVE`,
   `INCONCLUSIVE_NEEDS_LEAN`.
2. **Required-reading inventory** — what was read; what was missing.
3. **Statement under test** — quote the exact Lean type of the
   `hInDag` family at the canonical instantiation, with all module
   paths fully qualified.
4. **Route 1 audit** — P-membership + compiler bridge.
5. **Route 2 audit** — canonical decider + compiler.
6. **Route 3 audit** — direct algorithmic argument from `sYES=1, sNO=2`.
7. **Cross-route synthesis** — which routes close, which do not, and
   the precise missing intermediate theorems for those that do not.
8. **NoGo cross-check** — does any of the existing refutations
   (PR 13, NOGO-000004/6/8/9) restrict the attack routes?
9. **Verdict-specific consequence** —
   - if `RED`: which downstream verdicts must be updated and how
     (post-PR13 retarget, iso-strong audit, STATUS.md, TM-verifier
     plan);
   - if `GREEN`: confirmation that the promise-YES L0 probe is now
     the next work item;
   - if `YELLOW`: which specific Lean construction would settle the
     probe and why it is out of D0 scope;
   - if `INCONCLUSIVE_NEEDS_LEAN`: the exact theorem statement, the
     staging file path, and a kernel-checked sketch.
10. **Scope statement** — explicit confirmation that no mainline Lean
    source / spec / JSONL / NoGoLog / known_guards / trust-root /
    `ResearchGapWitness` / `SourceTheorem` / `gap_from` / endpoint /
    `P ≠ NP` claim was introduced.
11. **Commands run** — exact shell commands used during the probe.

## Allowed L0 Lean (conditional)

Only under verdict `INCONCLUSIVE_NEEDS_LEAN` may the worker land one
Lean file at:

```text
pnp3/Tests/HInDagTrivialityProbe.lean
```

Constraints on that file:

- ≤ 200 source lines.
- No `axiom`, `opaque`, `noncomputable def`, `Fact`, `Provider`,
  `Payload`, `Default`, `Source`, `Witness`, `Gap` in any declaration
  name (per `RESEARCH_CONSTITUTION.md` Rule 16).
- No `sorry`, no `admit`, no `native_decide` (per
  `RESEARCH_CONSTITUTION.md` Rule 1 + repo hygiene).
- Imports must NOT include any refuted predicate's home module
  (`Magnification.LocalityProvider_Partial` may NOT be imported, since
  it would transitively bring in `FormulaCertificateProviderPartial`;
  use `Magnification.CanonicalAsymptoticTrackData` /
  `CanonicalAsymptoticDecider` directly).
- The file must compile with `./scripts/check.sh` and must NOT modify
  any other file.
- The file must contain exactly one named theorem of the form

  ```
  theorem hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β, InPpolyDAG (gapPartialMCSP_Language
      ((eventualGapSliceFamily_of_asymptotic
          canonicalAsymptoticHAsym).paramsOf n β))
  ```

  or a clearly-named negative companion theorem that the worker
  proves cannot be established and explains why.

## Forbidden scope

- No mainline Lean source edits (anywhere outside the conditional
  staging file above).
- No JSONL edits.
- No `NoGoLog` edits.
- No `known_guards` edits.
- No spec edits.
- No trust-root edits.
- No `ResearchGapWitness`.
- No `VerifiedNPDAGLowerBoundSource` construction.
- No `SourceTheorem`.
- No `gap_from`.
- No endpoint.
- No `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## Allowed scope

- One markdown report under `seed_packs/hInDag_triviality_probe_D0/reports/`.
- Failure notes under `seed_packs/hInDag_triviality_probe_D0/failures/`.
- Conditionally on verdict `INCONCLUSIVE_NEEDS_LEAN`: one L0 Lean
  file at the staging path above, under the listed constraints.

## Commands

Run:

```sh
./scripts/check.sh
```

If the check fails for an environment reason (e.g. `lake` not
installed in the worker sandbox), record the exact command, exit
status, and observation in `failures/`.  Confirm that the same
failure reproduces on `main` HEAD to establish it is not a regression.

## Required output format

End the response with:

```text
Task: hInDag triviality probe D0
Handle: <handle>
Branch: <branch>
Commit before: <hash>
Commit after: <hash>
Changed files:
  <file>
  ...

Outcome:
  REPORT_LANDED | STRUCTURED_FAILURE

If report landed:
  report path: seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_<HANDLE>.md
  executive verdict: RED_HINDAG_TRIVIALLY_PROVABLE | GREEN_HINDAG_NOT_TRIVIALLY_PROVABLE | YELLOW_INCONCLUSIVE | INCONCLUSIVE_NEEDS_LEAN
  closing route, if RED: Route 1 | Route 2 | Route 3 | multiple
  blocking missing theorem, if YELLOW or NEEDS_LEAN: <theorem statement>
  L0 Lean file landed, if NEEDS_LEAN: pnp3/Tests/HInDagTrivialityProbe.lean
  next action:
    if RED: open_post_pr13_retarget_v2_D0
    if GREEN: open_promiseYes_route_probe_L0
    if YELLOW: open_hInDag_triviality_probe_L0
    if NEEDS_LEAN: review L0 file, then re-run downstream audits
  commands run:

Scope violations:
  none | list
```
