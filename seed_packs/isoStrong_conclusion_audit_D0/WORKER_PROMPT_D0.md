# Worker prompt — iso-strong conclusion audit D0

Branch: `main` (base).  Develop on a worker branch.

Task type: **markdown-only D0 audit**.  Do not write Lean code.

## Context

Audit chain so far (most recent first):

1. PR #1404 (`global_hInDag_contract_L0`, gpt55): landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with
   `GlobalAsymptoticDAGWitness`, `globalPolyDAGSizeBound`,
   `AsymptoticPromiseYesWeakRouteEventually_global`,
   `globalWitness_to_hInDag` projection.
2. PR #1396 (`global_hInDag_contract_repair_D0`, codex53):
   `REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS`.  Proposed the contract.
3. PR #1388 (`hInDag_triviality_probe_L0`, gpt55): landed
   `pnp3/Tests/HInDagTrivialityProbe.lean` (121 LOC) showing
   per-slice hardwiring satisfies the original `∀ hInDag` quantifier.
4. Earlier chain: PR 13 (`FormulaCertificateProviderPartial → False`),
   post-PR13 retarget D0, asymptotic iso-strong audit D0, hInDag
   triviality D0.

After PR #1404, the contract repair is in main.  The **hypothesis-side**
question is settled (the global witness suffices to block hardwiring).

This task audits the **conclusion-side**: under the global contract at
canonical `sYES = 1, sNO = 2`, does the route's conclusion
(`IsoStrongFamilyEventually F (projected hInDag)` or equivalently the
body of `AsymptoticPromiseYesWeakRouteEventually_global
canonicalAsymptoticHAsym`) carry research-meaningful content, or
does it collapse to a trivially-true / refutable statement?

## Goal

Produce **exactly one** markdown report at:

```text
seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_<HANDLE>.md
```

Replace `<HANDLE>` with your worker handle (e.g. `gpt55`, `codex`,
`opus47`, `codex53`).

If the conclusion-side audit cannot be completed in markdown, file a
short failure note under `failures/` AND issue the verdict
`INCONCLUSIVE_NEEDS_LEAN_PROBE` with a precise probe target.

## Central question

Under `AsymptoticPromiseYesWeakRouteEventually_global
canonicalAsymptoticHAsym` (defined in
`pnp3/Tests/GlobalHInDagContractProbe.lean`), the conclusion-side
asks: for every `W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`,
there exist `ε β0 > 0` and threshold `n0 ≥ N0` such that for all
sufficiently large `n ≥ n0` and sufficiently small `β`, the
predicate `SmallDAGImpliesPromiseYesSubcubeAtEventually F
(globalPolyDAGSizeBound W) n β ε` holds.

`SmallDAGImpliesPromiseYesSubcubeAtEventually` unfolds (per
`AsymptoticDAGBarrierTheorems.lean:985–1004`-ish vicinity) to a
condition involving every DAG `C` with
`globalPolyDAGSizeBound W n β ε (size C)` (i.e., `size C ≤
W.coeff * encodedLen^W.exponent + W.coeff`) and
`CorrectOnPromiseSlice C (gapSliceOfParams (paramsOf n β))`,
producing a YES-isolated subcube structure (`PromiseYesSubcubeAt`,
`SmallDAGImpliesPromiseYesSubcubeAt`).

**Equivalent reformulation** (the cleaner version, since the L0 landing
provides a projection):

Under `IsoStrongFamilyEventually F (globalWitness_to_hInDag W)` for
natural `W` (where "natural" means
`W.family N` is the polynomial-size DAG family compiled from
`decideAsymptotic`, polynomial-time decider for the canonical
asymptotic language):

For every polynomial-size DAG `C : DagCircuit (2 · 2^m)` correct on
the canonical promise at slice `m`, does the prover always succeed
at constructing:

- A YES center `yYes ∈ Yes ∧ ValidEncoding yYes`;
- A coordinate set `D : Finset (Fin (2^m))` with `|D| ≤ κ m β`;
- such that every `z : Bitstring (2 · 2^m)` with `ValidEncoding z ∧
  AgreeOnValues D yYes z` satisfies `z ∈ Yes`;
- AND `m + 2 < 2^(2^m - κ m β)` (the counting slack for canonical
  `sYES = 1, sNO = 2`)?

## Required reading

Before writing the report, read:

- `RESEARCH_CONSTITUTION.md` (Rules 0, 1, 6).
- `STATUS.md`.
- `seed_packs/isoStrong_conclusion_audit_D0/README.md` (this seed
  pack's README — sections 3, 4, 5 are essential).
- `seed_packs/global_hInDag_contract_L0/reports/L0_global_contract_codex53.md`
  (the L0 landing report that motivated this D0).
- `seed_packs/global_hInDag_contract_repair_D0/reports/D0_global_hInDag_contract_repair_codex53.md`
  (the D0 contract proposal).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually` — the definition under audit).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–1075`
  (`ppolyDAGSizeBoundOnSlicesEventually`,
  `SmallDAGSolverEventually`, `SmallDAGImpliesPromiseYesSubcubeAtEventually`
  and immediate context).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:70–110`
  (`GapSliceFamilyEventually`, `encodedLen`, `tableLen`).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (`canonicalAsymptoticSpec` with `sYES = 1, sNO = 2`,
  `canonicalAsymptoticParams`, `canonicalAsymptoticHAsym`).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the L0 contract).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `gapPartialMCSP_AsymptoticLanguage`,
  `partialInputLen`, `Partial.tableLen`, `circuitCountBound`,
  `GapPartialMCSPPromise.Yes/No`, `ValidEncoding`).
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
  (especially `ValueCoordinateSet`, `AgreeOnValues`, the promise-YES
  structures around `PromiseYesSubcubeAt` /
  `PromiseYesSubcubeCertificateAt`).
- `pnp3/Magnification/FinalResultMainline.lean:218–460`
  (the three asymptotic routes, the certificate-route-to-iso-strong
  conversion, the eventual-weak-route-to-certificate conversion).

If any required reading path is missing on the worker checkout,
record that fact in the report and continue from available context.

## Required report sections

The report must include all of these sections, in this order:

1. **Executive verdict** — exactly one of
   `GREEN_CONCLUSION_PROVABLE_FOR_TRIVIAL_REASONS`,
   `RED_CONCLUSION_REFUTABLE`,
   `YELLOW_CONCLUSION_RESEARCH_OPEN`,
   `INCONCLUSIVE_NEEDS_LEAN_PROBE`.
2. **Required-reading inventory** — files read; files missing.
3. **Conclusion statement under audit** — the exact Lean statement
   (full Lean quote of
   `IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`
   unfolded; OR the body of
   `AsymptoticPromiseYesWeakRouteEventually_global
   canonicalAsymptoticHAsym`).
4. **Triviality test (GREEN)** — does a structurally trivial
   construction discharge the conclusion?  Try:
   - `yYes := <encoding of const-false partial truth table>`,
     `D := <some specific subset>`.  Does every agreement extension
     stay in YES?
   - Other trivially-shaped `yYes` candidates.
   - For each attempted construction, identify whether the
     "every agreement extension in YES" condition or the counting
     slack inequality fails.
   - If a trivial construction succeeds: GREEN.
5. **Refutability test (RED)** — can one construct an adversarial
   polynomial-size DAG `C` correct on canonical promise such that no
   YES-isolation with required slack exists?  Try:
   - The compiled `decideAsymptotic` DAG itself.
   - Other polynomial-size correct DAGs.
   - If a counterexample DAG family can be sketched (informally),
     identify whether the obstruction is "no valid `yYes` exists in
     `C`'s accepting set" or "every `D` of valid slack-size has an
     agreement extension outside YES".
   - If RED is confirmed informally: RED.
6. **Combinatorial structure analysis** — independent of GREEN/RED
   above, analyze the combinatorial structure of canonical
   `sYES = 1, sNO = 2`:
   - Number of YES instances at slice `m`: bounded by `m + 2`
     (size-1 functions) × (number of partial-table extensions per
     function).
   - Number of NO instances at slice `m`: complement.
   - Density / overlap structure of YES extensions in
     `Bitstring (2 · 2^m)`.
   - Does the structure favor YES-isolation (GREEN-ish) or block it
     (RED-ish)?
7. **Conclusion vacuity vs research-open classification** — based on
   sections 4–6, classify which verdict applies and why.  If the
   classification cannot be made in markdown, switch to
   `INCONCLUSIVE_NEEDS_LEAN_PROBE` and proceed to section 8.
8. **Lean probe target (only if INCONCLUSIVE)** — if verdict is
   `INCONCLUSIVE_NEEDS_LEAN_PROBE`, specify:
   - The exact Lean theorem statement that would settle the audit
     (positive or negative).
   - Estimated LOC at staging path
     `pnp3/Tests/IsoStrongConclusionProbe.lean`.
   - Which key lemmas / existing repo helpers would be invoked.
9. **Implications for the canonical track** — for each verdict,
   spell out the consequence:
   - GREEN: canonical track closes as inconsistent at conclusion
     level.
   - RED: canonical track closes as inconsistent at conclusion
     level (slightly different reason from GREEN).
   - YELLOW: canonical track is a legitimate research target.
   - INCONCLUSIVE: need L0 Lean probe to advance.
10. **NoGo cross-check** — confirm the verdict does NOT conflict with
    any existing refutation (`FormulaCertificateProviderPartial`,
    `FormulaSupportRestrictionBoundsPartial`,
    `FormulaSupportBoundsFromMultiSwitchingContract`,
    `MagnificationAssumptions[_fromPipeline]`,
    `FormulaSupportBoundsPartial_fromPipeline`).
11. **Scope statement** — explicit confirmation that no mainline
    Lean / spec / JSONL / NoGoLog / known_guards / trust-root edits
    were introduced; no `ResearchGapWitness` / `SourceTheorem` /
    `gap_from` / endpoint / `P ≠ NP` claim.
12. **Commands run** — exact shell commands used during the audit.

## Possible verdicts

End the report with exactly one of:

- **`GREEN_CONCLUSION_PROVABLE_FOR_TRIVIAL_REASONS`** — Conclusion
  derivable for trivial structural reasons.  Closes canonical track
  as formally inconsistent (route Prop derives `NP_not_subset_PpolyDAG`
  from trivially-true conclusion, similar to a hardwiring
  refutation).
- **`RED_CONCLUSION_REFUTABLE`** — Conclusion refutable via an
  explicit (informal-but-parameter-complete) counterexample DAG
  family.  Closes canonical track as inconsistent at conclusion
  level.
- **`YELLOW_CONCLUSION_RESEARCH_OPEN`** — Real research-open
  combinatorial content.  Canonical track is a legitimate target
  for future research.
- **`INCONCLUSIVE_NEEDS_LEAN_PROBE`** — Markdown cannot decide; L0
  Lean probe required.  Report must specify the precise probe
  target.

## Forbidden scope

- No Lean code.
- No edits outside the seed pack.
- No mainline Lean / spec / JSONL / NoGoLog / known_guards / trust-root
  edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  `P ≠ NP` claim.
- No promotion of refuted predicates.
- No TM-verifier session work.

## Allowed scope

- ONE markdown report at the path above.
- Optional failure notes under
  `seed_packs/isoStrong_conclusion_audit_D0/failures/`.

## Commands

```sh
./scripts/check.sh
```

Document the result.  If `check.sh` fails for an environment reason
(e.g., `lake` not installed), record the failure mode and confirm it
reproduces on `main` HEAD.

## Required output format

End the response with:

```
Task: iso-strong conclusion audit D0
Handle: <handle>
Branch: <branch>
Commit before: <hash>
Commit after: <hash>
Changed files:
  seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_<HANDLE>.md
  seed_packs/isoStrong_conclusion_audit_D0/failures/<note>.md (if any)

Outcome:
  REPORT_LANDED | STRUCTURED_FAILURE

If report landed:
  executive verdict: GREEN_CONCLUSION_PROVABLE_FOR_TRIVIAL_REASONS |
                     RED_CONCLUSION_REFUTABLE |
                     YELLOW_CONCLUSION_RESEARCH_OPEN |
                     INCONCLUSIVE_NEEDS_LEAN_PROBE
  L0 probe target (if INCONCLUSIVE): <theorem statement + staging path>
  canonical-track implication: closed_inconsistent | closed_inconsistent_via_refutation |
                                legitimate_research_target | needs_L0_to_decide
  next action:
    if GREEN: open_post_pr13_retarget_v2_D0 (canonical track closed)
    if RED:   open_post_pr13_retarget_v2_D0 (canonical track closed)
    if YELLOW: open_isoStrong_conclusion_full_route_L1 (formalise route)
    if INCONCLUSIVE: open_isoStrong_conclusion_L0_probe
  commands run:

Scope violations:
  none | list
```
