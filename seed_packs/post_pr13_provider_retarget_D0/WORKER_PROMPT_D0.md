# Worker prompt — post-PR13 provider retarget D0

Branch: `main` (base).  Develop on a worker branch.

Task type: **markdown-only**.  Do not write Lean code.

## Context

PR 13 has landed and proved:

```
FormulaCertificateProviderPartial → False
```

This means all consumers of `FormulaCertificateProviderPartial` are
ex-falso wrappers.

The 7-session TM-verifier plan for `canonicalAsymptoticSpec` is no longer
a path to unconditional `NP ⊄ P/poly` through
`i4_final_wiring_of_formulaCertificate`.

But the canonical asymptotic infrastructure itself may still be reusable
if retargeted to a non-refuted downstream consumer.

## Required reading

- `RESEARCH_CONSTITUTION.md`
- PR 13 / Probe 13 surface:
  - `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
  - `pnp3/Magnification/LocalityProvider_Partial.lean`
  - `pnp3/Tests/BridgeLocalityRegression.lean`
  - `pnp3/RefutedPredicates/Registry.lean`
  - `STATUS.md`
- Canonical infrastructure:
  - `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  - `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
  - `pnp3/Tests/CanonicalIntegrationTests.lean`
- Prior NoGo context:
  - `outputs/nogolog.jsonl`
  - `NOGO-000001` … `NOGO-000009`

## Goal

Create exactly one report:

```text
seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_<HANDLE>.md
```

If the seed pack skeleton does not yet exist, also create:

```
seed_packs/post_pr13_provider_retarget_D0/README.md
seed_packs/post_pr13_provider_retarget_D0/WORKER_PROMPT_D0.md
seed_packs/post_pr13_provider_retarget_D0/reports/.gitkeep
seed_packs/post_pr13_provider_retarget_D0/failures/.gitkeep
```

No Lean code under any circumstances.

## Report sections

1. **Executive verdict** — exactly one of:
   - `RETARGET_EXISTING_ROUTE`
   - `DESIGN_NEW_PROVIDER`
   - `CLOSE_CANONICAL_ROUTE`
   - `INCONCLUSIVE_NEEDS_MORE_AUDIT`

2. **What PR 13 killed** — explain why
   `FormulaCertificateProviderPartial → False` and list the now ex-falso
   downstream routes (must include
   `i4_final_wiring_of_formulaCertificate`,
   `structuredLocalityProviderPartial_of_formulaCertificate`,
   `dag_stableRestrictionGoal_of_formulaCertificate`,
   `dag_stableRestriction_producer_of_formulaCertificate`).

3. **What PR 13 did NOT kill** — list canonical infrastructure that
   remains sound (must include `canonicalAsymptoticHAsym`,
   `canonicalAsymptoticSpec`, `decideAsymptotic`, `decideAsymptotic_iff`,
   `canonicalAsymptoticNPBridge_of_TM W`,
   `canonicalAntiCheckerAssumptions_of_TM W`).

4. **Existing possible replacement consumers** — audit at minimum:
   - `AsymptoticIsoStrongRoute`
   - `AsymptoticPromiseYesCertificateRoute`
   - any non-refuted WeakRoute / Optional route
   - any SearchMCSP / ContractExpansion route
   - any pnp4 frontier route
   For each: exact theorem name, required hypotheses, whether it avoids
   `FormulaCertificateProviderPartial`, whether it avoids universal
   `PpolyFormula` quantification, known NoGo risk, verdict
   (usable / wrapper / refuted / too vague).

5. **New provider sketch** — only if verdict is `DESIGN_NEW_PROVIDER`.
   Must NOT quantify over arbitrary `PpolyFormula`, must reject
   truth-table hardwiring, must be non-vacuous, must have an explicit
   anti-hardwiring self-test, must not be equivalent to
   `NP_not_subset_PpolyDAG`, must not package `ResearchGapWitness` or
   `VerifiedNPDAGLowerBoundSource`.

6. **Hardwiring audit** — test the proposed route/provider against:
   - NOGO-000004 (prefixAnd)
   - NOGO-000006 (arbitrary all-essential ttFormula payload)
   - NOGO-000008 (syntactic tautological-seed rewrite)
   - NOGO-000009 (normalisation meta-barrier)
   - PR 13 `FormulaCertificateProviderPartial` refutation.

7. **Recommendation on TMVerifier sessions** — exactly one of:
   - `stop_all_TMVerifier_sessions`
   - `continue_only_as_reusable_NP_infrastructure`
   - `continue_if_retarget_found`
   - `continue_full_speed`

8. **Next action** — exactly one of:
   - `open_new_provider_D0`
   - `open_existing_route_audit_D0`
   - `merge_only_documentation_and_stop`
   - `resume_TMVerifier_with_new_consumer`
   - `close_canonical_route`

## Forbidden scope

No Lean code.  No source edits.  No JSONL edits.  No NoGoLog edits.  No
`known_guards` edits.  No spec edits.  No `ResearchGapWitness`.  No
`VerifiedNPDAGLowerBoundSource` construction.  No `SourceTheorem`.  No
`gap_from`.  No endpoint.  No P ≠ NP claim.

## Allowed scope

Only the report / skeleton files above.

## Commands

```sh
./scripts/check.sh
```

## Output format

```
Task: post-PR13 provider retarget D0
Handle:
Branch:
Commit before:
Commit after:
Changed files:

Outcome:
  REPORT_LANDED | STRUCTURED_FAILURE

If report landed:
  report path:
  executive verdict:
  killed routes:
  reusable infrastructure:
  recommended replacement:
  TMVerifier recommendation:
  next action:
  commands run:

Scope violations:
  none | list
```
