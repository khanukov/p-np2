# post-PR13 provider retarget — D0

## 1. Status

**D0 only.**  This seed pack is markdown-only.  It does not introduce Lean
code, a source theorem, a bridge, a `ResearchGapWitness`, an endpoint, or a
`P ≠ NP` claim.

A full Round 1 is **NOT** authorised here.  Whether any Round-1 design
follows is decided by the operator after reading D0 reports.

## 2. Why post-PR13 retarget exists

PR 13 audit landed (commit `1e0454f`).  It records the refutation theorem

```
Probe 13 : FormulaCertificateProviderPartial → False
```

(see `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`,
`false_of_FormulaCertificateProviderPartial`).

This means every downstream consumer of `FormulaCertificateProviderPartial`
is an ex-falso wrapper:

- `i4_final_wiring_of_formulaCertificate`
  (`pnp3/Tests/BridgeLocalityRegression.lean`)
- `structuredLocalityProviderPartial_of_formulaCertificate`
  (`pnp3/Magnification/LocalityProvider_Partial.lean:3225`)
- `dag_stableRestrictionGoal_of_formulaCertificate`
  (`pnp3/LowerBounds/SingletonDensityContradiction.lean:2210`)
- `dag_stableRestriction_producer_of_formulaCertificate`
  (`pnp3/LowerBounds/SingletonDensityContradiction.lean:2228`)

The 7-session TM-verifier construction plan
(`pnp3/Docs/TMVerifier_Session_Plan.md`) was scoped against
`canonicalAsymptoticSpec` and routed through
`i4_final_wiring_of_formulaCertificate`.  After PR 13 that final wiring is
ex-falso.

But the canonical asymptotic infrastructure itself (PR #1366 +
`CanonicalAsymptoticTrackData.lean` + `CanonicalAsymptoticDecider.lean`)
does not import `FormulaCertificateProviderPartial`.  It may still be
reusable if retargeted onto a non-refuted downstream consumer.

This seed pack opens exactly one D0 slot:

**D0 — Provider retarget feasibility audit.**

D0 may write one feasibility report under `reports/`.  No Lean code, JSONL,
spec, guard, trust-root, theorem-promotion, endpoint, or Round-1 work is
authorised here.

## 3. D0 central question

After PR 13, is there a non-refuted downstream consumer of the canonical
asymptotic infrastructure that:

1. avoids `FormulaCertificateProviderPartial`;
2. avoids universal quantification over arbitrary `PpolyFormula` witnesses;
3. survives the existing hardwiring NoGo family
   (NOGO-000004, NOGO-000006, NOGO-000008, NOGO-000009);
4. directly produces `ComplexityInterfaces.NP_not_subset_PpolyDAG`
   (rather than the refuted `NP_not_subset_PpolyFormula` cone);
5. has at least one hypothesis surface that is research-level open
   (not vacuously satisfied and not formally refuted)?

If the answer is yes, the canonical infrastructure is **reusable** and a
follow-up D0 should formally audit that consumer's hypothesis surface.

If the answer is no, the canonical asymptotic track is closed and the
7-session TM-verifier plan should be retired.

## 4. D0 possible verdicts

Exactly one of:

- **RETARGET_EXISTING_ROUTE** — a non-refuted consumer exists; the
  canonical infrastructure should be replumbed onto it.
- **DESIGN_NEW_PROVIDER** — no usable existing consumer; a new
  provider contract must be designed (D0 sketch only, no Lean).
- **CLOSE_CANONICAL_ROUTE** — no usable consumer is even sketchable;
  the canonical track is closed and the 7-session TM-verifier plan
  retires.
- **INCONCLUSIVE_NEEDS_MORE_AUDIT** — D0 cannot decide; escalate to
  operator with a list of unaudited surfaces.

## 5. D0 required outputs

D0 must produce a report at:

```text
seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_<HANDLE>.md
```

Replace `<HANDLE>` with the worker handle.

## 6. Forbidden scope

- No Lean code.
- No source edits.
- No JSONL edits.
- No `NoGoLog` edits.
- No `known_guards` edits.
- No spec edits.
- No `ResearchGapWitness`.
- No `VerifiedNPDAGLowerBoundSource` construction.
- No `SourceTheorem`.
- No `gap_from`.
- No endpoint.
- No `P ≠ NP` claim.

## 7. Allowed scope

Only:

- This `README.md`
- `WORKER_PROMPT_D0.md`
- One report per worker in `reports/`
- Failure notes in `failures/`
