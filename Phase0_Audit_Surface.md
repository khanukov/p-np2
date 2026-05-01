# Phase 0 Audit Surface

This document is the read-only inventory baseline for the
`p-np2` repository at the start of Research Governance v0.1. It is the
input to Phase 0 cleanup PRs 1–6 (see `RESEARCH_CONSTITUTION.md`).

Baseline commit: `91693ef` (branch
`claude/research-governance-phase0-lmZBP` cut from main analysis).

This file does **not** modify any Lean code. It only records what
exists, what is canonical, what is refuted, and what must be moved.

---

## 0. Summary

- **Honest unconditional theorem**: **none**. The identifier
  `P_ne_NP_unconditional` is mentioned in comments and documentation but
  is **not defined as a closed term** anywhere in the active source tree.
- **Canonical research-gap port**:
  `pnp3/Magnification/UnconditionalResearchGap.lean`. It defines
  `ResearchGapTarget := ComplexityInterfaces.NP_not_subset_PpolyDAG` and
  the structure `ResearchGapWitness` whose only field is
  `dagSeparation : ResearchGapTarget`.
- **Refuted predicates**: 6 predicates have been formally proved
  `→ False` in `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- **Active typeclass-payload channel**: `FinalPayloadProvider` and the
  associated `Fact has...` instances in
  `pnp3/Magnification/FinalResultAuditRoutes.lean` provide a vacuous /
  refuted-shaped path to `P_ne_NP` that violates Rule 16. This is the
  primary attack vector that Phase 0 must close.
- **Suspicious endpoints**: ~80 final-looking declarations route
  transitively through refuted predicates or the typeclass-payload
  channel. None of them is a real unconditional theorem.

The repository must be treated as **not having an unconditional proof of
P ≠ NP**. Public claims to the contrary are governed by Rule 1.

---

## 1. Public final-looking endpoints

### 1.1 Canonical (honest) endpoints

These endpoints take a `ResearchGapWitness` argument explicitly. They are
not vacuous: they faithfully express "if the gap is closed, the final
target follows".

| Endpoint                                         | File                                                   |
| ------------------------------------------------ | ------------------------------------------------------ |
| `NP_not_subset_PpolyDAG_final`                   | `pnp3/Magnification/UnconditionalResearchGap.lean`     |
| `P_ne_NP_final`                                  | `pnp3/Magnification/UnconditionalResearchGap.lean`     |
| `P_ne_NP_of_researchGap`                         | `pnp3/Magnification/UnconditionalResearchGap.lean`     |
| `P_ne_NP_final_dag_only` *(no `gap` arg, but takes `NP_not_subset_PpolyDAG`)* | `pnp3/Magnification/UnconditionalResearchGap.lean` |

All four are honest: they admit a hypothesis that nobody currently knows
how to discharge.

### 1.2 Direct refuted-route endpoints

**PR 3 status: rename-in-place complete.** All final-looking endpoints
whose direct premise is one of the six refuted predicates listed in §2
have been renamed with the explicit `RefutedRoute_*` prefix. Physical
relocation under `pnp3/Magnification/AuditRoutes/` is deferred to a
later split PR (alongside PR 2b).

Endpoints renamed in PR 3:

| File                                                    | Old name                                                         |
| ------------------------------------------------------- | ---------------------------------------------------------------- |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyFormula_final_with_supportBounds`            |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyFormula_final_with_multiswitching`           |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyReal_final_with_supportBounds`               |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyReal_final_with_multiswitching`              |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_of_asymptotic_supportBounds`       |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_with_magnification`                |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_of_asymptoticPullback`             |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_of_multiswitchingData`             |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance` |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_of_magnification`                  |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `P_ne_NP_final_of_asymptoticPullback`                            |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `P_ne_NP_final_of_multiswitchingData`                            |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `NP_not_subset_PpolyDAG_final_of_supportBounds`                  |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `P_ne_NP_final_of_supportBounds`                                 |
| `pnp3/Magnification/FinalResultAuditRoutes.lean`        | `P_ne_NP_final_of_magnification`                                 |
| `pnp3/Magnification/FinalResultLegacyTM.lean`           | `NP_not_subset_PpolyDAG_final_of_supportBounds_TM`               |
| `pnp3/Magnification/FinalResultLegacyTM.lean`           | `P_ne_NP_final_of_supportBounds_TM`                              |
| `pnp3/LowerBounds/SingletonDensityContradiction.lean`   | `NP_not_subset_PpolyDAG_of_supportBounds`                        |
| `pnp3/LowerBounds/SingletonDensityContradiction.lean`   | `NP_not_subset_PpolyDAG_of_supportBounds_TM`                     |

Each row's new name is the old name with the prefix `RefutedRoute_`
prepended. No backwards-compatibility aliases were introduced. All
internal callers and `Tests/AxiomsAudit.lean` /
`Tests/BridgeLocalityRegression.lean` / `Tests/RouteSurfaceAudit.lean`
references have been updated.

Total: **19 endpoints renamed.**

**PR 3b status: closed.** The bare package-based `_final` endpoints
have been quarantined:

| File                                                    | Old name                                          |
| ------------------------------------------------------- | ------------------------------------------------- |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyFormula_final`                |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyFormula_final_fromPipeline`   |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyReal_final`                   |
| `pnp3/Magnification/FinalResultMainline.lean`           | `NP_not_subset_PpolyReal_final_fromPipeline`      |

Each row's new name has the `RefutedRoute_` prefix. The conflicting
policy block in `scripts/check.sh` (formerly lines 222-233) now requires
the renamed `RefutedRoute_*` forms instead of the bare names; the
default-provider-signature block (formerly lines 254-266) was tightened
into a positive ban on bare `theorem NP_not_subset_PpolyFormula_final`
/ `NP_not_subset_PpolyReal_final` declarations in the magnification
surface. Reintroduction is also blocked by Step 6/10's
`scripts/check_refuted_route_quarantine.sh` which now recognises
`_final` and `_final_fromPipeline` as direct-refuted suffixes when the
head is `NP_not_subset_PpolyFormula` or `NP_not_subset_PpolyReal`.
The canonical research-gap final `NP_not_subset_PpolyDAG_final` (with
`gap : ResearchGapWitness` premise) is intentionally outside the
restricted head set and remains canonical.

Out of PR 3 / PR 3b scope (deferred):

- Helper / intermediate lemmas that consume a refuted predicate but do
  not look like a final endpoint (e.g.
  `dag_stableRestrictionGoal_of_supportBounds`,
  `*_of_supportBounds` wrappers in `LocalityProvider_Partial.lean`).
  These will be addressed in PR 4 (`Centralize refuted predicates under
  pnp3/RefutedPredicates/`).
- Provider/composite endpoints (`*_with_provider`, `*_fromPipeline`-on-
  provider, `*_withAntiChecker`, etc.) — separate provider-audit PR.

A regression guard, `scripts/check_refuted_route_quarantine.sh`, is
wired into `scripts/check.sh` as Step 6/10 to prevent reintroduction of
unmarked direct-refuted final endpoints in production code.

### 1.3 Typeclass-payload-channel endpoints

**PR 2 status: rename-in-place complete; physical move deferred to PR 2b.**
These endpoints live in `pnp3/Magnification/FinalResultAuditRoutes.lean`
and violated Rule 16. PR 2 (commit on
`claude/research-governance-phase0-lmZBP`) renamed them in place with
the `Vacuous_*` prefix; the physical move into a dedicated
`pnp3/Magnification/AuditRoutes/Vacuous_TypeclassChannel.lean` is
deferred to PR 2b to avoid a wider import-cycle refactor.

| Old name                                      | Renamed (PR 2)                                       |
| --------------------------------------------- | ---------------------------------------------------- |
| `P_ne_NP` *(took `[FinalPayloadProvider]`)*   | `Vacuous_P_ne_NP_via_FinalPayloadProvider`           |
| `P_ne_NP_of_default_formulaSource`            | `Vacuous_P_ne_NP_via_DefaultFormulaSource`           |
| `P_ne_NP_of_default_sources`                  | `Vacuous_P_ne_NP_via_DefaultSources`                 |
| `P_ne_NP_of_constructive_asymptoticData`      | `Vacuous_P_ne_NP_via_ConstructiveAsymptotic`         |
| `class FinalPayloadProvider`                  | `class VacuousFinalPayloadProvider`                  |
| `instance finalPayloadProvider_of_default_supportBounds` | `instance vacuousFinalPayloadProvider_of_default_supportBounds` |

No backwards-compatibility aliases were introduced. The bare name
`P_ne_NP` no longer occurs as a `theorem` declaration in the
magnification tree; the only remaining definition with that name is the
canonical `def P_ne_NP` in `pnp3/Complexity/Interfaces.lean`.

Defining declarations to follow them out of the public surface:

- `class FinalPayloadProvider` (line 719)
- `def hasDefaultAsymptoticFormulaTrackData` (line 740)
- `def hasDefaultFormulaSupportRestrictionBoundsPartial` (referenced at
  lines 775, 806, 823, 824, 841)
- `instance` declarations that inhabit the above `Fact`s.

Phase 0 PR 2 is a guard: `[FinalPayloadProvider]` must not appear outside
`pnp3/Magnification/AuditRoutes/`, and `Fact
hasDefaultFormulaSupportRestrictionBoundsPartial` must not appear
outside `pnp3/Magnification/AuditRoutes/` or `pnp3/Tests/`.

### 1.4 Suspicious provider/composite endpoints

Estimated ~80 declarations referencing one or more of:

- `FormulaCertificateProviderPartial`
- `FormulaSemanticMultiSwitchingProvider`
- `AC0FamilyWitnessProvider`
- `LocalCircuitFamilyWitnessProvider`
- `AC0MultiSwitchingWitnessProvider`
- `AsymptoticPayloadProvider`

These are **not auto-rejected**. They will be reclassified during PR 8
(`Suspicious endpoint reclassification`). Until then they are treated as
**non-canonical**.

### 1.5 Conditional semantic bridges in `Complexity/Interfaces.lean`

Rough count: **9** semantic-conditional bridges. They are not refuted
routes and are not typeclass channels, but they remain conditional. They
are part of the trust root surface (Rule 0) and will be cross-checked
against `FrozenSpec.lean` once it lands.

---

## 2. Refuted hypotheses and routes

The falsifiability probe in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` formally proves
that the following predicates imply `False`. Any endpoint whose statement
takes one of these as a hypothesis is therefore vacuous.

| Refuted predicate                                  | Theorem of refutation                                                |
| -------------------------------------------------- | -------------------------------------------------------------------- |
| `FormulaSupportRestrictionBoundsPartial`           | `false_of_FormulaSupportRestrictionBoundsPartial` (≈ line 280)       |
| `FormulaSupportBoundsFromMultiSwitchingContract`   | `false_of_FormulaSupportBoundsFromMultiSwitchingContract` (≈ 315)    |
| `MagnificationAssumptions`                         | `false_of_MagnificationAssumptions` (≈ 333)                          |
| `FormulaSupportBoundsPartial_fromPipeline`         | `false_of_FormulaSupportBoundsPartial_fromPipeline` (≈ 401)          |
| `MagnificationAssumptions_fromPipeline`            | `false_of_MagnificationAssumptions_fromPipeline` (≈ 426)             |
| `fixedParams ∧ uniformProvenance`                  | `false_of_fixedParams_and_uniformProvenance` (≈ 532)                 |

The probe also contains a positive lemma
`fixedParams_entails_old_under_uniformProvenance` (≈ 502) which is the
**leak theorem**: it shows precisely how the route collapses into the
refuted predicate. This lemma is what motivates the FixedParams Probe
(see `FixedParams_Probe.md`): we want to find a **strictly weaker**
provenance Π that defeats hardwiring.

---

## 3. Import graph risk

Risk classes for downstream files:

- **Refuted-route imports.** Files under `pnp3/Magnification/` that
  import or transitively reference refuted predicates. Currently:
  - `FinalResult.lean`
  - `FinalResultAuditRoutes.lean`
  - `FinalResultLegacyTM.lean`
  - `FinalResultMainline.lean`
  - `FinalResultWeakRoutes.lean`
  - `Bridge_to_Magnification_Partial.lean`
  - `Facts_Magnification_Partial.lean`
  - `PipelineStatements_Partial.lean`
  - `LocalityInterfaces_Partial.lean`
  - `LocalityLift_Partial.lean`
  - `LocalityProvider_Partial.lean`
  - `AsymptoticDAGCollapse.lean`
  - `AsymptoticFormulaCollapse.lean`

  Phase 0 PR 9 splits this into a thin
  `pnp3/Magnification/FinalResultCanonical.lean` (honest bridges only)
  plus `pnp3/Magnification/AuditRoutes/RefutedRoute_*.lean` and
  `Conditional_*.lean` siblings.

- **Typeclass-payload imports.** Anything importing
  `FinalResultAuditRoutes.lean` inherits the `FinalPayloadProvider`
  channel. PR 2 must add a guard ensuring no file outside
  `pnp3/Magnification/AuditRoutes/` imports `FinalResultAuditRoutes.lean`
  after it is split.

- **Trust-root imports.** `pnp3/Complexity/Interfaces.lean` currently
  delegates `P` to `Internal.PsubsetPpoly.Complexity.P`. Therefore
  `pnp3/Complexity/PsubsetPpolyInternal/` is part of the **current trust
  root**. This is recorded here so the FrozenSpec PR (PR 7) can address
  it explicitly (see `spec/frozen_spec_plan.md` §1).

---

## 4. Frozen target identifiers

(Identical to `spec/target.toml::[frozen_identifiers]`; reproduced here
for human readability.)

```
ComplexityInterfaces.P
ComplexityInterfaces.NP
ComplexityInterfaces.PpolyDAG
ComplexityInterfaces.PpolyFormula
ComplexityInterfaces.NP_not_subset_PpolyDAG
ComplexityInterfaces.P_ne_NP
ResearchGapTarget
ResearchGapWitness
ResearchGapWitness.dagSeparation
FormulaCircuit.size
DagCircuit.size
SAT.encoding
DAG.encoding
decides
recognizes
```

A change to any of these is Foundational, never Candidate.

---

## 5. Hidden payload / typeclass channels (Rule 16 inventory)

Active classes / facts found in the active tree:

- `class VacuousFinalPayloadProvider` (renamed from
  `FinalPayloadProvider` in PR 2;
  `pnp3/Magnification/FinalResultAuditRoutes.lean`).
  Use as a typeclass parameter is now blocked outside the audit/test/
  docs allowlist by `scripts/check_typeclass_payload_quarantine.sh`.
- `def hasDefaultAsymptoticFormulaTrackData`
  (`pnp3/Magnification/FinalResultAuditRoutes.lean`).
  Not renamed in PR 2; flagged for PR 6 (`Provider audit annotations`).
- `def hasDefaultFormulaSupportRestrictionBoundsPartial`
  (defined in `pnp3/Magnification/LocalityProvider_Partial.lean`,
  consumed in `FinalResultAuditRoutes.lean`). Use as
  `[Fact hasDefaultFormulaSupportRestrictionBoundsPartial]` is now
  blocked outside the audit/test/docs allowlist by the same guard.

Plus references to provider classes (deferred to PR 6):

- `AsymptoticPayloadProvider`
- `FormulaCertificateProviderPartial`
- `FormulaSemanticMultiSwitchingProvider`
- `AC0FamilyWitnessProvider`
- `LocalCircuitFamilyWitnessProvider`
- `AC0MultiSwitchingWitnessProvider`

PR 2 status (this commit):

1. Endpoints renamed `Vacuous_*` (see §1.3).
2. Provider class `FinalPayloadProvider` → `VacuousFinalPayloadProvider`.
3. Instance `finalPayloadProvider_of_default_supportBounds` →
   `vacuousFinalPayloadProvider_of_default_supportBounds`.
4. Guard script `scripts/check_typeclass_payload_quarantine.sh` added
   and wired into `scripts/check.sh` as Step 5/9.
5. Bare `theorem P_ne_NP` is now forbidden in `pnp3/Magnification/`
   and `pnp3/LowerBounds/` by part (B) of the same guard.

Still pending after PR 2:

- PR 2b: physical move into
  `pnp3/Magnification/AuditRoutes/Vacuous_TypeclassChannel.lean`.
- PR 6: `@audit-class:` annotations on every provider/typeclass class,
  including `AsymptoticPayloadProvider` and the six provider classes
  listed above.
- Candidate-local enforcement (verifier, PR 5–6 of the constitution
  ordering, see `spec/implicit_assumption_channels.md`).

---

## 6. Candidate surface risks

There are no `pnp3/Candidates/` packages yet. When the directory is
created (after PR 1–6), every package must satisfy:

- Layout: `proof.lean`, `manifest.toml`, `sketch.md`,
  `barrier_certificate.md`, `self_attack.md`.
- No imports from `pnp3/RefutedPredicates/` or
  `pnp3/Magnification/AuditRoutes/`.
- No `class`/`instance`/`opaque`/`Fact` over a frozen-target type.
- `SourceTheorem_<id>` and `gap_from_<id>` rendered with `pp.all` must
  satisfy `spec/implicit_assumption_channels.md`.
- `K_stmt`/`K_exp` checks per `spec/source_theorem_size_policy.md`.

Until the verifier exists (PR 6), candidate intake is closed.

---

## 7. Proposed Phase 0 cleanup plan

(Stub — full description in `RESEARCH_CONSTITUTION.md` § "Implementation
PR order". The below is the order, not the implementation.)

1. **PR 1 — Doc-honesty linter.** Reject Markdown/LaTeX claims of
   unconditional P ≠ NP unless `P_ne_NP_unconditional` exists as a
   closed Lean term.
2. **PR 2 — Quarantine typeclass-payload channel.** Move the four
   endpoints in §1.3 plus their supporting `class`/`Fact` declarations
   into `pnp3/Magnification/AuditRoutes/Vacuous_TypeclassChannel.lean`,
   add the import guard.
3. **PR 3 — Rename/move direct refuted-route endpoints.** Per §1.2.
4. **PR 4 — Centralize refuted predicates** under
   `pnp3/RefutedPredicates/`.
5. **PR 5 — Rule 16 smoke probes and verifier shell.** See
   `bench/SmokeProbe_plan.md`.
6. **PR 6 — Provider audit annotations.** Annotate every provider /
   typeclass class.
7. **PR 7 — FrozenSpec implementation.** See
   `spec/frozen_spec_plan.md`.
8. **PR 8 — Suspicious endpoint reclassification.** Walk the ~80
   endpoints from §1.4 and assign a final class to each.
9. **PR 9 — Split `FinalResultMainline.lean`** into
   `FinalResultCanonical.lean` + audit-route siblings.
10. **PR 10 — FixedParams Probe.** See `FixedParams_Probe.md`.

---

## 8. `needs_review` classifications

The following items are deliberately not assigned a final classification
in this baseline. They are tagged `needs_review` and must be addressed
during PR 8 or a dedicated audit PR.

| Path / object                                       | Tentative class                | Reason                                                                  |
| --------------------------------------------------- | ------------------------------ | ----------------------------------------------------------------------- |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | `conditional-suspicious` | Not canonical; do not use as path to the final theorem before audit.   |
| `pnp3/Magnification/AsymptoticDAGCollapse.lean`     | `conditional-collapse`         | Collapse consequence ≠ contradiction (Rule 8); audit-only until proof. |
| `pnp3/Magnification/AsymptoticFormulaCollapse.lean` | `conditional-collapse`         | Same.                                                                   |
| `pnp3/Magnification/AsymptoticDAGBarrierTheorems.lean` *(if present)* | `barrier-audit-suspicious` | Barrier/audit area; not a source route.                                 |
| `pnp3/Complexity/Interfaces.lean`                   | `semantic-conditional-bridges` | Part of frozen target surface; verify against FrozenSpec.              |
| `pnp3/Magnification/Bypass.lean` *(if present)*     | `barrier-suite / audit`        | Barrier infrastructure, not a candidate source.                         |

These classifications are intentionally conservative: when in doubt, an
endpoint is **not canonical**. Reclassification upward (toward canonical)
requires explicit Foundational PR review.
