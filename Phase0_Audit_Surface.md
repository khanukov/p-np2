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

These endpoints depend transitively on one of the six refuted predicates
listed in §2. They are mathematically vacuous in the sense of Rule 6 and
must be relocated under `pnp3/Magnification/AuditRoutes/` and renamed
`RefutedRoute_*`.

The list below is **not** exhaustive; a full enumeration is the work
product of Phase 0 PR 3 (`Rename/move direct refuted-route endpoints`).
Representative names from the inventory:

- `NP_not_subset_PpolyFormula_final_with_supportBounds`
- `NP_not_subset_PpolyFormula_final_with_multiswitching`
- `NP_not_subset_PpolyDAG_final_of_supportBounds`
- `P_ne_NP_final_of_supportBounds`
- `P_ne_NP_final_of_magnification`
- `NP_not_subset_PpolyDAG_of_supportBounds`
- `NP_not_subset_PpolyDAG_of_supportBounds_TM`

Estimated count of direct refuted endpoints: **≥ 19**. Final count to be
produced as `outputs/phase0_endpoint_table.csv` during PR 3.

### 1.3 Typeclass-payload-channel endpoints

These live in `pnp3/Magnification/FinalResultAuditRoutes.lean` and
violate Rule 16. They must be quarantined in
`pnp3/Magnification/AuditRoutes/Vacuous_TypeclassChannel.lean` (PR 2)
and renamed `Vacuous_*`:

| Current name                                  | Proposed renamed name                                |
| --------------------------------------------- | ---------------------------------------------------- |
| `P_ne_NP` *(takes `[FinalPayloadProvider]`)*  | `Vacuous_P_ne_NP_via_FinalPayloadProvider`           |
| `P_ne_NP_of_default_formulaSource`            | `Vacuous_P_ne_NP_via_DefaultFormulaSource`           |
| `P_ne_NP_of_default_sources`                  | `Vacuous_P_ne_NP_via_DefaultSources`                 |
| `P_ne_NP_of_constructive_asymptoticData`      | `Vacuous_P_ne_NP_via_ConstructiveAsymptotic`         |

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

- `class FinalPayloadProvider`
  (`pnp3/Magnification/FinalResultAuditRoutes.lean:719`)
- `def hasDefaultAsymptoticFormulaTrackData`
  (`pnp3/Magnification/FinalResultAuditRoutes.lean:740`)
- `def hasDefaultFormulaSupportRestrictionBoundsPartial`
  (referenced in `FinalResultAuditRoutes.lean:775,806,823,824,841`)

Plus references to provider classes:

- `AsymptoticPayloadProvider`
- `FormulaCertificateProviderPartial`
- `FormulaSemanticMultiSwitchingProvider`
- `AC0FamilyWitnessProvider`
- `LocalCircuitFamilyWitnessProvider`
- `AC0MultiSwitchingWitnessProvider`

Phase 0 cleanup must:

1. Move all of these into
   `pnp3/Magnification/AuditRoutes/Vacuous_TypeclassChannel.lean`.
2. Annotate each with one of:
   `@audit-class: refuted-channel`,
   `@audit-class: optional-combinatorial`,
   `@audit-class: infrastructure`.
3. Forbid candidate-local code from using any of them (Rule 16, see
   `spec/implicit_assumption_channels.md`).

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
