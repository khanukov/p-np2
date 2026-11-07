# Publication navigation: direct standalone route and historical tracks

The current researcher entry is the [Conditional Separation source package](conditional_separation/README.md)
(subdirectory `conditional_separation/`), with a [mathematical introduction to R](conditional_separation/PROOF_MAP.md#research-note)
and a [two-root partial-lemma exchange recipe](conditional_separation/README.md#partial-work-across-machines).
The known public starting revision is
[`a86a6ce9720b71a6bd5439c90d86edd6b6bc25b6`](https://github.com/khanukov/p-np2/tree/a86a6ce9720b71a6bd5439c90d86edd6b6bc25b6/conditional_separation);
this documentation follow-up retains that PR1822 ancestry and does not merge it.
For any distributed package, identify the exact reviewed release revision and
complete package inventory; branch names and old CI do not certify new bytes.

| Current standalone surface | Boundary |
|---|---|
| [`OpenProblem.R`](conditional_separation/ConditionalSeparation/OpenProblem.lean) | UNPROVED: one fixed threshold exponent k defeats every polynomial degree of nonuniform DAG promise-search solvers on full tables |
| [`R_iff_original`](conditional_separation/ConditionalSeparation/Equivalence.lean) | Definitional equality of the exact problem, not a lower bound |
| [`close (hR)`](conditional_separation/ConditionalSeparation/Conditional.lean) | Conditional SAME-k/SAME-language Ordinary NP, non-PpolyDAG and non-Ordinary-P conclusion; no legacy ContentVerifierBridge premise |
| [Partial lemma workflow](conditional_separation/README.md#partial-work-across-machines) | Compile a useful closed lemma and its named check; transfer source/identity; final checker must still reject the partial-only attempt |

This is **Infrastructure**, not a proof of R, unconditional P≠NP, a novel
magnification theorem, an established equivalence to every external model, or
Lean-team/mathlib/institutional endorsement. Source review, exact-head native
Linux/macOS/install evidence and release/publication decisions remain separate.
The [old Preprint](Preprint.latex) describes a historical SAL/anti-checker route;
it is not the accompanying direct-route paper. Its retained claims are not
current release evidence. The research note states the current quantifiers,
codec, prefix language and literature limitations explicitly.

## Historical PNP3 RC notes (17 August 2026)

The following material is retained for the legacy PNP3 release/audit track.
Its `ResearchGapWitness` and verifier/runtime/advice boundaries are not extra
hypotheses of the direct standalone endpoint above. Links and historical audit
commands below preserve that scope; they are not fresh execution receipts.

- Release type: **RC / framework milestone**, not a final unconditional claim.
- Status date: 2026-08-17.
- Source of truth for release wording: `RELEASE_RC.md`.
- Source of truth for closure progress: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Claim matrix

| Claim                                                                 | Status                                                       |
|-----------------------------------------------------------------------|--------------------------------------------------------------|
| Active `pnp3/` has no project-local axioms and no `sorry`/`admit`     | Verified by `scripts/check.sh` policy                        |
| `P_subset_PpolyDAG` internalized                                      | Proved, but coarse polynomial-size inclusion                 |
| `ResearchGapWitness` → `P_ne_NP_final`                                | Proved conditional bridge                                    |
| Old support-bounds / multi-switching route                            | Formally refuted; retained only as audit / compatibility     |
| `FormulaSupportBoundsPartial_fromPipeline_fixedParams`                | Candidate contract shape, not a proved source theorem        |
| Deprecated pnp3 AC0 endpoint                                         | Vacuous enriched-package statement; not a standard AC0 lower bound |
| Unconditional `P != NP`                                               | **Not claimed**                                              |

## Historical PNP3 public closure boundary

The current public default endpoints (in
`pnp3/Magnification/UnconditionalResearchGap.lean`) are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

The only mathematical input is
`ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG`.  Legacy
`hMag` / `hMS` / support-bounds / multi-switching / provider entry points
are retained only as explicit audit / compatibility wrappers; their source
predicates are formally refuted by the falsifiability audit.

## What this release does not include

1. An unconditional in-repo theorem `P != NP`.
2. A non-vacuous proof of the formula-side support / locality source
   theorem.
3. A proof that `FormulaSupportBoundsPartial_fromPipeline_fixedParams` is
   realizable for realistic AC0 parameters.
4. A zero-argument final theorem with no external research payload.
5. A claim that deprecated `gapPartialMCSP_not_in_AC0` is a standard AC0
   lower bound. It only negates an enriched package whose `params` and
   `easyData` fields already imply `False` without solver correctness.

## Audit-only theorem surfaces — not claims

The final-result modules also contain quarantined audit / compatibility
endpoints that compile but do not represent publishable claims.  Per
Research Constitution Rule 6, every such endpoint carries one of three
explicit name prefixes:

| Prefix          | Meaning                                                      | Module                                       |
|-----------------|--------------------------------------------------------------|----------------------------------------------|
| `RefutedRoute_` | Consumes a refuted predicate (e.g. `MagnificationAssumptions`, `FormulaSupportBoundsFromMultiSwitchingContract`, ...).  Vacuous as a path to unconditional closure. | `FinalResultAuditRoutes.lean`, plus the `_supportBounds_TM` companions in `FinalResultLegacyTM.lean` |
| `AuditOnly_`    | Legacy `_TM` compatibility wrapper not consuming refuted predicates directly, but kept off the publishable surface. | `FinalResultLegacyTM.lean`                   |
| `Vacuous_`      | Vacuous via the typeclass-payload audit channel (`FinalPayloadProvider`, `DefaultFormulaSource`, ...).  Records the channel concretely so it cannot quietly come back. | `FinalResultAuditRoutes.lean`                |

These prefixes are enforced visually: no `RefutedRoute_*` /
`AuditOnly_*` / `Vacuous_*` endpoint should ever be presented as the
public closure boundary.  Treat them as the analogue of an `audit/`
directory inside the type-theoretic API: their job is to keep historical
shapes importable while making it impossible to mistake them for
unconditional results.

## How to verify

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean \
         pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean; do
  lake env lean "$f"
done
```

## Where to read next

| Question                                | File                                         |
|-----------------------------------------|----------------------------------------------|
| What is the project, in two pages?      | `README.md`                                  |
| What is closed and what is open?        | `STATUS.md`                                  |
| What blocks unconditional closure?      | `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`         |
| Route map for auditors                  | `PROOF_OVERVIEW.md`                          |
| Common questions                        | `FAQ.md`                                     |
| Verified vs. not-claimed claim table    | `TECHNICAL_CLAIMS.md`                        |
| Axiom / `sorry` hygiene only            | `AXIOMS_FINAL_LIST.md`                       |
| Detailed frontier FAQ           | `pnp3/Docs/Unconditionality_FAQ.md`       |
| Route policy lock                       | `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`          |
| Release wording guardrail               | `RELEASE_RC.md`                              |
