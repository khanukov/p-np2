# Worker prompt

Branch:

main

Task:

post-RED canonical asymptotic closure audit

Task type:

Markdown-only, unless explicitly asked to add a tiny companion theorem later.

Context

The canonical asymptotic track now has a RED theorem:

isoStrong_conclusion_negative_for_canonical

This proves that the canonical iso-strong route is impossible at
canonicalAsymptoticHAsym.

STATUS.md also says the promise-YES weak/certificate routes are
inconsistent at conclusion side. This audit must verify whether that
claim is already theorem-backed or only an expected analogue.

Required reading

Read:

RESEARCH_CONSTITUTION.md
STATUS.md
pnp3/Tests/IsoStrongConclusionProbe.lean
pnp3/Tests/GlobalHInDagContractProbe.lean
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean
pnp3/Magnification/FinalResultMainline.lean
pnp3/Tests/CanonicalIntegrationTests.lean

Goal

Create exactly one report:

seed_packs/post_red_canonical_closure_audit/reports/post_red_closure_<HANDLE>.md

If the seed pack does not exist, create:
seed_packs/post_red_canonical_closure_audit/README.md
seed_packs/post_red_canonical_closure_audit/WORKER_PROMPT.md
seed_packs/post_red_canonical_closure_audit/reports/.gitkeep
seed_packs/post_red_canonical_closure_audit/failures/.gitkeep

Required sections

1. Executive verdict

Choose exactly one:

- ISO_ONLY_RED_STATUS_OK
- ISO_RED_PROMISE_OVERCLAIM
- ISO_AND_PROMISE_RED_FORMALLY_SUPPORTED
- NEEDS_COMPANION_PROMISE_THEOREM

2. What is formally proved

Quote/summarize:

isoStrong_conclusion_negative_for_canonical

State exact file and theorem.

3. What STATUS.md claims

List each claim:
- iso-strong route closed
- promise-YES weak route closed
- promise-YES certificate route closed
- canonical asymptotic track closed

Classify each as:
- theorem-backed
- follows by existing theorem
- plausible but not formal
- overclaim

4. Promise route dependency audit

Inspect:

- AsymptoticPromiseYesCertificateRoute
- AsymptoticPromiseYesWeakRouteEventually
- PromiseYesSubcubeCertificateAt
- final endpoints using promise routes

Answer:

Does isoStrong negative directly imply promise negative?
Or does promise need separate theorem?

5. Recommended correction

If STATUS overclaims, propose exact wording change.

If companion theorem is needed, state exact theorem target.

6. Next action

Choose one:

- merge_status_as_is
- patch_status_wording
- open_promise_companion_L0
- close_canonical_track_fully

Forbidden

No Lean code unless separately authorised.
No source edits.
No JSONL/spec/known_guards.
No ResearchGapWitness.
No SourceTheorem.
No gap_from.
No endpoint.
No P≠NP claim.

Allowed

Only the report/skeleton files.

Commands

Run:

./scripts/check.sh

Output format

Task: post-RED canonical closure audit
Handle:
Commit before:
Commit after:
Outcome:
Executive verdict:
Theorem-backed claims:
Overclaims:
Recommended next action:
Scope violations:
