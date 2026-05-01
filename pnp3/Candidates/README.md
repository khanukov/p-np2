# Candidate intake — Research Governance v0.1

This directory holds candidate research packages.

A **candidate** is one self-contained attempt to construct a
`ResearchGapWitness` (or to fail in a way that produces a structured
`NoGoLog` entry). Each candidate lives in its own directory:

```
pnp3/Candidates/<method-family>/<candidate-id>/
```

with the standard five-file layout (see
`pnp3/Candidates/_template/`).

The full intake protocol is specified in:

- `RESEARCH_CONSTITUTION.md` Rule 3 (candidate location)
- `RESEARCH_CONSTITUTION.md` Rule 4 (`SourceTheorem` size limits)
- `RESEARCH_CONSTITUTION.md` Rule 5 (no arbitrary witness quantification)
- `RESEARCH_CONSTITUTION.md` Rule 7 (executable barrier certificates)
- `RESEARCH_CONSTITUTION.md` Rule 11 (joint candidates)
- `RESEARCH_CONSTITUTION.md` Rule 13 (reproducibility)
- `RESEARCH_CONSTITUTION.md` Rule 14 (time-locked verification)
- `RESEARCH_CONSTITUTION.md` Rule 15 (prior-work disclosure)
- `RESEARCH_CONSTITUTION.md` Rule 16 (no hidden payload providers)
- `spec/implicit_assumption_channels.md`
- `spec/source_theorem_size_policy.md`

## Required layout per candidate

```
pnp3/Candidates/<method-family>/<candidate-id>/
  proof.lean              Lean source: SourceTheorem_<id> + gap_from_<id>
  manifest.toml           machine-readable metadata (Rule 3)
  sketch.md               plain-language summary of the approach
  barrier_certificate.md  Rule 7 certificate (which barrier is broken)
  self_attack.md          candidate's own attempt to break itself
```

`scripts/verify_candidate.sh --candidate <path>` checks file presence
and runs all currently-shipped guards. PR 8 (size checker), PR 11
(target-lock checker), and PR 12 (barrier-certificate checker)
extend the verifier with progressively stricter checks. PR 15
finalises the JSON `result.json` schema.

## Status semantics

- `PASS_SHAPE_ONLY` — file layout, manifest schema, and all global
  guards pass. **This is not an `accepted` status.** Per
  `RESEARCH_CONSTITUTION.md` Rule 1, an `accepted` status requires a
  closed `P_ne_NP_unconditional` term, which the verifier does not
  yet produce.
- `FAIL_<reason>` — at least one guard or shape check failed.
- `HUMAN_REVIEW_REQUIRED` — the candidate passes mechanical guards
  but exceeds `K_stmt`/`K_exp` (Rule 4), or its barrier certificate
  is marked `unknown-human-review` (Rule 7).
- `EXPIRED_REVIEW` — the candidate has been in
  `HUMAN_REVIEW_REQUIRED` for longer than
  `spec/target.toml::[human_review].candidate_sla_days` (= 14 days).

## Forbidden moves

Per `RESEARCH_CONSTITUTION.md` Rule 16:

- No `class`, `instance`, `default_instance`, `attribute [instance]`
  inside a candidate's `proof.lean` (whitelist exemptions only via
  `manifest.toml::[whitelisted_typeclasses]`).
- No `Fact <P>` arguments in `SourceTheorem_<id>` or `gap_from_<id>`.
- No `noncomputable def` with names matching
  `(Provider|Default|Payload|Witness|Source|Gap)`.
- No `opaque` declarations.

Per Rule 6:

- No imports from `pnp3/RefutedPredicates/` other than the canonical
  `RefutedPredicate_*` audit aliases (importing them means the
  candidate explicitly acknowledges the dependency).
- No imports from `pnp3/Magnification/AuditRoutes/` (planned).

Per Rule 0:

- No edits to the trust root: `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`.

## Adding a new candidate

1. Copy `pnp3/Candidates/_template/` to
   `pnp3/Candidates/<method-family>/<candidate-id>/`.
2. Fill `manifest.toml` with concrete values.
3. Replace `SourceTheorem_template` and `gap_from_template` with
   real declarations.
4. Run `scripts/verify_candidate.sh --candidate
   pnp3/Candidates/<method-family>/<candidate-id>/`.
5. If `PASS_SHAPE_ONLY`, open a PR tagged `candidate` (mutually
   exclusive with `foundational` per `RESEARCH_CONSTITUTION.md`
   §"Mutually exclusive PR scopes").
6. The Critic (Rule 12) attacks the candidate; failures land in
   `outputs/nogolog.jsonl` (PR 9).
