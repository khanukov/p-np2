# Pilot Wave 0 — worker protocol

Research Governance v0.1, Autoresearch MVP-0.1.

This document is the **step-by-step minimum-viable cycle** for one
Pilot Wave 0 worker.  A worker is a single human (manual mode) or
LLM agent (assisted mode) tasked with one seed pack from
`seed_packs/<id>/`.  The cycle is intentionally small: 5–10 manual
workers max, sequential, no autoresearch full-scale.

The protocol exists to make the cycle **comparable across runs**
and **auditable post-hoc**.  Every step has a concrete artifact
that gets committed; nothing lives only in chat or scratch notes.

## 0. Pre-requisites

Before starting:

1. The branch passes `scripts/audit_bootstrap.sh` clean
   (no real `P_ne_NP_unconditional` blocker).
2. `lake build PnP3 Pnp4` is green.
3. `scripts/check.sh` is 17/17 green (incl. all sub-steps:
   10.b, 10.c, 12.b, 12.c).
4. `scripts/run_smoke_probes.sh` is 8/8 green.
5. The worker has read:
   * `RESEARCH_CONSTITUTION.md`,
   * `seed_packs/<chosen_seed_pack_id>/README.md`,
   * `spec/critic_protocol.md`,
   * `FixedParams_Probe.md` if the seed pack is in the FP family.
6. The worker has selected exactly ONE seed pack id; running
   multiple in parallel under one worker is forbidden.

## 1. Pick a seed pack

```
ls seed_packs/
cat seed_packs/<chosen_id>/README.md
```

The seed pack defines:

* **Goal** — what the worker is trying to formalize, falsify, or
  classify.
* **Allowed scope** — the files the worker MAY edit.
* **Forbidden scope** — files the worker MUST NOT edit (always
  includes the trust root).
* **Acceptance criteria** — the executable / testable conditions
  for a successful worker run.

A seed pack run produces ONE of three terminal states: `attempts.jsonl`
records the outcome with `verifier_status` and `critic_status`
fields plus optional NoGoLog/survivor history entries.

## 2. Branch off

```
git checkout -b worker/<seed_pack_id>/<short_name>
```

Worker branches are NOT pushed to `main` directly.  They are
reviewed via PR; only after one human review is the branch merged.
A worker may NEVER force-push, NEVER edit existing JSONL log
entries, and NEVER promote anything to `pnp3/Candidates/<id>/`
without explicit owner approval.

## 3. Do the work

The work is whatever the seed pack's Goal section says.  Examples:

* **FP-3b.2 (Research-A):** replace the body of
  `FP3Attempt.FP3b1.adversaryFamily` in
  `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` with a
  real log-width truth-table-shaped construction; prove
  `adversary_satisfies_diversity`.
* **Critic dry-run (Critic-1):** write a real, non-template
  `critic_report.md` against
  `FP3Attempt.InSupportFunctionalDiversity` (audit-only routing,
  see `spec/critic_protocol.md` §7).
* **Infra hardening:** ship a small targeted PR (e.g.
  MVP-0.1.x).

The worker does NOT write a Pilot Wave 0 attempt for trust-root
audits, doc edits, or other non-candidate work.  Only seed-pack
cycles produce attempts.jsonl entries.

## 4. Run the Verifier

```
scripts/verify_candidate.sh \
  --candidate <candidate_dir_or_omit_for_tree_level> \
  --full \
  --json /tmp/wave0_<id>_result.json \
  --stage-timeout 1200
```

The Verifier emits four critic-state fields in result.json (per
MVP-0.1.1 hardening):

* `critic_report_present`
* `critic_report_is_template`
* `critic_completed`
* `critic_status` (`not_run` until the Critic step below runs)

`--stage-timeout 1200` (20 min) bounds long-running stages
(MVP-0.1.6).  If the Verifier dies mid-stage, an EXIT trap writes
a partial result.json with `status="ABNORMAL_EXIT"` so the
worker can see *which stage* died.

If the Verifier returns `status=FAIL_*`, the worker MUST stop here
and append a NoGoLog entry plus an attempts.jsonl entry — see §7.
A worker CANNOT proceed to the Critic step on a FAIL'd candidate.

## 5. Run the Critic (only after Verifier PASS / PASS_SHAPE_ONLY)

The Critic produces a **structured** Markdown report at
`<candidate_dir>/critic_report.md` (or
`seed_packs/<seed_pack_id>/critic_report.md` for audit-only seed
packs that don't ship a `Candidates/<id>/` package).

The protocol is fixed at `spec/critic_protocol.md`:

* Six attack sections, in order: Hidden-payload, Hardwiring,
  KnownGuards-factorization, Natural-proof / relativization /
  algebrization, Collapse-not-contradiction, Vacuity / source-
  theorem rephrasing.
* Each section has fields `status` (`no break found`/`break
  found`/`attack not applicable`), `summary` (1–3 sentences),
  `evidence` (bulleted list with reproducible references).
* Final Verdict block with `critic_status` (`pass`/`fail` —
  `TEMPLATE` is the empty-template marker only),
  `dominant_break_class`, `dominant_break_section`,
  `next_recommended_action`.

Forbidden Critic actions:

* editing `<candidate_dir>/proof.lean` (that's Generator's
  responsibility — Rule 12);
* editing the trust root to make the candidate pass;
* claiming `pass` when any attack section is missing or in
  template shape;
* claiming `break found` without reproducible evidence;
* downgrading an existing NoGoLog entry's status (corrections
  via supersession only).

After writing the report, validate it:

```
scripts/validate_critic_report.py --require-completed \
  <candidate_dir>/critic_report.md
```

This MUST exit 0.  If it exits 2, the report is in template /
incomplete state; fix it.

## 6. Append to the ledgers

Append exactly one line to `outputs/attempts.jsonl`:

```
echo '{...}' | scripts/attempts_append.py
```

Required fields (from `spec/nogolog_schema.json::AttemptLedgerEntry`):

```json
{
  "candidate_id": "<id>",
  "seed_pack_id": "<seed_pack_id>",
  "method_family": "<MethodFamily>",
  "verifier_status": "PASS|FAIL|PASS_SHAPE_ONLY",
  "verifier_failure_class": "<FailureClass or null>",
  "critic_status": "pass|fail|not_run",
  "critic_break_class": "<FailureClass or null>",
  "critic_report_path": "<path-to-critic_report.md or null>",
  "applicable_spec_version": "0.1.0",
  "attack_suite_version": "0.1.0"
}
```

Cross-field rules (MVP-0.1.1 hardening) enforce:

* `critic_status=pass` requires non-null path, non-template,
  completed, verdict-pass — three pass-traps closed.
* `critic_status=fail` requires populated `critic_break_class` and
  agreement with the report's `dominant_break_class`.
* `critic_status=not_run` allows path null/missing/template (the
  Verifier-ran-but-no-Critic state).

If `critic_status=fail`: ALSO append a NoGoLog entry via
`scripts/nogolog_append.py` describing the structural pattern of
the break.  Both appends are mandatory; together they form the
audit trail.

If `critic_status=pass` AND the seed pack's acceptance criteria
include "promote to survivor": append a `SurvivorHistoryEntry`
via the pattern in `spec/nogolog_schema.json` (currently no helper
script — do it manually until MVP-0.2 ships one).

## 7. FAIL-path summary

If the Verifier or Critic fails, the worker still produces TWO
artifacts:

1. `outputs/attempts.jsonl` line with the failed status.
2. `outputs/nogolog.jsonl` entry via `scripts/nogolog_append.py`
   (only when `critic_status=fail` or when the Verifier failure
   reveals a new structural pattern; routine `verifier_status=FAIL`
   from a stale candidate doesn't necessarily warrant a NoGoLog
   entry).

NoGoLog entries are the project's institutional memory; they
prevent the same failure shape from being re-tried later under a
different name.

## 8. Final commit

```
git add <whatever-was-modified>
git commit -m "<seed_pack_id>: <one-line-summary>"
```

Commit messages MUST mention:

* the seed pack id;
* the verifier status, critic status, NoGoLog entry id (if any),
  attempts.jsonl entry id;
* explicit "what did NOT change" list (no trust-root edits,
  no Candidates/ promotion if applicable, etc.).

A worker run that does NOT update either `outputs/attempts.jsonl`
OR a NoGoLog entry is INVALID and MUST NOT be merged.  The whole
point of Pilot Wave 0 is to close the loop seed→verifier→critic
→ledger.

## 9. Forbidden parallel scaling in Pilot Wave 0

Until at least three Pilot Wave 0 cycles have completed cleanly:

* MAX 5–10 workers concurrently;
* NO autoresearch full-scale;
* NO LLM-only Critic (every Critic report MUST be reviewed by at
  least one human);
* NO automatic NoGoLog appends (every entry MUST be human-
  authored or human-reviewed);
* NO `pnp3/Candidates/<real-id>/` promotion without explicit
  owner approval;
* NO FP-4 / bridge / SourceTheorem / final endpoint;
* NO promotion of any guard in `spec/known_guards.toml` to
  `status = "accepted"`.

The scaling gates beyond Pilot Wave 0 are:

* **Wave 1 (10–20 workers):** requires three Pilot Wave 0 cycles
  to have completed cleanly with at least one Critic-fail and
  one Critic-pass observed.
* **Wave 2 (50+ workers):** requires Wave 1 plus a Critic-vs-
  Generator separation enforced at infrastructure level (today's
  Critic protocol relies on protocol-level enforcement only).
* **Autoresearch full-scale:** out of scope until at least one
  candidate has survived Wave 2 plus one human-driven adversarial
  pass.

## 10. Common failure modes (anti-patterns)

These have been observed in earlier non-Pilot-Wave-0 work and
must be avoided:

* **Critic-template trap.**  `critic_status=pass` with a path
  pointing at the empty template.  Closed by MVP-0.1.1; the
  attempts validator now refuses this.
* **Underscore-bypass.**  Naming a candidate `_evil/` to evade
  the Rule-16 scan.  Closed by MVP-0.1.3.
* **Hidden payload via typeclass / Fact / opaque / class**.  See
  `spec/implicit_assumption_channels.md` and the negative-control
  test `scripts/test_rule16_negative.sh` (MVP-0.1.2).
* **Renaming the predicate.**  Replacing
  `OverbroadUniformFormulaProvenance` with a structurally
  identical `UniformFamilyProvenance` is a Rule-2 violation.  See
  `FixedParams_Probe.md` §7.
* **Quantifier shuffling / existential dressing.**  Wrapping the
  predicate to keep hardwiring witness alive.  Same §7.
* **Assuming `lake build` = green = correct.**  `lake build`
  proves the *types* check; it does not prove the *math* is
  meaningful.  An audit-only artifact is not the same as a
  proven theorem.

## 11. Worker output checklist

Before opening a PR for the worker run, the worker MUST verify:

```
[ ]  lake build PnP3 Pnp4                    -> green
[ ]  scripts/check.sh                         -> 17/17 + sub-steps green
[ ]  scripts/run_smoke_probes.sh              -> 8/8 green
[ ]  scripts/audit_bootstrap.sh               -> result clean
[ ]  scripts/test_attempts_validator.sh       -> green
[ ]  scripts/test_underscore_policy.sh        -> green
[ ]  scripts/test_rule16_negative.sh          -> green
[ ]  python3 scripts/validate_jsonl.py        -> all 3 logs green
[ ]  python3 scripts/validate_version_manifest.py -> green
[ ]  outputs/attempts.jsonl gained exactly 1 new line
[ ]  if critic_status=fail: outputs/nogolog.jsonl gained 1 new line
[ ]  no edits to trust-root files
[ ]  no `axiom`, `opaque`, `Fact`, typeclass payload, sorry, admit
     in any committed Lean file
[ ]  no edits to existing JSONL log entries (append-only Rule 9)
[ ]  PR description mentions seed_pack_id, attempts.jsonl entry id,
     nogolog.jsonl entry id (if any), explicit "what did NOT change"
     list
```

If any box is unchecked, the worker run is INVALID; fix it before
asking for review.
