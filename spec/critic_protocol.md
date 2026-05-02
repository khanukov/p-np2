# Critic protocol — Research Governance v0.1, Autoresearch MVP-4 / MVP-0.1.1

This document specifies the **structured output format** every Critic
agent (manual or LLM-assisted) must produce when evaluating a
candidate package under `pnp3/Candidates/<id>/`.

> **MVP-0.1.1 update (Critic state hardening).**  Section 8 below
> formalises the four critic-state fields that
> `scripts/verify_candidate.sh` now emits in `result.json`
> (`critic_report_present`, `critic_report_is_template`,
> `critic_completed`, `critic_status`) and the cross-field rules
> that `scripts/validate_jsonl.py::validate_attempt` enforces on
> `outputs/attempts.jsonl` lines.  The intent is that a
> `critic_status = pass` / `fail` line in the attempts ledger is
> only admissible when the Critic has produced a real,
> non-template, well-formed report — not just any file at the
> conventional path.

The Critic is **not** a verifier; that is `scripts/verify_candidate.sh`
(Autoresearch MVP-2).  The Critic is **adversarial**: its job is to
break the candidate, not to fix it.  See Rule 12 of the Research
Constitution: Generator and Critic are separated, the Critic only
refutes.

The Critic protocol is intentionally minimal in this MVP:

- output is one Markdown file at `pnp3/Candidates/<id>/critic_report.md`,
  using the template at `pnp3/Candidates/_template/critic_report.md`;
- exactly six attack sections, in the order below, each with a fixed
  three-field schema (`status`, `summary`, `evidence`);
- one final classification verdict (`pass` / `fail`) at the bottom;
- an `outputs/attempts.jsonl` line is appended for every Verifier+Critic
  cycle, with `critic_status ∈ {not_run, pass, fail}` and
  `critic_break_class` populated from `failure_class` when
  `critic_status = fail`.

## 1. The six attack sections

Every Critic report must contain these six sections, in this order:

| § | Attack name                          | Maps to failure_class             |
| - | ------------------------------------ | --------------------------------- |
| 1 | Hidden-payload attack                | `typeclass_payload`, `implicit_assumption_channel` |
| 2 | Hardwiring attack                    | `hardwiring`                      |
| 3 | KnownGuards-factorization attack     | `vacuity`                         |
| 4 | Natural-proof / relativization / algebrization barrier audit | `natural_proof`, `relativization`, `algebrization` |
| 5 | Collapse-not-contradiction audit     | `collapse_not_contradiction`      |
| 6 | Vacuity / source-theorem rephrasing audit | `vacuity`, `goal_drift`        |

A Critic that omits any of the six sections produces an INVALID
report; the verifier MUST refuse to record `critic_status = pass` for
the corresponding `attempts.jsonl` line.

## 2. Per-attack fixed schema

Every attack section is exactly this shape (verbatim Markdown):

```markdown
## Attack <N>: <attack name>

- **status:** `no break found` | `break found` | `attack not applicable`
- **summary:** <one to three sentences explaining what was attempted>
- **evidence:**
    - <bullet 1>
    - <bullet 2>
    - ...
```

Allowed `status` values:

* `no break found` — the Critic ran the attack and could not refute
  the candidate.
* `break found` — the Critic produced an explicit refutation;
  `evidence` MUST cite either a Lean witness (`path:line`) or a
  precise structural argument that another reviewer can independently
  reproduce.  Vague prose ("this looks fishy") is NOT a `break found`
  — file it under `attack not applicable` or `no break found` with a
  follow-up TODO.
* `attack not applicable` — the candidate's method family does not
  intersect this attack family (e.g. a candidate that contains no
  truth-table-like construction is not subject to a hardwiring
  attack).  `evidence` MUST justify the non-applicability in one
  sentence.

## 3. Final verdict

The report ends with one of:

```markdown
## Verdict

- **critic_status:** `pass` | `fail`
- **dominant_break_class:** <one of nogolog_schema.json's failure_class enum>  (when status=fail)
- **dominant_break_section:** <integer 1..6>  (when status=fail)
- **next_recommended_action:** <free-text, ≤ 200 chars>
```

`critic_status = pass` is allowed iff every attack section has
`status ∈ {no break found, attack not applicable}`.  A single
`break found` forces `critic_status = fail`, with `dominant_break_class`
and `dominant_break_section` populated.

## 4. Append to `outputs/attempts.jsonl`

After the report file is written, the Critic MUST append a single
line to `outputs/attempts.jsonl` via `scripts/attempts_append.py`,
with at minimum these fields:

```json
{
  "candidate_id": "<id>",
  "method_family": "<MethodFamily>",
  "verifier_status": "<from prior verifier run>",
  "critic_status": "<pass | fail>",
  "critic_break_class": "<failure_class or null>",
  "critic_report_path": "pnp3/Candidates/<id>/critic_report.md",
  "applicable_spec_version": "<from spec/target.toml::[meta].spec_version>",
  "attack_suite_version": "<from bench/SmokeProbe metadata>"
}
```

The append script auto-fills `id` and `created_at`.

If `critic_status = fail`, the Critic MUST ALSO append a NoGoLog
entry via `scripts/nogolog_append.py` describing the structural
pattern that was broken.  The two appends are NOT optional:
together they form the audit trail that proves the candidate has
been adversarially evaluated.

## 5. Forbidden Critic actions

A Critic MAY NOT:

* edit the candidate's source files (no `pnp3/Candidates/<id>/proof.lean`
  changes from the Critic side — Rule 12);
* edit any file in the trust root or under `pnp3/Magnification/` /
  `pnp3/LowerBounds/` / `pnp3/Complexity/` to make the candidate
  pass;
* edit any existing JSONL log entry (append-only, Rule 9);
* claim a `pass` verdict if any of the six attack sections is missing
  or has a malformed schema;
* claim a `break found` without citing reproducible evidence;
* downgrade an existing NoGoLog entry's `status` (corrections via
  supersession only).

## 6. MVP scope

This MVP defines the Critic protocol only.  It does NOT specify:

* who runs the Critic (manual reviewer / LLM / autoresearch worker);
* how attacks are generated (heuristic / template / search);
* a deterministic Critic engine (FP-3b/4 era);
* a Critic-vs-Generator policy network (deferred).

The protocol is the minimum that makes Critic outputs comparable
across runs.  Extensions (e.g. weighted attack severity, per-method-
family attack specialisations, Critic-Critic adversarial loops) are
follow-up work.

## 7. Critic-state fields and cross-field validation (MVP-0.1.1)

`scripts/verify_candidate.sh` emits four critic-state fields in
`result.json` (schema_version 1.2):

| Field                       | Source                                             |
| --------------------------- | -------------------------------------------------- |
| `critic_report_present`     | `[[ -f <candidate>/critic_report.md ]]`            |
| `critic_report_is_template` | `validate_critic_report.py` (TEMPLATE_MARKER scan) |
| `critic_completed`          | `validate_critic_report.py` (well-formed && !template && verdict in {pass, fail}) |
| `critic_status`             | Always `not_run` in Verifier-side `result.json`. Real pass/fail values are written by the Critic into the corresponding `outputs/attempts.jsonl` line. |

A Critic claiming a real verdict MUST do all of the following:

1. **Remove** the `<!-- TEMPLATE_MARKER: do-not-treat-as-completed -->`
   HTML comment line at the top of the report.
2. **Replace** every section's `Template placeholder` summary with
   real prose, and every `Template — fill ...` evidence bullet with
   real evidence (`path:line` or a structurally reproducible
   argument).
3. **Set** the Verdict block's `critic_status` to `pass` or `fail`
   (the template ships with the sentinel `template_not_filled`,
   which `validate_critic_report.py` reports as `not_run`).
4. **Append** a new `attempts.jsonl` line via
   `scripts/attempts_append.py` with `critic_report_path` pointing
   to the filled-in report.

`scripts/validate_jsonl.py::validate_attempt` enforces the following
cross-field rules on every `attempts.jsonl` entry:

* `verifier_status = "FAIL"` ⇒ `verifier_failure_class` present and
  non-null.
* `critic_status ∈ {"pass", "fail"}` ⇒
  `verifier_status ∈ {"PASS", "PASS_SHAPE_ONLY"}` (the Critic only
  runs after a passing Verifier, §4).
* `critic_status = "pass"` ⇒ `critic_report_path` is a non-empty
  string pointing to an existing file inside the repo, the file
  parses as well-formed and non-template via
  `validate_critic_report.py`, the file's own Verdict
  `critic_status` is `pass`, and no attack section reports
  `break found`.
* `critic_status = "fail"` ⇒ `critic_break_class` present and
  non-null AND `critic_report_path` points to an existing,
  well-formed, non-template report whose Verdict
  `critic_status` is `fail`.

A template `critic_report.md` (e.g.
`pnp3/Candidates/_template/critic_report.md`) is NEVER accepted as
evidence for `critic_status ∈ {"pass", "fail"}`.

## 8. Relationship to FixedParams Probe

The FixedParams Probe (FP-1 .. FP-3b.0) was conducted **before** the
Critic protocol existed; its self-attack lives in
`FixedParams_Probe.md` §8 with an ad-hoc four-test format (Test 1
no hidden payload / Test 2 not tautological / Test 3 hardwiring
attack / Test 4 KnownGuards factorization).  Future probes (FP-3b.1
onward) SHOULD use this six-attack Critic protocol instead, even
when the candidate stays under `pnp3/Magnification/AuditRoutes/`
rather than `pnp3/Candidates/`.  In that case the Critic report
lives at `seed_packs/<seed_pack_id>/critic_report.md` and the
attempts.jsonl line uses the seed pack id as `candidate_id` (with
a `notes` field explaining the audit-only routing).
