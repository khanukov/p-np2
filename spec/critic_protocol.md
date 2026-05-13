# Critic protocol — Research Governance v0.1, Autoresearch MVP-4

This document specifies the **structured output format** every Critic
agent (manual or LLM-assisted) must produce when evaluating a
candidate package under `pnp3/Candidates/<id>/`.

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

- **critic_status:** `pass` | `fail` | `TEMPLATE`
- **dominant_break_class:** <one of nogolog_schema.json's failure_class enum>  (when status=fail)
- **dominant_break_section:** <integer 1..6>  (when status=fail)
- **next_recommended_action:** <free-text, ≤ 200 chars>
```

`critic_status = pass` is allowed iff every attack section has
`status ∈ {no break found, attack not applicable}` AND the file is
NOT detected as a template (see §3.1).  A single `break found`
forces `critic_status = fail`, with `dominant_break_class` and
`dominant_break_section` populated.

The synthetic value `TEMPLATE` is used ONLY by the empty template at
`pnp3/Candidates/_template/critic_report.md` and never appears in a
real Critic-produced report.

### 3.1 TEMPLATE detection (MVP-0.1.1)

The validator `scripts/validate_critic_report.py` flags a report as
`is_template = true` when ANY of:

* the file contains the banner `TEMPLATE FILE` or any of:
  `Template placeholder`, `Template caveat`, `TEMPLATE marker`,
  `Template — fill`, `Template note.`, or
  `DO NOT USE AS A REAL CRITIC OUTPUT`;
* the Verdict's `critic_status:` line equals `TEMPLATE`;
* every attack section's `status` is `attack not applicable` AND the
  file contains the soft template marker `Template.` in any
  evidence block.

A real Critic-produced report MUST clear all three signals:

1. Remove the `TEMPLATE FILE` banner and any `Template …`
   placeholder text;
2. set the Verdict's `critic_status` to `pass` or `fail`;
3. provide non-template evidence in every section (the validator
   does not deeply parse evidence prose, but the `Template` markers
   above MUST be absent).

`outputs/attempts.jsonl` validation refuses to record
`critic_status ∈ {pass, fail}` when the cited
`critic_report_path` resolves to a template-flagged or incomplete
file.

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

### 4.1 Cross-field consistency rules (MVP-0.1.1 hardening)

`scripts/validate_jsonl.py::validate_attempt` enforces:

* `critic_status = "pass"` REJECTS the entry unless ALL of:
  * `critic_report_path` is a non-null string;
  * the file at that path exists relative to repo root;
  * `validate_critic_report_file(<path>).is_template == false`;
  * `validate_critic_report_file(<path>).completed == true`;
  * `validate_critic_report_file(<path>).verdict_critic_status == "pass"`.
* `critic_status = "fail"` REJECTS the entry unless ALL of:
  * the same four conditions above with verdict `"fail"` instead of
    `"pass"`;
  * `critic_break_class` populated with a `FailureClass` enum value;
  * the report's `dominant_break_class` agrees with
    `critic_break_class` (when both are present).
* `critic_status = "not_run"` allows `critic_report_path` to be
  missing, null, or pointing at a template — this is the "Critic
  has not yet run" state, e.g. immediately after Verifier has
  produced `verifier_status = PASS_SHAPE_ONLY`.

Three pass-traps the audit identified are now structurally
rejected:

1. `critic_status = "pass"` with NO `critic_report_path` field.
2. `critic_status = "pass"` with `critic_report_path` pointing at a
   non-existent file.
3. `critic_status = "pass"` with `critic_report_path` pointing at
   `pnp3/Candidates/_template/critic_report.md` (or any file
   carrying the TEMPLATE markers from §3.1).

These three cases are exercised by
`scripts/test_attempts_validator.sh`, which is wired into
`scripts/check.sh` step 12.b.

### 4.2 Verifier surface (MVP-0.1.1, schema 1.2; MVP-0.1.6 added 1.3)

`scripts/verify_candidate.sh` emits four critic-state fields in
its `result.json` since schema 1.2, plus optional abnormal-exit
metadata at schema 1.3:

```json
{
  "schema_version":            "1.3",
  "critic_report_present":     true | false,
  "critic_report_is_template": true | false,
  "critic_completed":          true | false,
  "critic_status":             "not_run" | "pass" | "fail",
  "abnormal_exit_stage":       "<stage>",   // only when status=ABNORMAL_EXIT
  "abnormal_exit_code":        <int>        // only when status=ABNORMAL_EXIT
}
```

The Verifier-emitted `critic_status` is `not_run` whenever the
report is a template, incomplete, or absent — even if the report
file's `critic_status:` line says `pass`.  Downstream tooling MUST
read `critic_status` and `critic_completed` (NOT just
`critic_report_present`) to decide whether the candidate has been
critic-cleared.

The full machine-readable contract is at
`scripts/verifier_result_schema.json`.  Cross-field rules in that
schema enforce: `critic_status ∈ {pass, fail}` ⇒
`critic_completed = true` AND `critic_report_is_template = false`.

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

## 7. Relationship to FixedParams Probe

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
