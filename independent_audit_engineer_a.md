# Independent audit report — Engineer A (Control-plane / verifier / ledger)

This is an independent first-pass audit of commit `7dcba2c`
("Autoresearch MVP control plane: ledger + Critic protocol + seed packs")
on branch `claude/research-governance-phase0-lmZBP` (≡ `kCCuv` at the
audit commit).

The audit follows the Engineer-A focus from the audit instructions:
control-plane / Verifier / ledger / Critic-report semantics. Math
feasibility of FP-3b.1 (Engineer B), Rule-16 surface adversarial
audit (Engineer C), and pilot-scaling governance (Engineer D) are
covered only at the depth needed to draw a Go/No-Go.

The audit was performed in isolation; no other auditor's output was
read before drafting this report.

## 1. Environment

- branch (audited): `claude/research-governance-phase0-lmZBP`
- branch (work): `claude/research-governance-phase0-kCCuv` (same HEAD)
- commit: `7dcba2c7cce8b251f9e936d7aacee4dc5c9eb601`
- lake version: `Lake 5.0.0-src+6a60de2 (Lean 4.22.0-rc2)`
- toolchain: `leanprover/lean4:v4.22.0-rc2` (matches `lean-toolchain`)
- OS: Linux 6.18.5 (sandbox)
- commands run (relevant subset):
  - `lake exe cache get`
  - `lake build PnP3 Pnp4`
  - `scripts/run_smoke_probes.sh`
  - `scripts/check.sh`
  - `python3 scripts/validate_jsonl.py`
  - `scripts/verify_candidate.sh --candidate pnp3/Candidates/_template …`
  - per-guard probes: `scripts/check_doc_honesty.sh`,
    `scripts/check_target_lock.sh`,
    `scripts/check_candidate_rule16.sh`,
    `scripts/check_refuted_predicate_usage.sh`,
    `scripts/check_typeclass_payload_quarantine.sh`,
    `scripts/attempts_append.py`

Working tree clean at audit start; no out-of-band edits committed.
A few transient scratch dirs were created and deleted under
`pnp3/Candidates/test_*` and `/tmp/rogue_*` for negative controls;
the live `outputs/attempts.jsonl` was backed up and restored byte-
for-byte after each probe (verified via `cp /tmp/attempts_backup.jsonl …`).

## 2. Baseline result

| Step                                       | Result |
| ------------------------------------------ | ------ |
| `lake build PnP3 Pnp4`                     | PASS   |
| `scripts/check.sh` (17 steps)              | PASS (`All checks passed.`) |
| `scripts/run_smoke_probes.sh`              | PASS (8/8) |
| `scripts/validate_jsonl.py` (all 3 files)  | PASS (`nogolog OK`, `survivor empty OK`, `attempts empty OK`) |
| Verifier on `_template` (`--full`)          | `PASS_SHAPE_ONLY` |

Axiom surface (Step 14/15) shows only the spec-allowed `propext`,
`Classical.choice`, `Quot.sound` — no `Lean.ofReduceBool` /
`Lean.trustCompiler` leaked into the audited theorem cone, in
either `pnp3` or `pnp4`.

Smoke probes that already exist as automated negative controls and
all PASSed:

1. `rejected_imports_refuted` (Rule 6 / PR 4a)
2. `rejected_phantom_axiom` (Rule 1 / PR 1)
3. `rejected_typeclass_payload_channel` (Rule 16 / PR 2)
4. `rejected_unmarked_refuted_route` (Rule 6 / PR 3)
5. `rejected_bare_package_final` (Rule 6 / PR 3b)
6. `rejected_candidate_type_error` (Layer 3 / PR 15.2)
7. `rejected_candidate_sorry` (Layer 3 / PR 15.2)
8. `accepted_noop_candidate_shape` (PR 15)

The shipped automated negative-control coverage is real and works.

## 3. Scope compliance

- Did the audited commit modify the trust root? **No.**
  - `pnp3/Complexity/Interfaces.lean`, `pnp3/Complexity/PsubsetPpolyInternal/`,
    `pnp3/Magnification/UnconditionalResearchGap.lean`, the size measures,
    SAT/DAG encoding, `decides`/`recognizes` — all untouched.
  - `git diff 80f0f72 7dcba2c -- pnp3/Complexity pnp3/Magnification/UnconditionalResearchGap.lean`
    confirms zero Lean changes from these paths in this commit.
- Any unauthorized `theorem P_ne_NP_unconditional`? **No.**
  - The grep `rg -n "theorem\s+P_ne_NP_unconditional|axiom\s+P_ne_NP_unconditional|def\s+P_ne_NP_unconditional" pnp3 pnp4`
    returns one match in `pnp3/Tests/TargetLockProbe.lean:13`, which is a
    docstring fragment, not a declaration.
  - Two textual matches inside `pnp3/Magnification/UnconditionalResearchGap.lean`
    (lines 39, 150) are inside `/-! … -/` block comments (the "How to
    use" template and the commented-out completion template). `awk
    '/^\s*theorem\s+P_ne_NP_unconditional/'` returns no actual top-level
    declaration in either file.
- Any hidden payload channel found in production? **None new.**
  - `VacuousFinalPayloadProvider`, `Fact hasDefault…`, etc. live only
    inside the explicitly-allowed audit-routes files
    (`FinalResultAuditRoutes.lean`, `LocalityProvider_Partial.lean`)
    where the typeclass-payload quarantine guard whitelists them.
- Any unmarked refuted route? **None.**
  - All historical bare names (`NP_not_subset_PpolyFormula_final`,
    `P_ne_NP_final_of_supportBounds`, etc.) appear as
    `theorem RefutedRoute_*` declarations or in docstrings/READMEs.

## 4. Findings

Severity legend (per audit instructions §14):
- **Blocker** — stops Pilot Wave 0.
- **High** — does not stop Pilot Wave 0 but blocks scaling to 10–20
  workers and any public claim of "Critic surviv-ed".
- **Medium** — must be fixed before scaling.
- **Low / Info** — usability, naming, governance hygiene.

### Finding 1 — Template critic trap (BLOCKER)

- severity: **blocker** for scaling; **high** for Pilot Wave 0
- file: `scripts/attempts_append.py`, `scripts/validate_jsonl.py`,
  `pnp3/Candidates/_template/critic_report.md`
- description: `attempts_append.py` + `validate_jsonl.py::validate_attempt`
  accept a fully-formed attempts-ledger entry that records
  `critic_status = "pass"` while `critic_report_path` points at the
  unmodified template `pnp3/Candidates/_template/critic_report.md`.
  The template ships `critic_status: pass` with all six attack
  sections set to `attack not applicable`, and only a textual caveat
  ("a real `pass` requires every attack section to be FILLED IN with
  non-template evidence") asserts the safety property — there is no
  machine guard that:
  1. parses `critic_report.md` for the six required attack sections;
  2. rejects template/placeholder text;
  3. cross-checks that the file at `critic_report_path` exists at all;
  4. cross-checks that the report's verdict matches the ledger entry's
     `critic_status`.
- reproduction (verbatim):
  ```bash
  cp outputs/attempts.jsonl /tmp/attempts_backup.jsonl
  cat > /tmp/fake_pass.json <<'EOF'
  {
    "candidate_id": "fp3b1_log_width_hardwiring_smoke",
    "method_family": "ac0_locality_support",
    "seed_pack_id": "fp3b1_log_width_hardwiring",
    "verifier_status": "PASS_SHAPE_ONLY",
    "critic_status": "pass",
    "critic_report_path": "pnp3/Candidates/_template/critic_report.md",
    "applicable_spec_version": "0.1.2",
    "attack_suite_version": "0.1.0"
  }
  EOF
  python3 scripts/attempts_append.py < /tmp/fake_pass.json   # → ATT-000001, rc=0
  python3 scripts/validate_jsonl.py outputs/attempts.jsonl   # → OK
  cp /tmp/attempts_backup.jsonl outputs/attempts.jsonl       # restore
  ```
- expected: rejection or at minimum a downgrade to `critic_status = not_run`
  unless a real Critic report is presented.
- actual: ledger entry is created with `id = ATT-000001` and validation
  reports `OK`. Three additional variants confirmed:
  4b. `critic_status: pass` with no `critic_report_path` → accepted.
  4c. `critic_status: pass` with a non-existent path → accepted.
  4d. `verifier_status: PASS` with `critic_status: not_run` → accepted
      (see Finding 2).
- recommendation:
  1. Add `scripts/check_critic_report.py` (or similar) that parses
     `critic_report.md` and asserts:
     - presence of all six attack sections in canonical order;
     - none of the attack sections has a "Template" / placeholder
       marker phrase (e.g. `Template placeholder`, `attack not applicable`
       paired with `Template — fill with`);
     - the verdict line matches the actual section statuses
       (`pass` ⇔ no `break found`).
  2. In `attempts_append.py::validate_attempt`, when
     `critic_status ∈ {"pass", "fail"}`, *require*
     `critic_report_path` to be a non-null string AND require that
     path to exist on disk AND require it to satisfy the parser
     above.
  3. Make `verify_candidate.sh` distinguish three Critic-report
     states in `result.json`:
     - `critic_report_present: false` (no file)
     - `critic_report_is_template: true` (file exists but is unmodified
       or contains template markers)
     - `critic_report_complete: true` (file exists and parses clean)
  4. Until (1)–(3) ship, change the template's verdict line from
     `critic_status: pass` to `critic_status: not_run` so that an
     accidentally-shipped template cannot accidentally claim `pass`.

This is the user-flagged primary hardening item, and it reproduces
end-to-end with no manual file edits — a single LLM-driven worker can
populate the ledger with fake `pass` entries today.

### Finding 2 — Verifier-status enum drift (HIGH)

- severity: **high**
- file: `scripts/validate_jsonl.py:66`
- description: `ATTEMPT_VERIFIER_STATUS = {"PASS", "FAIL", "PASS_SHAPE_ONLY"}`,
  but `scripts/verify_candidate.sh` has no code path that emits a
  bare `PASS`. Its three positive aggregate statuses are
  `PASS_SHAPE_ONLY`, `HUMAN_REVIEW_REQUIRED`, and `FAIL_<reason>`
  (lines 410–420 of `verify_candidate.sh`). The schema therefore
  permits a `verifier_status` that the live verifier cannot produce,
  meaning a hand-crafted ledger line can claim a stronger pass than
  the verifier ever asserts.
  Conversely, `HUMAN_REVIEW_REQUIRED` (a real verifier output) is
  *not* in the validator enum, so legitimate human-review cycles
  cannot be recorded.
- reproduction:
  ```bash
  echo '{"candidate_id":"x","method_family":"other","verifier_status":"PASS",
         "critic_status":"not_run","applicable_spec_version":"0.1.2",
         "attack_suite_version":"0.1.0"}' \
    | python3 scripts/attempts_append.py
  # → rc=0, ATT-... assigned
  ```
- expected: `verifier_status` enum should equal the verifier's actual
  output set: `{PASS_SHAPE_ONLY, HUMAN_REVIEW_REQUIRED, FAIL}`, with
  the convention that `FAIL` covers all `FAIL_*` reasons (the reason
  is captured separately in `verifier_failure_class`).
- actual: bare `PASS` accepted.
- recommendation: align the enum to `{PASS_SHAPE_ONLY,
  HUMAN_REVIEW_REQUIRED, FAIL}` and remove `PASS`.

### Finding 3 — Spec-version skew between target.toml and known_guards.toml (MEDIUM)

- severity: **medium** (governance hygiene)
- files:
  - `spec/target.toml:11`: `spec_version = "0.1.0"`,
    `last_reviewed = "2026-04-30"`
  - `spec/known_guards.toml:27`: `spec_version = "0.1.2"`,
    `last_reviewed = "2026-05-01"`
  - `outputs/nogolog.jsonl::NOGO-000001`: `applicable_spec_version = "0.1.1"`
  - `outputs/nogolog.jsonl::NOGO-000002`, `NOGO-000003`:
    `applicable_spec_version = "0.1.2"`
  - `seed_packs/fp3b1_log_width_hardwiring/README.md:181`:
    workers will record `applicable_spec_version = "0.1.2"`
- description: `target.toml` itself instructs (line 8): "Bump
  [meta].spec_version on any change. The verifier records which
  spec_version was in force at the time of a candidate's verification."
  But `target.toml` has not been bumped despite known-guards
  evolving 0.1.0 → 0.1.1 → 0.1.2. The verifier therefore emits
  `spec_version: "0.1.0"` in its `result.json` while workers will
  legitimately stamp attempts with `applicable_spec_version: "0.1.2"`.
  Auditors comparing the two artifacts will see a discrepancy and
  cannot tell which side is canonical.
- recommendation: bump `target.toml::[meta].spec_version` to
  `0.1.2` and `last_reviewed` to the same date as
  `known_guards.toml`, in a governance-only PR. Optionally, add a
  cross-check in `scripts/check_target_lock.sh` that the two files
  agree.

### Finding 4 — Rule-16 candidate scan bypass via leading underscore (HIGH)

- severity: **high** for autoresearch (must be fixed before scaling)
- file: `scripts/check_candidate_rule16.sh:65-74`
- description: the candidate-directory enumerator excludes any path
  whose component starts with `_`:
  ```awk
  for (i = 1; i <= NF; i++) {
    if ($i ~ /^_/) { skip = 1; break }
  }
  ```
  The intent (per the comment) is to skip `_template/` and
  `_scratch/`. The actual effect is that any candidate dir
  `pnp3/Candidates/_anything/` (or
  `pnp3/Candidates/<family>/_anything/`) is silently skipped from
  the Rule-16 scan, while still being a valid `pnp3/Candidates/`
  candidate as far as `verify_candidate.sh` is concerned. The
  script even prints `[rule16] OK (no real candidates yet; only
  pnp3/Candidates/_template excluded)`, which is *misleading* —
  the filter excluded my probe directory `_sneaky_attempt`, not
  just `_template`.
- reproduction:
  ```bash
  mkdir -p pnp3/Candidates/_sneaky_attempt
  cat > pnp3/Candidates/_sneaky_attempt/proof.lean <<'EOF'
  namespace Pnp3.Candidates.SneakyAttempt
  class HiddenGapProvider where
    payload : True
  end Pnp3.Candidates.SneakyAttempt
  EOF
  touch pnp3/Candidates/_sneaky_attempt/{manifest.toml,sketch.md,barrier_certificate.md,self_attack.md}
  bash scripts/check_candidate_rule16.sh
  # → "[rule16] OK (no real candidates yet; only pnp3/Candidates/_template excluded)" — rc=0
  rm -rf pnp3/Candidates/_sneaky_attempt
  ```
- expected: only an explicit allowlist (`_template`, `_scratch`,
  perhaps `_archive`) is excluded; any other leading-underscore
  directory is either scanned or rejected with a clear error.
- actual: any leading-underscore name slips past Rule-16.
- recommendation: replace the regex test with a literal allowlist:
  ```bash
  case "$(basename "$dir")" in
    _template|_scratch|_archive) skip=1 ;;
    _*) echo "[rule16] FAIL: candidate dir name '$dir' starts with '_' but is not on the audit allowlist"; fail=1 ;;
    *) skip=0 ;;
  esac
  ```
  Mitigation today: a hidden-payload class wired to
  `ResearchGapWitness` would still trip the source-theorem-size
  check (`bridge ... must mention ResearchGapWitness`), so the
  bypass is not yet end-to-end exploitable for actually claiming a
  gap; but Rule-16 is supposed to be a hard guard, not optional
  defense in depth.

### Finding 5 — `verify_candidate.sh --candidate` accepts arbitrary paths (MEDIUM)

- severity: **medium** (defense-in-depth hole; not exploitable today
  end-to-end because of size/bridge check, see below)
- file: `scripts/verify_candidate.sh:74-105`
- description: the `--candidate` argument is taken verbatim and
  joined into shell-relative paths; there is no check that the
  directory is under `pnp3/Candidates/`. The Rule-16 scan however
  (Finding 4) only walks `pnp3/Candidates/`, so a candidate placed
  outside the tree (e.g. `/tmp/rogue_v2/`) bypasses Rule-16
  altogether. The candidate-shape check, barrier check, and size
  check still run against the supplied path, so a rogue candidate
  will fail at the size/bridge stage if its bridge does not mention
  `ResearchGapWitness`.
- reproduction: `mkdir /tmp/rogue_v2; …; scripts/verify_candidate.sh --candidate /tmp/rogue_v2 --json …`
  produced `status = FAIL_source_theorem_size` (rejected), but with
  `typeclass_payload_quarantine: PASS` despite the proof.lean
  containing a forbidden `class HiddenGapProvider where` —
  Rule-16 was simply not invoked on the file.
- recommendation: in `verify_candidate.sh`, normalise the path and
  reject a `--candidate` whose canonicalisation does not start with
  `${ROOT_DIR}/pnp3/Candidates/`. In `check_candidate_rule16.sh`,
  also accept an explicit `--dir <path>` to scan an arbitrary
  directory when invoked standalone, so the verifier can pass the
  exact `--candidate` path through.

### Finding 6 — Critic protocol has no machine-readable schema check (HIGH)

- severity: **high** (blocks scaling, complementary to Finding 1)
- file: `spec/critic_protocol.md`, `pnp3/Candidates/_template/critic_report.md`
- description: `spec/critic_protocol.md` §2–3 mandates a fixed
  Markdown schema (six attack sections in fixed order, each with
  `status` / `summary` / `evidence` fields, and the verdict block
  with `critic_status`, `dominant_break_class`,
  `dominant_break_section`, `next_recommended_action`). §3 is
  explicit: "`critic_status = pass` is allowed iff every attack
  section has `status ∈ {no break found, attack not applicable}`."
  But there is no script that parses a `critic_report.md` and
  enforces the schema or the `pass` precondition. The template
  exploits this by setting all six statuses to `attack not applicable`
  with placeholder evidence and then claiming `pass` — a tautology
  the protocol explicitly does *not* sanction.
- recommendation:
  1. Implement `scripts/check_critic_report.py <path>` that parses
     the Markdown into the six sections, validates each section's
     three fields, validates the verdict block, and exits non-zero
     on any violation. Reject section bodies whose `evidence`
     bullets contain only placeholder text such as `Template`,
     `Replace this`, or `Template — fill with`.
  2. Wire it into `scripts/check.sh` Step 12 (alongside the JSONL
     validator) and into `scripts/verify_candidate.sh` so a
     candidate that ships a present-but-template critic report
     gets `critic_report_complete: false` in `result.json`.
  3. Append a corresponding probe to
     `bench/SmokeProbe/expected_results.json` so future regressions
     are caught.

### Finding 7 — `attempts.jsonl` has no link to a reproducible verifier-result.json (HIGH)

- severity: **high**
- file: `scripts/attempts_append.py`, `scripts/validate_jsonl.py`,
  `scripts/verifier_result_schema.json`
- description: an attempts-ledger line records `verifier_status`
  but carries no pointer to (or hash of) the `result.json` that the
  verifier produced. Combined with Finding 2 (the enum permits
  values the verifier never emits), this means the trust model is
  purely "the worker is honest". Once Pilot Wave 0 has multiple
  workers, there is no audit way to verify that a recorded
  `verifier_status: PASS_SHAPE_ONLY` actually came from a real
  verifier run.
- recommendation: extend the AttemptLedgerEntry schema with a
  required `verifier_result_path` (path:line of a stored
  `result.json` snapshot in `outputs/verifier_results/<ATT-id>.json`)
  or a content hash. The verifier should write its `result.json`
  into a worker-private artifact directory and `attempts_append.py`
  should refuse entries whose `verifier_status` does not match
  `result.status`.

### Finding 8 — NOGO-000003 prose contradicts FP-3b.1 packaging correction (MEDIUM)

- severity: **medium** (onboarding hazard)
- file: `outputs/nogolog.jsonl::NOGO-000003.notes` vs.
  `seed_packs/fp3b1_log_width_hardwiring/README.md` §4
- description: NOGO-000003 documents a "lift" plan that includes
  step (iv): "packaging into `InPpolyFormula (fun _ _ => false)`
  with `polyBound n := 6*(n+1)` and `c = 11` for `polyBound_poly`".
  The seed pack §4 ("CRITICAL packaging correction") explicitly
  marks this packaging as *wrong* (the `InPpolyFormula.correct`
  field would not hold for `L = const false`) and gives the correct
  shape `adversaryLanguage := fun n x => FormulaCircuit.eval
  (adversaryFamily n) x` with `correct := by intro n x; rfl`.
  Because Rule 9 makes JSONL append-only, NOGO-000003 cannot be
  rewritten — but a worker who reads the NoGoLog before the seed
  pack will follow the wrong recipe.
- recommendation: the FP-3b.1 result MUST append a *new* NOGO entry
  (e.g. `NOGO-000004`) with `supersedes: "NOGO-000003"`, status
  `formalized`, and `notes` pointing at the corrected packaging.
  The seed pack's acceptance criterion §7.6 already requires this;
  highlight it in §1 of the seed pack README so a worker sees the
  contradiction up front.

### Finding 9 — `critic_report_present` semantics overload (MEDIUM)

- severity: **medium** (precursor to Finding 1)
- file: `scripts/verify_candidate.sh:181-185`, `scripts/verifier_result_schema.json`
- description: the verifier emits `critic_report_present: true`
  iff the file exists on disk. There is no check on the file's
  contents. Downstream tooling (or a worker) that interprets
  `critic_report_present == true` as "Critic report is real" will
  accept the unmodified template.
- recommendation: split the field into
  `critic_report_present: bool` (file exists) and
  `critic_report_complete: bool | null` (file parses, schema valid,
  no template placeholders) — `null` until the parser of Finding 6
  ships, then `bool`. This change is backwards-compatible with the
  existing schema (just an additional optional field).

### Finding 10 — No worker identity / reproducibility metadata in attempts ledger (MEDIUM)

- severity: **medium** for scaling
- file: `spec/nogolog_schema.json`, `scripts/attempts_append.py`
- description: per Rule 12, "Generator and Critic identity is
  recorded in the NoGoLog entry". The attempts-ledger schema today
  has no `generator_identity` / `critic_identity` /
  `generator_seed` / `critic_seed` / `git_sha` fields. With
  multiple workers running in parallel, there is no way to attribute
  an attempt to the agent that produced it, nor to confirm Rule 12
  diversity (Generator and Critic must use different snapshots /
  templates / seeds).
- recommendation: add optional fields `generator_identity`,
  `critic_identity`, `generator_seed`, `critic_seed`, and `git_sha`
  to `AttemptLedgerEntry`. Make them required for any line whose
  `verifier_status != FAIL` once Pilot Wave 0 closes.

### Finding 11 — Append-only ledger is unsigned (LOW / INFO)

- severity: **low** for MVP, **medium** before any public claim
- description: `outputs/attempts.jsonl` and `outputs/nogolog.jsonl`
  are plain text on shared filesystem. Any process can append.
  This is acceptable at MVP scale (single-repo, manual review of
  PRs) but becomes risky once 10–20 workers append concurrently.
- recommendation: not a blocker for Pilot Wave 0. Track for
  Autoresearch MVP-5: hash-chain the ledger (each entry includes
  `prev_id_hash`), or co-commit a Sigstore signature.

## 5. Negative controls performed

| # | Test                                          | Expected | Actual | Verdict |
| - | --------------------------------------------- | -------- | ------ | ------- |
| 1 | `class FakeGapProvider where` in candidate-local `pnp3/Candidates/test_hidden_payload/proof.lean` | Rule-16 hard reject | `[rule16] FAIL (hard): forbidden declaration ... pattern: ^[[:space:]]*class[[:space:]]+[A-Za-z]` | PASS |
| 2 | `def shameless := Magnification.FormulaSupportRestrictionBoundsPartial` in candidate-local proof.lean | refuted-predicate-usage hard reject | `[refuted-predicate] FAIL: bare 'FormulaSupportRestrictionBoundsPartial' in hard-fail zone (code-level)` rc=1 | PASS |
| 3 | `axiom P_ne_NP_unconditional : Pnp3.ComplexityInterfaces.P_ne_NP` in candidate-local proof.lean | doc-honesty + target-lock hard reject | both `check_doc_honesty.sh` and `check_target_lock.sh` rc=1 with `phantom 'axiom P_ne_NP_unconditional' detected` | PASS |
| 4a | `attempts_append.py` with `critic_status:pass` + `critic_report_path` pointing at unmodified `_template/critic_report.md` | reject | accepted, `ATT-000001` written | **FAIL — see Finding 1** |
| 4b | `attempts_append.py` with `critic_status:pass` and no `critic_report_path` | reject | accepted | **FAIL — see Finding 1** |
| 4c | `attempts_append.py` with `critic_status:pass` and non-existent `critic_report_path` | reject | accepted | **FAIL — see Finding 1** |
| 4d | `attempts_append.py` with `verifier_status: "PASS"` | reject (verifier never emits PASS) | accepted | **FAIL — see Finding 2** |
| 5 | `_sneaky_attempt` candidate dir bypassing Rule-16 | scan should fail or reject the dir name | `[rule16] OK` with misleading message | **FAIL — see Finding 4** |
| 6 | `/tmp/rogue_v2` candidate dir with `class HiddenGapProvider` and full manifest | Rule-16 should fail | `typeclass_payload_quarantine: PASS`, defeated only by `source_theorem_size` later | **FAIL — see Finding 5** |
| smoke 1–8 | shipped negative-control suite | all pass | 8/8 PASS | PASS |

In total: 7 of 8 substantive negative controls passed; **4 distinct
controls (4a/4b/4c/4d)** failed against the new MVP-3 / MVP-4 surface;
**2 additional controls (5, 6)** revealed pre-existing Rule-16 scope
gaps that the new MVP exacerbates by introducing more candidate
trust.

## 6. Critic dry-run verdict

- target: `Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.InSupportFunctionalDiversity`
  (the FP-3-actual provenance filter under attack by seed pack
  `fp3b1_log_width_hardwiring`)
- protocol: `spec/critic_protocol.md` six-attack format
- the dry-run is performed on the *filter shape*, not on a candidate
  package, since FP-3b.1 is audit-only routing.

### Attack 1 — Hidden-payload attack
- status: `no break found`
- summary: `InSupportFunctionalDiversity` is a plain Lean `def` over
  the existing trust-root record `InPpolyFormula`. It does not use
  `class`, `instance`, `Fact`, `opaque`, or `noncomputable def`. The
  surrounding probe file declares only `abbrev`/`def`/`theorem`
  forms; no payload provider channel is introduced.
- evidence:
  - `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:231-234`
    — defining `def`, no typeclass parameters.
  - `scripts/check_typeclass_payload_quarantine.sh` PASS on the
    audited tree.

### Attack 2 — Hardwiring attack
- status: **`break found`**
- summary: The seed pack `fp3b1_log_width_hardwiring` describes a
  log-width truth-table-shaped adversary that satisfies both
  conjuncts of `InSupportFunctionalDiversity`
  (unboundedness + infinitely-often-non-saturated) while internally
  being exhaustive truth-table on a `k(n) = O(log n)`-wide window.
  At lengths `n = 2^t`, the support cardinality is exactly `t`,
  which is unbounded over `n` and strictly less than `n`. The
  truth-table size is `O(2^t · t) = O(n · log n)`, polynomially
  bounded. NOGO-000003 already records this as
  `failure_class = hardwiring`, status `needs_review`. The seed
  pack itself frames the construction as the *intended* refutation
  of `InSupportFunctionalDiversity` as a provenance filter.
- evidence:
  - `outputs/nogolog.jsonl::NOGO-000003` — log-width hardwiring
    counterexample family, `failure_class: hardwiring`,
    `supersedes: NOGO-000002`.
  - `seed_packs/fp3b1_log_width_hardwiring/README.md` §1 ("If the
    construction succeeds, the candidate filter
    `InSupportFunctionalDiversity` is dead as a provenance filter").
  - `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:236-281`
    — the dual exclusion lemma
    `InSupportFunctionalDiversity_excludes_uniformPolyBound`
    applies only to *uniformly-bounded* `polyBound` and explicitly
    does not cover log-width hardwiring (cf. file comment lines
    256-264).

### Attack 3 — KnownGuards-factorization attack
- status: `attack not applicable`
- summary: `spec/known_guards.toml` has only one `accepted` guard
  (`HardwiringGuard`) flagged `outcome_b_usage = "obstruction_only"`,
  `standalone_factorization_target = false`. `ProvenanceFilter_v1`
  is `informal`. Per `FixedParams_Probe.md` §3.B, a factorization
  attack requires an `accepted` guard with
  `standalone_factorization_target = true`; none exist. The filter
  is therefore not subject to factorization.
- evidence: `spec/known_guards.toml:39-58` (HardwiringGuard's
  `outcome_b_usage = "obstruction_only"`),
  `spec/known_guards.toml:84-94` (ProvenanceFilter_v1 informal).

### Attack 4 — Natural-proof / relativization / algebrization barrier audit
- status: `no break found`
- summary: the filter is a pure structural condition on the support
  cardinality function of an `InPpolyFormula L` record and does
  not invoke a "useful, large, constructive" predicate over
  Boolean functions, an oracle-relative argument, or an algebraic
  extension. Razborov-Rudich / BGS / Aaronson-Wigderson
  obstructions do not apply at this stage; the filter is
  pre-mathematical.
- evidence: definitional check of `InSupportFunctionalDiversity`;
  no relativization-sensitive primitives in the dependency closure
  (the closure stops at `FormulaCircuit.support`/`size`, which are
  combinatorial, not oracle-relative).

### Attack 5 — Collapse-not-contradiction audit
- status: `attack not applicable`
- summary: `InSupportFunctionalDiversity` is a candidate provenance
  predicate, not a separation result. It does not assert any
  collapse / contradiction shape (no "if NP ⊆ P/poly then ..."
  consequence is claimed).
- evidence: definitional inspection.

### Attack 6 — Vacuity / source-theorem rephrasing audit
- status: **`break found`** (mild, preliminary)
- summary: NOGO-000002 already records the alternating-slice
  multi-slice hardwiring counterexample as `failure_class: hardwiring`
  with `status: formalized`. NOGO-000003 supersedes it with the
  log-width sub-case as `needs_review`. The filter therefore
  already has a documented vacuity issue: it was designed to
  exclude single-slice truth-table hardwiring (Probe 2) but admits
  multi-slice / log-width hardwiring shapes whose support functions
  satisfy both conjuncts. This is structurally a vacuity break,
  not just a hardwiring break (it is the same construction reused
  in §2 above; it counts here because the *predicate structure*
  is exactly the rephrasing of the previously-refuted
  single-slice-only filter).
- evidence: `outputs/nogolog.jsonl::NOGO-000002` (alternating-slice,
  formalized) and `NOGO-000003` (log-width, needs_review).

### Verdict
- **critic_status:** `fail`
- **dominant_break_class:** `hardwiring`
- **dominant_break_section:** `2`
- **next_recommended_action:** Run FP-3b.1 (formalize the log-width
  adversary per the seed pack), then upgrade NOGO-000003 to
  `formalized`. Until that happens, do not promote
  `ProvenanceFilter_v1` to `accepted` and do not start FP-4.

This matches the user's prior expectation in §11 of the audit
instructions ("Скорее всего, текущий InSupportFunctionalDiversity
должен получить: critic_status = fail, dominant_break_class =
hardwiring, dominant_break_section = Attack 2"). The slight
strengthening here is recording Attack 6 also as a `break found`
because the issue is structural (cardinality-only filter) and not
purely about a single hardwiring construction.

## 7. FP-3b.1 assessment

- packaging correction respected? **yes (in the seed pack)**, but
  partially **contradicted** by `NOGO-000003.notes` (Finding 8).
  A worker who reads only NOGO-000003 will use the wrong recipe;
  a worker who reads the seed pack first will use the right one.
- adversary formalizable? **yes, with caveat.** The seed pack §5
  power-of-two-slice variant is the right escape hatch:
  - width `k_pow2 n := t` if `n = 2^t` else `0` is decidable via
    `Nat.isPowerOfTwo` (Mathlib provides it).
  - `(ttFormula f).size ≤ 6 · 2^k` is induction over `k`; the
    existing Probe 2 infrastructure
    (`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean::ttFormula`,
    `FormulaCircuit.rename`) is already in tree and is the right
    primitive to lift on.
  - polyBound: `polyBound n := if n = 2^t then 6·n·(t+1) else 1`
    is bounded by `6·n²` for `n ≥ 2`, satisfying `polyBound_poly`
    with a small `c`.
  - `correct := by intro n x; rfl` works under the seed pack's
    corrected packaging because the language is *defined* to be
    `eval (adversaryFamily n)`.
- estimated Lean effort: 100–200 lines (matches the seed pack §6
  estimate). The hard sub-lemma is `FormulaCircuit.rename`
  preserving size and transporting support along an injective `σ`
  with cardinality preservation. Probe 2 already has the size
  side; the support side is the new piece.
- blockers: none formal. The principal practical risk is that the
  worker spends time on the `Nat.log` heavy path instead of the
  power-of-two slice; the seed pack §5 mitigates this explicitly.
- recommendation: run FP-3b.1 as **Seed Task A** of Pilot Wave 0
  *after* the Critic-trap hardening (Findings 1, 6) ships;
  otherwise the FP-3b.1 result will be admitted to the ledger
  with an unverifiable `critic_status` field. The math itself is
  ready.

## 8. Go / No-Go

- **Pilot Wave 0**: **GO with caveats.**
  Conditional on (a) shipping a *minimal* fix for Finding 1 (even
  just changing the template's verdict line from `pass` to `not_run`,
  and rejecting `attempts_append.py` entries where
  `critic_status ∈ {pass, fail}` and `critic_report_path` is
  null/missing) and (b) at most one human-driven worker (the seed-
  pack author themself or one designated reviewer) for FP-3b.1.
  The shipped automated negative-control coverage (smoke 8/8) is
  sufficient for one trusted worker; it is not sufficient for
  unsupervised LLM workers.
- **Scaling to 10–20 workers**: **NO-GO.**
  Findings 1, 2, 4, 6, 7 must all ship before unsupervised
  multi-worker autoresearch. Without (1) and (6) the ledger is
  forge-able by any worker. Without (4) and (5) Rule-16 is bypassable
  by candidate-dir naming. Without (2) the verifier-status field is
  forgeable. Without (7) there is no audit chain from a recorded
  pass to a real verifier run.
- **FP-4**: **NO-GO.**
  Per the audit instructions §15, FP-4 is forbidden until
  NOGO-000003 is `formalized`, `ProvenanceFilter_v1` remains
  `informal`, and no candidate has survived a real Critic. None of
  these conditions is met today; FP-3b.1 is the gating prerequisite.

## 9. Top 5 recommendations

1. **Close the template-critic trap (Finding 1, 6).** Ship
   `scripts/check_critic_report.py` that parses the Markdown report
   and asserts the six-attack schema + non-template evidence, and
   wire it into both `attempts_append.py` (when `critic_status ∈
   {pass, fail}`) and `scripts/check.sh`. As an immediate stopgap
   before that lands, change `_template/critic_report.md` so its
   verdict says `critic_status: not_run` (the template caveat in
   the file already explains this is the intended semantics).
2. **Tighten the `_*` exclusion in `check_candidate_rule16.sh`
   (Finding 4).** Replace the regex with a literal allowlist
   (`_template`, `_scratch`, `_archive`); reject other
   leading-underscore names with a clear error rather than a
   silent skip whose log message is misleading.
3. **Align the `verifier_status` enum and add a verifier-result
   pointer (Findings 2, 7).** Drop bare `PASS` from
   `validate_jsonl.py::ATTEMPT_VERIFIER_STATUS`; add
   `HUMAN_REVIEW_REQUIRED`; require `verifier_result_path` (or
   hash) on any non-FAIL attempt entry; cross-check the recorded
   `verifier_status` against the referenced `result.json`.
4. **Bump `spec/target.toml::[meta].spec_version` to 0.1.2 to match
   `known_guards.toml` (Finding 3),** and add a cross-version
   consistency check to `scripts/check_target_lock.sh`. Without
   this, every FP-3b.1 attempt entry will record an
   `applicable_spec_version` that doesn't match the verifier's
   `result.json::spec_version`, producing audit confusion.
5. **Run FP-3b.1 as a single trusted-human-worker pilot, not as the
   first multi-worker autoresearch wave.** Recommendations 1–3
   close the LLM-attack surface; until they ship, treat FP-3b.1 as
   a manual research task with one author and one reviewer. Use
   the pilot to populate the first non-empty `attempts.jsonl` line
   *and* the first real (non-template) `critic_report.md`. Those
   two artifacts are the prerequisites for scaling to 10–20
   workers — not green CI on its own.
