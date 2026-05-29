# Independent audit report

## 1. Environment
- branch: claude/research-governance-phase0-lmZBP
- commit: 7dcba2c7cce8b251f9e936d7aacee4dc5c9eb601
- lake version: Lake version 5.0.0-src+6a60de2 (Lean version 4.22.0-rc2)
- OS: Linux devbox 6.8.0 x86_64
- commands run: `lake build PnP3 Pnp4`, `./scripts/check.sh`, `python3 scripts/validate_jsonl.py`, `python3 scripts/attempts_append.py`, etc.

## 2. Baseline result
- lake build PnP3 Pnp4: PASS
- ./scripts/check.sh: PASS (17/17)
- smoke: PASS
- JSONL validation: PASS

## 3. Scope compliance
- Did latest branch modify trust root? no
- Any unauthorized P_ne_NP_unconditional? no
- Any hidden payload channel found? no
- Any unmarked refuted route found? no

## 4. Findings
### Finding 1
- severity: blocker
- file: scripts/attempts_append.py
- line: N/A
- description: The Autoresearch MVP-4 critic protocol adds a `pnp3/Candidates/_template/critic_report.md` template. This template ships with `- **critic_status:** \`pass\`` as a placeholder. The attempt append script (`scripts/attempts_append.py`) and verifier do not check if a passed `critic_status` was actually just copied from the template default. This means tooling can mistakenly record `critic_status=pass` directly off the template, undermining the entire adversarial review process.
- reproduction: `python3 -c "import json; print(json.dumps({'candidate_id': '_template', 'method_family': 'ac0_locality_support', 'verifier_status': 'PASS_SHAPE_ONLY', 'critic_status': 'pass', 'applicable_spec_version': '0.1.0', 'attack_suite_version': '0.1.0'}))" | scripts/attempts_append.py`. It accepts the entry.
- expected: Tooling MUST reject or not automatically assume `critic_status=pass` if the `critic_report.md` file still contains template markers like `Template placeholder` or if the `attempts_append.py` doesn't verify the report content.
- actual: `attempts_append.py` happily accepts `critic_status: pass`.
- recommendation: Implement a hardening check (e.g. `check_critic_template.sh` or in Python) that parses the `critic_report.md`. If it contains `Template placeholder`, it MUST NOT be accepted as `critic_status: pass`.

## 5. Negative controls performed
- test: Hidden payload candidate
- expected: Verifier FAIL due to Rule 16 or SourceTheorem size policy.
- actual: `FAIL_source_theorem_size: returned 1 (status=unknown)`. Missing source theorem and missing bridge.
- verdict: PASS

## 6. Critic dry-run verdict
- target: FP3Attempt.InSupportFunctionalDiversity
- critic_status: fail
- dominant_break_class: hardwiring
- dominant_break_section: 2
- summary: The candidate filter admits a truth-table-shaped hardwired family on a sublinear/log-width window of variables. The log-width hardwiring completely defeats the diversity constraint.

## 7. FP-3b.1 assessment
- packaging correction respected? yes
- adversary formalizable? yes
- estimated Lean effort: 150-200 lines
- blockers: Requires formalizing `Nat.log` or power-of-two slice which may be slightly cumbersome but is standard.
- recommendation: Strongly recommend utilizing the power-of-two slice variant outlined in the seed pack to avoid the `Nat.log` overhead.

## 8. Go / No-Go
- Pilot Wave 0: GO (with conditions)
- Scaling to 10–20 workers: NO-GO (needs template critic guard)
- FP-4: NO-GO (waiting on FP-3b.1 completion)

## 9. Top 5 recommendations
1. Implement a template critic guard to ensure `critic_report_present` does not imply `critic_completed/pass` when the report retains template text.
2. Formalize FP-3b.1 using the power-of-two slice approach.
3. Ensure no `critic_status: pass` is logged without a corresponding human review or LLM verification step that confirms all sections are filled.
4. Keep the strict `SourceTheorem` size limits.
5. Do not proceed to FP-4 until NOGO-000003 is upgraded to `formalized`.
