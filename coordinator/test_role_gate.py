#!/usr/bin/env python3
"""End-to-end role-gate test —
Research Governance v0.1, MVP-0.4 (Phase D).

Exercises the Rule-12 (Generator/Critic separation) enforcement
that MVP-0.4 added to `POST /v1/result`:

  Test 1 (gen-as-crit):
    a Generator-role submission carrying critic_status='pass' is
    rejected (403) even though the worker_id has the gen- prefix.

  Test 2 (crit-as-gen):
    a Critic-role submission carrying critic_status='not_run' is
    rejected (403).

  Test 3 (gen-and-crit-same-worker):
    worker `gen-alice` generates an attempt (success), then the
    SAME worker tries to submit a critic verdict for that
    attempt under the crit-* prefix.  The role-gate refuses
    (Rule 12) — even if the worker_id is rebranded `crit-alice`
    on a separately-leased crit assignment, the supersedes
    target's worker_id is `gen-alice`, so the prefix-rebrand
    doesn't escape.

    For MVP-0.4 the simple sub-test uses worker_id = "gen-alice"
    on a crit-leased assignment, which is rejected at /v1/task
    by the existing prefix check; we then directly probe the
    role_gate by constructing a crit assignment for the same
    underlying worker base name, which the supersedes-lookup
    catches.

  Test 4 (gen-and-crit-different-worker):
    `gen-alice` generates; `crit-bob` submits a critic verdict
    that supersedes alice's attempt.  Allowed.

The test reuses the stub-repo + coordinator-subprocess pattern
from coordinator/test_coordinator.py.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

import random
TEST_PORT = 21000 + random.randint(0, 999)
COORDINATOR_URL = f"http://127.0.0.1:{TEST_PORT}"


def _stage_stub_repo(tmp: Path) -> Path:
    stub = tmp / "stub_repo"
    stub.mkdir(parents=True, exist_ok=True)
    for sub in ("scripts", "spec", "outputs", "seed_packs", "coordinator"):
        (stub / sub).mkdir(parents=True, exist_ok=True)
    for name in (
        "attempts_append.py", "nogolog_append.py", "survivor_append.py",
        "validate_jsonl.py", "validate_critic_report.py",
    ):
        shutil.copy2(ROOT / "scripts" / name, stub / "scripts" / name)
    for name in (
        "nogolog_schema.json", "version_manifest.toml",
        "concurrency_model.md", "critic_protocol.md",
        "target.toml", "known_guards.toml", "provider_audit_registry.toml",
        "source_theorem_size_policy.md", "implicit_assumption_channels.md",
        "frozen_spec_plan.md",
    ):
        src = ROOT / "spec" / name
        if src.exists():
            shutil.copy2(src, stub / "spec" / name)
    for name in ("attempts.jsonl", "nogolog.jsonl", "survivor_history.jsonl"):
        (stub / "outputs" / name).write_text("")
    sp = stub / "seed_packs" / "role_gate_smoke_pack"
    sp.mkdir(parents=True, exist_ok=True)
    (sp / "README.md").write_text(
        "# Synthetic seed pack used only by role-gate e2e test.\n")
    for name in ("__init__.py", "schema.py", "store.py", "dedup.py",
                 "leases.py", "ledger.py", "role_gate.py", "wave_gate.py",
                 "metrics.py", "server.py",
                 # v0.4.2 Track C2 / C3 / C4.
                 "cost_budget.py", "critic_dispatcher.py",
                 "promotion_evaluator.py"):
        shutil.copy2(ROOT / "coordinator" / name,
                     stub / "coordinator" / name)
    src_th = ROOT / "spec" / "wave_gate_thresholds.toml"
    if src_th.exists():
        shutil.copy2(src_th, stub / "spec" / "wave_gate_thresholds.toml")
    src_cb = ROOT / "spec" / "cost_budget_thresholds.toml"
    if src_cb.exists():
        shutil.copy2(src_cb, stub / "spec" / "cost_budget_thresholds.toml")
    return stub


def _start_coordinator(stub: Path) -> subprocess.Popen:
    env = os.environ.copy()
    env["PYTHONPATH"] = str(stub)
    env["AUTORESEARCH_INITIAL_WAVE"] = "2"  # bypass Wave-0 cap=10
    env["AUTORESEARCH_PROMOTION_FORCE"] = "true"  # PR 5 guard opt-in
    proc = subprocess.Popen(
        [sys.executable, "-m", "coordinator.server",
         "--bind", "127.0.0.1", "--port", str(TEST_PORT),
         "--db", str(stub / "coordinator" / "state.db"),
         "--quiet"],
        cwd=stub,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    for _ in range(50):
        try:
            with urllib.request.urlopen(
                    COORDINATOR_URL + "/v1/health", timeout=1) as r:
                if r.status == 200:
                    return proc
        except (urllib.error.URLError, ConnectionError):
            pass
        time.sleep(0.1)
    err = proc.stderr.read().decode("utf-8", "replace") if proc.stderr else ""
    proc.kill()
    raise RuntimeError(f"coordinator failed to come up: {err}")


def _http_get(path: str) -> tuple[int, dict]:
    req = urllib.request.Request(COORDINATOR_URL + path, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=5) as r:
            return r.status, json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read().decode("utf-8"))


def _http_post(path: str, body: dict) -> tuple[int, dict]:
    payload = json.dumps(body).encode("utf-8")
    req = urllib.request.Request(
        COORDINATOR_URL + path,
        data=payload,
        method="POST",
        headers={"Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as r:
            return r.status, json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read().decode("utf-8"))


def _take_task(role: str, worker_id: str) -> dict:
    code, body = _http_get(
        f"/v1/task?role={role}&worker_id={worker_id}"
        f"&seed_pack=role_gate_smoke_pack")
    assert code == 200, f"task {role}/{worker_id} returned {code}: {body}"
    return body


def _attempt_body(candidate_id: str, **overrides) -> dict:
    base = {
        "candidate_id": candidate_id,
        "method_family": "ac0_locality_support",
        "verifier_status": "PASS_SHAPE_ONLY",
        "critic_status": "not_run",
        "applicable_spec_version": "0.1.0",
        "attack_suite_version": "0.1.0",
    }
    base.update(overrides)
    return base


# ---------------------------------------------------------------------------
# Test cases.
# ---------------------------------------------------------------------------


def run_test_gen_carrying_critic_pass_rejected() -> None:
    """gen-* worker submits attempt with critic_status='pass'.
    Rejected with 403 (Generator submissions must be not_run)."""
    task = _take_task("gen", "gen-rule12-1")
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-rule12-1",
        "attempt": _attempt_body(
            task["candidate_id"],
            critic_status="pass",   # <-- forbidden for gen role
            critic_break_class=None,
        ),
    }
    code, resp = _http_post("/v1/result", body)
    assert code == 403, (
        f"gen with critic_status=pass should be 403, got {code}: {resp}")
    assert "not_run" in resp.get("error", ""), resp
    print("[test_role_gate] OK   gen with critic_status=pass -> 403")


def run_test_crit_carrying_not_run_rejected() -> None:
    """crit-* worker submits attempt with critic_status='not_run'.
    Rejected with 403 (Critic submissions must be pass/fail)."""
    task = _take_task("crit", "crit-rule12-1")
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "crit-rule12-1",
        "attempt": _attempt_body(task["candidate_id"]),  # critic_status='not_run'
    }
    code, resp = _http_post("/v1/result", body)
    assert code == 403, (
        f"crit with critic_status=not_run should be 403, got {code}: {resp}")
    assert "pass" in resp.get("error", "") and "fail" in resp.get("error", ""), \
        resp
    print("[test_role_gate] OK   crit with critic_status=not_run -> 403")


def run_test_gen_then_crit_same_worker_rejected() -> None:
    """gen-alice generates attempt X.  Then a crit-alice submission
    that supersedes X is rejected (Rule 12: same worker base name
    cannot be both Generator and Critic of the same candidate).

    NOTE on naming: the role-gate compares worker_id strings
    verbatim, so "gen-alice" and "crit-alice" are TECHNICALLY
    different worker_ids.  The Rule 12 enforcement is via the
    supersedes lookup: crit-alice's submission carries
    supersedes=ATT-X whose recorded worker_id is "gen-alice".
    The role-gate refuses if those two strings are equal.

    For Phase D we therefore exercise the *exact* invariant: a
    crit-* worker whose `worker_id` matches the gen worker_id
    that produced the supersedes target is rejected.  This is
    triggered by re-using a single suffix, e.g. worker_id =
    "gen-alice" (for both gen and crit phases).  A real Phase E
    deployment will rely on operator discipline to prevent the
    crit-* prefix from being applied to a worker that previously
    ran with the gen-* prefix; the role-gate is the last line of
    defence.

    The minimal test here exercises a slightly stricter version
    of the rule: we make the Critic worker_id literally equal to
    the Generator worker_id (both gen-alice).  This forces
    /v1/task's prefix check to fail when crit role is requested,
    so we drive the test by directly invoking /v1/result against
    a crit-leased assignment using gen-alice's worker_id (which
    /v1/result rejects at the lease-holder check, but that's a
    separate path).

    The clean, focused exercise is to call the role_gate
    in-process (NOT through HTTP) on a synthetic store that
    answers find_worker_for_attempt with the same worker_id.
    That isolates the Rule-12 logic from the HTTP wrapping.
    """
    # In-process exercise of the role_gate logic.  This bypasses
    # HTTP and proves the Rule-12 rejection path itself works.
    sys.path.insert(0, str(ROOT))
    from coordinator.role_gate import enforce_role_for_submission

    class _StubStore:
        def find_worker_for_attempt(self, attempt_id):
            # Pretend ATT-000123 was generated by gen-alice.
            return "gen-alice" if attempt_id == "ATT-000123" else None

    err = enforce_role_for_submission(
        role="crit",
        worker_id="gen-alice",   # same string as the original generator
        attempt={
            "candidate_id": "synthetic_candidate",
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "fail",
            "critic_break_class": "hardwiring",
            "supersedes": "ATT-000123",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
        },
        store=_StubStore(),
    )
    assert err is not None, "role_gate should reject same-worker gen+crit"
    assert "Rule 12" in err, f"error should mention Rule 12: {err!r}"
    print("[test_role_gate] OK   gen+crit same-worker -> Rule 12 reject")


_SYNTHETIC_PASS_REPORT = """\
# Critic report — synthetic_role_gate_e2e

## Attack 1: Hidden-payload attack
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Attack 2: Hardwiring attack
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Attack 3: KnownGuards-factorization attack
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Attack 4: Natural-proof / relativization / algebrization barrier audit
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Attack 5: Collapse-not-contradiction audit
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Attack 6: Vacuity / source-theorem rephrasing audit
- **status:** `no break found`
- **summary:** Synthetic role-gate e2e fixture; references intentional.
- **evidence:**
    - synthetic role-gate e2e fixture; references intentional.

## Verdict
- **critic_status:** `pass`
- **dominant_break_class:** `null`
- **dominant_break_section:** `null`
- **next_recommended_action:** `Synthetic test fixture; do not act.`
"""


def run_test_dispatcher_no_pending_returns_503() -> None:
    """v0.4.2 Track C3: a critic asking for work without a seed_pack
    when no verified gen attempt is available gets 503 with reason
    `no_pending_critic`."""
    # No prior verified gen attempt has been submitted, so the
    # dispatcher's ledger scan finds nothing.  We pick a fresh
    # critic worker_id that has never appeared so previous tests
    # in the suite cannot have left state attributable to it.
    code, body = _http_get(
        "/v1/task?role=crit&worker_id=crit-disp-empty")
    assert code == 503, f"expected 503, got {code}: {body}"
    msg = json.dumps(body).lower()
    assert "no_pending_critic" in msg, body
    print("[test_role_gate] OK   /v1/task crit no-seed-pack with empty "
          "ledger -> 503 no_pending_critic")


def run_test_dispatcher_offers_pending_with_supersedes(stub: Path) -> None:
    """v0.4.2 Track C3: when one verified gen attempt exists, the
    dispatcher returns it via supersedes."""
    # Step 1: gen-eve generates a verified attempt.
    gen_task = _take_task("gen", "gen-eve")
    code, resp = _http_post("/v1/result", {
        "assignment_id": gen_task["assignment_id"],
        "worker_id": "gen-eve",
        "attempt": _attempt_body(gen_task["candidate_id"]),
    })
    assert code == 200, f"gen-eve submission failed: {code}: {resp}"
    gen_attempt_id = resp["attempt_id"]
    # Step 2: crit-frank asks for work; dispatcher picks gen-eve's
    # attempt and stamps supersedes.
    code, body = _http_get(
        "/v1/task?role=crit&worker_id=crit-frank")
    assert code == 200, f"expected 200, got {code}: {body}"
    assert body.get("supersedes") == gen_attempt_id, body
    # Release the assignment so subsequent tests don't see this
    # critic in-flight (the wave cap is generous in the e2e harness
    # but we still avoid pollution).
    _http_post("/v1/release", {
        "assignment_id": body["assignment_id"],
        "worker_id": "crit-frank",
    })
    print("[test_role_gate] OK   /v1/task crit no-seed-pack -> 200 with "
          "supersedes pointing at pending gen attempt")


def run_test_principal_identity_rejects_same_principal(stub: Path) -> None:
    """v0.4.2 Track C3: gen-grace generates; crit-grace submits the
    critic verdict with explicit supersedes.  Rejected by role_gate
    even though worker_ids differ in prefix (principal matches)."""
    # Step 0: stage a synthetic completed Critic report (we'll
    # attach it to the rejected submission so the rejection comes
    # from the principal-identity gate, not from the report
    # cross-field check).
    report_dir = stub / "synthetic_critic_reports"
    report_dir.mkdir(parents=True, exist_ok=True)
    report_path = report_dir / "synthetic_role_gate_principal.md"
    report_path.write_text(_SYNTHETIC_PASS_REPORT)
    rel_report = report_path.relative_to(stub).as_posix()
    # Step 1: gen-grace generates.
    gen_task = _take_task("gen", "gen-grace")
    code, resp = _http_post("/v1/result", {
        "assignment_id": gen_task["assignment_id"],
        "worker_id": "gen-grace",
        "attempt": _attempt_body(gen_task["candidate_id"]),
    })
    assert code == 200, resp
    gen_attempt_id = resp["attempt_id"]
    # Step 2: dispatcher must NOT offer this attempt to crit-grace.
    # Use the explicit-seed-pack path so we get a fresh assignment
    # without going through the dispatcher (which would itself
    # refuse with 503).
    crit_task = _take_task("crit", "crit-grace")
    code, resp = _http_post("/v1/result", {
        "assignment_id": crit_task["assignment_id"],
        "worker_id": "crit-grace",
        "attempt": _attempt_body(
            crit_task["candidate_id"],
            verifier_status="PASS_SHAPE_ONLY",
            critic_status="pass",
            supersedes=gen_attempt_id,
            critic_report_path=rel_report,
        ),
    })
    assert code == 403, f"expected 403, got {code}: {resp}"
    err_text = json.dumps(resp).lower()
    assert "principal" in err_text, resp
    print("[test_role_gate] OK   crit-grace + gen-grace -> 403 "
          "(principal identity guard)")


def run_test_gen_then_crit_different_worker_accepted(stub: Path) -> None:
    """gen-alice generates attempt X.  Then crit-bob submits a
    critic verdict that supersedes X.  Allowed."""
    # Step 0: stage a synthetic completed Critic report inside the
    # stub repo so MVP-0.1.1 cross-field validation accepts the
    # critic_status='pass' submission.
    report_dir = stub / "synthetic_critic_reports"
    report_dir.mkdir(parents=True, exist_ok=True)
    report_path = report_dir / "synthetic_role_gate_pass.md"
    report_path.write_text(_SYNTHETIC_PASS_REPORT)
    # validate_attempt resolves critic_report_path RELATIVE to the
    # repo root (which for the subprocess coordinator is `stub`).
    rel_report = report_path.relative_to(stub).as_posix()

    # Step 1: gen-alice generates.
    gen_task = _take_task("gen", "gen-alice")
    code, resp = _http_post("/v1/result", {
        "assignment_id": gen_task["assignment_id"],
        "worker_id": "gen-alice",
        "attempt": _attempt_body(gen_task["candidate_id"]),
    })
    assert code == 200, f"gen submission failed: {code}: {resp}"
    gen_attempt_id = resp["attempt_id"]

    # Step 2: crit-bob takes a separate task.
    crit_task = _take_task("crit", "crit-bob")
    code, resp = _http_post("/v1/result", {
        "assignment_id": crit_task["assignment_id"],
        "worker_id": "crit-bob",
        "attempt": _attempt_body(
            crit_task["candidate_id"],
            verifier_status="PASS_SHAPE_ONLY",
            critic_status="pass",
            supersedes=gen_attempt_id,
            critic_report_path=rel_report,
        ),
    })
    assert code == 200, (
        f"crit-bob submission against gen-alice should succeed, "
        f"got {code}: {resp}")
    print("[test_role_gate] OK   gen-alice + crit-bob -> 200 (different workers)")


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="role_gate_e2e_") as tmp:
        tmp_path = Path(tmp)
        stub = _stage_stub_repo(tmp_path)
        proc = _start_coordinator(stub)
        try:
            run_test_gen_carrying_critic_pass_rejected()
            run_test_crit_carrying_not_run_rejected()
            run_test_gen_then_crit_same_worker_rejected()
            # v0.4.2 Track C3: dispatcher 503 BEFORE any verified gen
            # attempt is in the ledger, so this case must run before
            # the "different worker accepted" case below populates one.
            run_test_dispatcher_no_pending_returns_503()
            run_test_gen_then_crit_different_worker_accepted(stub)
            # v0.4.2 Track C3: dispatcher offers a pending gen attempt
            # to a critic with a different principal id.
            run_test_dispatcher_offers_pending_with_supersedes(stub)
            # v0.4.2 Track C3: principal-identity guard rejects same
            # principal even when prefix differs.
            run_test_principal_identity_rejects_same_principal(stub)
        finally:
            proc.send_signal(2)  # SIGINT
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
    print("[test_role_gate] OK (7 Rule-12 + dispatcher cases passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
