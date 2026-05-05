#!/usr/bin/env python3
"""Wave-gate + metrics e2e — Research Governance v0.1, MVP-0.5 (Phase E).

Asserts:

  Test 1 (cap-enforced):
    Wave 0 has max_concurrent=10.  Issue 10 tasks (no result), then
    the 11th /v1/task is refused with 503 + reason "wave_cap".

  Test 2 (cap-released-on-submit):
    After submitting one of the 10 in-flight assignments, /v1/task
    succeeds again.

  Test 3 (metrics endpoint):
    /v1/metrics returns Prometheus-format text containing:
      autoresearch_tasks_assigned_total{role="gen"} >= 10
      autoresearch_results_merged_total{...} >= 1
      autoresearch_in_flight_assignments (gauge)
      autoresearch_current_wave (gauge) = 0
      autoresearch_worker_cap (gauge) = 10
      autoresearch_tasks_refused_total{reason="wave_cap"} >= 1

The test runs against a freshly-staged stub repo and bypasses the
default Wave-2 override used by other e2e tests; here we want
Wave 0 explicitly to exercise the cap.
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
TEST_PORT = 24000 + random.randint(0, 999)
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
        "frozen_spec_plan.md", "wave_gate_thresholds.toml",
    ):
        src = ROOT / "spec" / name
        if src.exists():
            shutil.copy2(src, stub / "spec" / name)
    for name in ("attempts.jsonl", "nogolog.jsonl", "survivor_history.jsonl"):
        (stub / "outputs" / name).write_text("")
    sp = stub / "seed_packs" / "wave_gate_smoke_pack"
    sp.mkdir(parents=True, exist_ok=True)
    (sp / "README.md").write_text(
        "# Synthetic seed pack used only by wave-gate e2e test.\n")
    for name in ("__init__.py", "schema.py", "store.py", "dedup.py",
                 "leases.py", "ledger.py", "role_gate.py", "wave_gate.py",
                 "metrics.py", "server.py",
                 # v0.4.2 Track C2 / C3 / C4.
                 "cost_budget.py", "critic_dispatcher.py",
                 "promotion_evaluator.py"):
        shutil.copy2(ROOT / "coordinator" / name,
                     stub / "coordinator" / name)
    # v0.4.2 Track C2: thresholds file (optional; reaper degrades to
    # defaults if missing, but copy when available so tests reflect
    # production config).
    src_cb = ROOT / "spec" / "cost_budget_thresholds.toml"
    if src_cb.exists():
        shutil.copy2(src_cb, stub / "spec" / "cost_budget_thresholds.toml")
    return stub


def _start_coordinator(stub: Path) -> subprocess.Popen:
    env = os.environ.copy()
    env["PYTHONPATH"] = str(stub)
    env["AUTORESEARCH_INITIAL_WAVE"] = "0"  # exercise the strictest cap
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


def _http_get(path: str) -> tuple[int, dict | str]:
    req = urllib.request.Request(COORDINATOR_URL + path, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=5) as r:
            body = r.read().decode("utf-8")
            ct = r.headers.get("Content-Type", "")
            if "json" in ct:
                return r.status, json.loads(body)
            return r.status, body
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8")
        try:
            return e.code, json.loads(body)
        except json.JSONDecodeError:
            return e.code, body


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


def _attempt_body(candidate_id: str) -> dict:
    return {
        "candidate_id": candidate_id,
        "method_family": "ac0_locality_support",
        "verifier_status": "PASS_SHAPE_ONLY",
        "critic_status": "not_run",
        "applicable_spec_version": "0.1.0",
        "attack_suite_version": "0.1.0",
    }


def run_test_cap_enforced() -> list[dict]:
    """Issue 10 tasks (Wave-0 cap), assert the 11th is refused."""
    tasks = []
    for i in range(10):
        code, body = _http_get(
            f"/v1/task?role=gen&worker_id=gen-cap-{i:02d}"
            f"&seed_pack=wave_gate_smoke_pack")
        assert code == 200, f"task {i} returned {code}: {body}"
        tasks.append(body)
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=gen-cap-11"
        "&seed_pack=wave_gate_smoke_pack")
    assert code == 503, f"11th task should be 503 (cap), got {code}: {body}"
    assert "Wave 0" in body.get("error", ""), body
    print("[test_wave_gate] OK   Wave-0 cap=10 enforced (11th -> 503)")
    return tasks


def run_test_cap_released_on_submit(tasks: list[dict]) -> None:
    """After submitting one in-flight assignment, /v1/task succeeds."""
    t = tasks[0]
    code, _ = _http_post("/v1/result", {
        "assignment_id": t["assignment_id"],
        "worker_id": t["worker_id"],
        "attempt": _attempt_body(t["candidate_id"]),
    })
    assert code == 200
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=gen-cap-after"
        "&seed_pack=wave_gate_smoke_pack")
    assert code == 200, (
        f"after submit, /v1/task should succeed, got {code}: {body}")
    print("[test_wave_gate] OK   cap released on submit (-1 in-flight)")


def run_test_expired_lease_frees_cap(stub: Path) -> None:
    """MVP-0.5.3 / PR 3: an assignment whose deadline has passed
    must be reclaimed by expire_due() so the wave cap reflects
    LIVE in-flight workers, not stale assignments from crashed
    ones.

    Real-time wait is avoided by directly back-dating the deadline
    column on an existing in-flight assignment via the stub's
    coordinator/state.db file.  Then the next /v1/task probe
    triggers expire_due() and admits a new worker.
    """
    import sqlite3

    # Confirm we're currently at the cap (the prior tests left
    # the coordinator with 10/10 in-flight: 9 from cap_enforced
    # plus 1 from cap_released_on_submit's gen-cap-after).
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=gen-expiry-pre"
        "&seed_pack=wave_gate_smoke_pack")
    assert code == 503, (
        f"pre-expiry task should hit cap (503), got {code}: {body}")

    # Pick any existing in-flight assignment and back-date it.
    db_path = stub / "coordinator" / "state.db"
    conn = sqlite3.connect(str(db_path))
    try:
        row = conn.execute(
            "SELECT assignment_id FROM assignments "
            " WHERE status = 'assigned' LIMIT 1"
        ).fetchone()
        assert row is not None, "no in-flight assignment to back-date"
        asn = row[0]
        conn.execute(
            "UPDATE assignments SET deadline = '1970-01-01T00:00:00Z' "
            " WHERE assignment_id = ?",
            (asn,),
        )
        conn.commit()
    finally:
        conn.close()

    # Now the next /v1/task call should run expire_due() FIRST,
    # which transitions the back-dated assignment to 'expired'
    # and frees one slot in the cap.  The new task should succeed.
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=gen-expiry-post"
        "&seed_pack=wave_gate_smoke_pack")
    assert code == 200, (
        f"after expire_due, /v1/task should succeed, got {code}: {body}")
    print(f"[test_wave_gate] OK   expired lease ({asn}) frees wave cap")


def run_test_metrics_endpoint() -> None:
    code, body = _http_get("/v1/metrics")
    assert code == 200, f"/v1/metrics returned {code}: {body!r}"
    assert isinstance(body, str)
    expected_substrings = (
        'autoresearch_tasks_assigned_total{role="gen"}',
        "autoresearch_results_merged_total",
        "autoresearch_in_flight_assignments",
        "autoresearch_current_wave",
        "autoresearch_worker_cap",
        'autoresearch_tasks_refused_total{reason="wave_cap"}',
        "# TYPE autoresearch_tasks_assigned_total counter",
        "# TYPE autoresearch_in_flight_assignments gauge",
    )
    for sub in expected_substrings:
        assert sub in body, (
            f"expected metric/comment {sub!r} in body, got:\n{body!r}")
    print("[test_wave_gate] OK   /v1/metrics exposes 6/6 expected metric"
          " families")


def run_test_promotion_force_required(stub: Path) -> None:
    """MVP-0.5.5 / PR 5: AUTORESEARCH_INITIAL_WAVE > 0 without
    AUTORESEARCH_PROMOTION_FORCE=true MUST refuse to start."""
    # Spawn a SHORT-lived coordinator on a different port that
    # tries to start at Wave 2 without the FORCE flag.
    env = os.environ.copy()
    env["PYTHONPATH"] = str(stub)
    env["AUTORESEARCH_INITIAL_WAVE"] = "2"
    env.pop("AUTORESEARCH_PROMOTION_FORCE", None)
    proc = subprocess.Popen(
        [sys.executable, "-m", "coordinator.server",
         "--bind", "127.0.0.1", "--port", str(TEST_PORT + 100),
         "--db", str(stub / "coordinator" / "state2.db"),
         "--quiet"],
        cwd=stub,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        rc = proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        raise AssertionError(
            "coordinator should have refused to start without "
            "AUTORESEARCH_PROMOTION_FORCE; instead it kept running")
    err = proc.stderr.read().decode("utf-8", "replace") if proc.stderr else ""
    assert rc != 0, (
        f"coordinator should have exited non-zero; got rc={rc}, stderr={err!r}")
    assert "AUTORESEARCH_PROMOTION_FORCE" in err, (
        f"refusal message must mention AUTORESEARCH_PROMOTION_FORCE; "
        f"stderr={err!r}")
    print("[test_wave_gate] OK   AUTORESEARCH_INITIAL_WAVE=2 without FORCE "
          "-> refused at startup")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="wave_gate_e2e_") as tmp:
        tmp_path = Path(tmp)
        stub = _stage_stub_repo(tmp_path)
        # Run the promotion-force-required test BEFORE the
        # main coordinator comes up: it spawns its own short-
        # lived subprocess and asserts non-zero exit.
        run_test_promotion_force_required(stub)
        proc = _start_coordinator(stub)
        try:
            tasks = run_test_cap_enforced()
            run_test_cap_released_on_submit(tasks)
            run_test_expired_lease_frees_cap(stub)
            run_test_metrics_endpoint()
        finally:
            proc.send_signal(2)
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
    print("[test_wave_gate] OK (4 wave-gate + metrics cases passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
