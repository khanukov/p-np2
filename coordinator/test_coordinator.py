#!/usr/bin/env python3
"""End-to-end coordinator test —
Research Governance v0.1, MVP-0.2 (Phase B).

Spawns the coordinator HTTP service against an isolated
sqlite state file and stub repo, then dispatches N parallel
"workers" against it via a synthetic in-process driver (NOT
the full scripts/run_worker.sh — that requires lake which
the test wants to avoid).

Asserts:

  1. /v1/health returns 200 with the expected shape.
  2. /v1/manifest returns the version_manifest.toml contents.
  3. N parallel /v1/task calls produce N distinct
     assignment_id / candidate_id pairs.
  4. /v1/task with a wrong-prefix worker_id (e.g. crit-X for
     role=gen) returns 403.
  5. /v1/task with role=gen but worker_id=crit-X returns 403
     (Generator/Critic role separation enforced at the
     protocol level).
  6. N parallel /v1/result calls each merge an attempt; the
     ledger ends with N distinct ATT-NNNNNN ids.
  7. /v1/result with a wrong worker_id for the assignment
     returns 403.
  8. /v1/result on an already-submitted assignment returns 409.
  9. /v1/release transitions an assigned lease to released
     and a subsequent /v1/result on the same assignment
     returns 409.
 10. /v1/dedup distinguishes seen vs unseen content_hash.

The test does NOT pollute the canonical outputs/ directory:
it points the coordinator at a stub repo where outputs/ is
empty, by way of running the coordinator with PYTHONPATH /
working directory tricks documented inline.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Avoid colliding with a real coordinator on 8765; pick something
# unlikely to be used and randomise.
import random
TEST_PORT = 18000 + random.randint(0, 1999)
COORDINATOR_URL = f"http://127.0.0.1:{TEST_PORT}"


def _stage_stub_repo(tmp: Path) -> Path:
    """Copy the minimum of the real repo into tmp so that the
    coordinator's subprocess pipes (attempts_append.py etc.) write
    to the stub's outputs/, NOT the real one.  Returns the stub
    repo root.
    """
    stub = tmp / "stub_repo"
    stub.mkdir(parents=True, exist_ok=True)
    for sub in ("scripts", "spec", "outputs", "seed_packs", "coordinator"):
        (stub / sub).mkdir(parents=True, exist_ok=True)
    # Copy writer + validator scripts.
    for name in (
        "attempts_append.py", "nogolog_append.py", "survivor_append.py",
        "validate_jsonl.py", "validate_critic_report.py",
    ):
        shutil.copy2(ROOT / "scripts" / name, stub / "scripts" / name)
    # Copy spec files (the validators need nogolog_schema.json and
    # the manifest endpoint reads version_manifest.toml).
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
    # Empty ledgers.
    for name in ("attempts.jsonl", "nogolog.jsonl", "survivor_history.jsonl"):
        (stub / "outputs" / name).write_text("")
    # One synthetic seed pack so /v1/task can succeed.
    # Stage TWO synthetic seed packs so the no-seed-pack
    # round-robin path (MVP-0.5.2 / PR 2) is exercised meaningfully.
    for sp_name in ("smoke_test_pack", "smoke_test_pack_b"):
        sp = stub / "seed_packs" / sp_name
        sp.mkdir(parents=True, exist_ok=True)
        (sp / "README.md").write_text(
            f"# Synthetic seed pack {sp_name} used only by coordinator e2e test.\n")
    # Copy coordinator package into stub (so subprocess scripts that
    # use Path(__file__).resolve().parent.parent resolve to the stub
    # root).
    for name in ("__init__.py", "schema.py", "store.py", "dedup.py",
                 "leases.py", "ledger.py", "role_gate.py", "wave_gate.py",
                 "metrics.py", "server.py",
                 # v0.4.2 Track C2 / C3 / C4.
                 "cost_budget.py", "critic_dispatcher.py",
                 "promotion_evaluator.py"):
        shutil.copy2(ROOT / "coordinator" / name,
                     stub / "coordinator" / name)
    # Phase E: thresholds file required by wave_gate.py.
    src_th = ROOT / "spec" / "wave_gate_thresholds.toml"
    if src_th.exists():
        shutil.copy2(src_th, stub / "spec" / "wave_gate_thresholds.toml")
    # v0.4.2 Track C2: cost_budget thresholds file.
    src_cb = ROOT / "spec" / "cost_budget_thresholds.toml"
    if src_cb.exists():
        shutil.copy2(src_cb, stub / "spec" / "cost_budget_thresholds.toml")
    # v0.4.2 Track B: initialise the stub as a git repo with a single
    # empty commit so the coordinator's `git rev-parse HEAD` returns a
    # real, deterministic-shaped 40-char hex.  The exact hash differs
    # per run (timestamp goes into the commit object), but the tests
    # that need it just read it from /v1/health.
    subprocess.run(["git", "-C", str(stub), "init", "-q"], check=True)
    subprocess.run(["git", "-C", str(stub), "config", "user.email",
                    "test@example.invalid"], check=True)
    subprocess.run(["git", "-C", str(stub), "config", "user.name",
                    "coord-test"], check=True)
    subprocess.run(["git", "-C", str(stub), "config", "commit.gpgsign",
                    "false"], check=True)
    subprocess.run(["git", "-C", str(stub), "commit", "--allow-empty",
                    "-m", "stub", "-q"], check=True,
                   env={**os.environ, "GIT_AUTHOR_DATE": "2026-05-05T12:00:00Z",
                        "GIT_COMMITTER_DATE": "2026-05-05T12:00:00Z"})
    return stub


def _start_coordinator(stub: Path) -> subprocess.Popen:
    """Start the coordinator as a subprocess so its working
    directory and `Path(__file__).resolve().parent.parent` resolve
    to the stub repo, isolating ledger writes."""
    env = os.environ.copy()
    env["PYTHONPATH"] = str(stub)
    # MVP-0.5 Phase E: the test exercises N=20 parallel tasks which
    # exceeds Wave-0's max_concurrent=10 cap.  Bump initial wave to
    # 2 (cap=500) so the e2e suite still passes; the wave-gate
    # behaviour itself is exercised by coordinator/test_wave_gate.py.
    env["AUTORESEARCH_INITIAL_WAVE"] = "2"
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
    # Spin until /v1/health succeeds (max 5s).
    for _ in range(50):
        try:
            with urllib.request.urlopen(
                    COORDINATOR_URL + "/v1/health", timeout=1) as r:
                if r.status == 200:
                    return proc
        except (urllib.error.URLError, ConnectionError):
            pass
        time.sleep(0.1)
    # Failed to come up; print stderr and raise.
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


# ---------------------------------------------------------------------------
# Test cases.
# ---------------------------------------------------------------------------


def run_test_health() -> None:
    code, body = _http_get("/v1/health")
    assert code == 200, f"health returned {code}: {body}"
    assert body["status"] == "ok", body
    assert "coordinator_version" in body, body
    assert "autoresearch_mvp_version" in body, body
    print("[test_coordinator] OK   /v1/health")


def run_test_manifest() -> None:
    # Manifest returns toml; we just check 200.
    req = urllib.request.Request(COORDINATOR_URL + "/v1/manifest")
    with urllib.request.urlopen(req, timeout=5) as r:
        assert r.status == 200
        text = r.read().decode("utf-8")
        assert "[snapshot]" in text, "manifest body missing [snapshot]"
    print("[test_coordinator] OK   /v1/manifest")


def run_test_task_role_mismatch() -> None:
    # Wrong-prefix worker_id MUST be rejected with 403.
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=crit-evil")
    assert code == 403, f"expected 403, got {code}: {body}"
    print("[test_coordinator] OK   /v1/task role-mismatch -> 403")


def run_test_n_parallel_tasks(n: int) -> list[dict]:
    """N parallel /v1/task; assert distinct assignment_id and
    candidate_id."""
    def fetch(i: int) -> dict:
        code, body = _http_get(
            f"/v1/task?role=gen&worker_id=gen-test-{i:03d}"
            f"&seed_pack=smoke_test_pack")
        assert code == 200, f"task {i} returned {code}: {body}"
        return body

    with ThreadPoolExecutor(max_workers=n) as ex:
        tasks = list(ex.map(fetch, range(n)))

    asn_ids = {t["assignment_id"] for t in tasks}
    cand_ids = {t["candidate_id"] for t in tasks}
    assert len(asn_ids) == n, f"distinct assignment_ids: {len(asn_ids)}/{n}"
    assert len(cand_ids) == n, f"distinct candidate_ids: {len(cand_ids)}/{n}"
    print(f"[test_coordinator] OK   /v1/task x N={n} -> {n} distinct ids")
    return tasks


def run_test_n_parallel_results(tasks: list[dict]) -> None:
    """N parallel /v1/result against the assignments produced
    above; assert distinct ATT-NNNNNN ids in the response."""
    n = len(tasks)

    def submit(t: dict) -> dict:
        body = {
            "assignment_id": t["assignment_id"],
            "worker_id": t["worker_id"],
            "attempt": {
                "candidate_id": t["candidate_id"],
                "method_family": "ac0_locality_support",
                "verifier_status": "PASS_SHAPE_ONLY",
                "critic_status": "not_run",
                "applicable_spec_version": "0.1.0",
                "attack_suite_version": "0.1.0",
            },
        }
        code, resp = _http_post("/v1/result", body)
        assert code == 200, f"result for {t['assignment_id']} returned {code}: {resp}"
        return resp

    with ThreadPoolExecutor(max_workers=n) as ex:
        results = list(ex.map(submit, tasks))

    att_ids = {r["attempt_id"] for r in results}
    assert len(att_ids) == n, f"distinct attempt_ids: {len(att_ids)}/{n}"
    print(f"[test_coordinator] OK   /v1/result x N={n} -> {n} distinct"
          f" ATT ids")


def run_test_wrong_worker_submission(stub: Path) -> None:
    """A worker submitting to an assignment leased by a DIFFERENT
    worker MUST be rejected with 403."""
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-victim&seed_pack=smoke_test_pack")
    assert code == 200
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-attacker",
        "attempt": {
            "candidate_id": task["candidate_id"],
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "not_run",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
        },
    }
    code, resp = _http_post("/v1/result", body)
    assert code == 403, f"expected 403, got {code}: {resp}"
    print("[test_coordinator] OK   /v1/result wrong-worker -> 403")


def run_test_double_submit_is_idempotent(stub: Path) -> None:
    """A second /v1/result on the same assignment by the same worker
    MUST return the previously-merged attempt_id (200 OK with
    idempotent_retry=true), NOT 409.  This is the MVP-0.5.1 PR-1
    contract: workers can safely retry under network errors.
    A different worker submitting the same assignment is still 403
    (covered by run_test_wrong_worker_submission).  Released /
    expired assignments are still 409 (covered by
    run_test_release_then_submit)."""
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-double&seed_pack=smoke_test_pack")
    assert code == 200
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-double",
        "attempt": {
            "candidate_id": task["candidate_id"],
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "not_run",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
        },
    }
    code1, resp1 = _http_post("/v1/result", body)
    assert code1 == 200, f"first submit failed: {code1}: {resp1}"
    first_attempt_id = resp1["attempt_id"]
    code2, resp2 = _http_post("/v1/result", body)
    assert code2 == 200, (
        f"second submit (idempotent retry) should be 200, got {code2}: {resp2}")
    assert resp2.get("attempt_id") == first_attempt_id, (
        f"idempotent retry must return the same attempt_id; "
        f"first={first_attempt_id} second={resp2.get('attempt_id')}")
    assert resp2.get("idempotent_retry") is True, (
        f"idempotent retry response must carry idempotent_retry=true: {resp2}")
    print("[test_coordinator] OK   /v1/result double-submit -> 200 (idempotent)")


def run_test_no_seed_pack_round_robin() -> None:
    """MVP-0.5.2 / PR 2: parallel /v1/task without seed_pack
    parameter must produce N distinct assignment ids AND must
    distribute across the available seed packs (round-robin)."""
    from concurrent.futures import ThreadPoolExecutor
    n = 8

    def fetch(i: int) -> dict:
        code, body = _http_get(
            f"/v1/task?role=gen&worker_id=gen-rr-{i:02d}")
        assert code == 200, f"task {i} returned {code}: {body}"
        return body

    with ThreadPoolExecutor(max_workers=n) as ex:
        tasks = list(ex.map(fetch, range(n)))
    asn_ids = {t["assignment_id"] for t in tasks}
    seed_pack_ids = {t["seed_pack_id"] for t in tasks}
    assert len(asn_ids) == n, (
        f"distinct assignment ids: {len(asn_ids)}/{n}")
    assert len(seed_pack_ids) >= 2, (
        f"round-robin should hit >=2 distinct seed packs; "
        f"got {seed_pack_ids}")
    print(f"[test_coordinator] OK   /v1/task no-seed-pack RR -> "
          f"{len(asn_ids)} distinct asn, {len(seed_pack_ids)} distinct seeds")


def run_test_prevalidation_rejects_bad_nogolog(stub: Path) -> None:
    """MVP-0.5.1 / PR 1: a /v1/result whose `nogolog_entry` is
    malformed MUST be rejected with 400 BEFORE the main attempt
    is appended to the canonical ledger.  This proves the
    pre-validation gate works: we don't end up with the attempt
    persisted but the auxiliary entry rejected."""
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-prev&seed_pack=smoke_test_pack")
    assert code == 200
    # Read the canonical ledger length before the doomed submit.
    ledger = stub / "outputs" / "attempts.jsonl"
    before = len([_ for _ in ledger.read_text().splitlines() if _.strip()])
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-prev",
        "attempt": {
            "candidate_id": task["candidate_id"],
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "not_run",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
        },
        "nogolog_entry": {
            # Deliberately malformed: missing required fields.
            "candidate_id": "synthetic_prev",
            # missing method_family, status, failure_class, ...
        },
    }
    code, resp = _http_post("/v1/result", body)
    assert code == 400, (
        f"prevalidation should reject bad nogolog with 400, "
        f"got {code}: {resp}")
    assert "nogolog prevalidation failed" in resp.get("error", ""), resp
    # Ledger MUST NOT have grown.
    after = len([_ for _ in ledger.read_text().splitlines() if _.strip()])
    assert after == before, (
        f"ledger grew during failed prevalidation: {before} -> {after}")
    print("[test_coordinator] OK   /v1/result bad nogolog -> 400 + no ledger drift")


def run_test_release_then_submit() -> None:
    """A released lease MUST refuse a subsequent /v1/result with 409."""
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-cancel&seed_pack=smoke_test_pack")
    assert code == 200
    rcode, _ = _http_post("/v1/release", {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-cancel",
    })
    assert rcode == 200
    code2, resp = _http_post("/v1/result", {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-cancel",
        "attempt": {
            "candidate_id": task["candidate_id"],
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "not_run",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
        },
    })
    assert code2 == 409, f"expected 409 after release, got {code2}: {resp}"
    print("[test_coordinator] OK   /v1/release then /v1/result -> 409")


def run_test_dedup_register_then_lookup() -> None:
    """MVP-0.5.4 / PR 4: register a content_hash, then look it up.

    Sequence:
        1. lease an assignment (need a real assignment_id to bind
           the dedup row to);
        2. POST /v1/dedup/register {content_hash, assignment_id};
           expect 200 with seen=False and first_assignment_id == ours;
        3. POST /v1/dedup/register again with the same hash but a
           different assignment_id; expect 409 with
           first_assignment_id pointing at the original;
        4. GET /v1/dedup?content_hash=... ; expect 409 with the
           same first_assignment_id.

    Together (with run_test_release_then_submit's lease release
    keeping the test isolated from the wave-cap test) this proves
    the dedup table actually persists.
    """
    # Lease an assignment first.
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-dedup-1"
        "&seed_pack=smoke_test_pack")
    assert code == 200, f"task lease failed: {code}: {task}"
    asn_a = task["assignment_id"]
    h = "1" * 64

    # Step 1: register.
    code, body = _http_post("/v1/dedup/register", {
        "content_hash": h,
        "assignment_id": asn_a,
    })
    assert code == 200, f"first register should 200, got {code}: {body}"
    assert body["seen"] is False, body
    assert body["first_assignment_id"] == asn_a, body

    # Step 2: register again under a different assignment.
    code, task_b = _http_get(
        "/v1/task?role=gen&worker_id=gen-dedup-2"
        "&seed_pack=smoke_test_pack")
    assert code == 200
    asn_b = task_b["assignment_id"]
    code, body = _http_post("/v1/dedup/register", {
        "content_hash": h,
        "assignment_id": asn_b,
    })
    assert code == 409, f"second register should 409, got {code}: {body}"
    assert body["seen"] is True, body
    assert body["first_assignment_id"] == asn_a, body

    # Step 3: GET lookup confirms.
    code, body = _http_get(f"/v1/dedup?content_hash={h}")
    assert code == 409, f"GET lookup of seen hash should 409, got {code}: {body}"
    assert body["first_assignment_id"] == asn_a, body
    print("[test_coordinator] OK   /v1/dedup register-then-lookup -> "
          "200 (newly), 409 (seen), 409 (lookup)")

    # Release the leases so they don't pollute later tests.
    for asn, wid in ((asn_a, "gen-dedup-1"), (asn_b, "gen-dedup-2")):
        _http_post("/v1/release", {"assignment_id": asn, "worker_id": wid})


def run_test_dedup() -> None:
    """Unseen content_hash returns 200; seen returns 409."""
    code, body = _http_get("/v1/dedup?content_hash=" + "0" * 64)
    assert code == 200, f"unseen hash should 200, got {code}: {body}"
    assert body["seen"] is False
    print("[test_coordinator] OK   /v1/dedup unseen -> 200")


def run_test_health_carries_commit() -> str:
    """v0.4.2 Track B: /v1/health exposes coordinator_git_commit
    (40-char hex) and coordinator_git_ref.  Returns the commit so
    later tests can use it."""
    code, body = _http_get("/v1/health")
    assert code == 200, body
    commit = body.get("coordinator_git_commit", "")
    ref = body.get("coordinator_git_ref", "")
    assert isinstance(commit, str), body
    assert len(commit) == 40, f"expected 40-char commit, got {commit!r}"
    assert all(c in "0123456789abcdef" for c in commit), commit
    assert isinstance(ref, str) and ref, body
    print("[test_coordinator] OK   /v1/health carries 40-hex coordinator_git_commit")
    return commit


def run_test_task_carries_commit(coord_commit: str) -> None:
    """v0.4.2 Track B: /v1/task response includes git_commit + git_ref."""
    code, body = _http_get(
        "/v1/task?role=gen&worker_id=gen-pinning&seed_pack=smoke_test_pack")
    assert code == 200, body
    assert body.get("git_commit") == coord_commit, body
    assert isinstance(body.get("git_ref"), str) and body["git_ref"], body
    # Release immediately so we don't pollute subsequent tests.
    _http_post("/v1/release", {
        "assignment_id": body["assignment_id"],
        "worker_id": "gen-pinning",
    })
    print("[test_coordinator] OK   /v1/task carries git_commit + git_ref")


def run_test_result_commit_mismatch_rejected(coord_commit: str) -> None:
    """v0.4.2 Track B: a /v1/result whose attempt.git_commit does
    not match the coordinator's HEAD MUST be rejected with 403 and
    the error message MUST mention 'commit_mismatch'."""
    code, task = _http_get(
        "/v1/task?role=gen&worker_id=gen-mismatch&seed_pack=smoke_test_pack")
    assert code == 200, task
    bogus = "0" * 40  # certainly not the stub's HEAD
    assert bogus != coord_commit
    body = {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-mismatch",
        "attempt": {
            "candidate_id": task["candidate_id"],
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": "not_run",
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
            "git_commit": bogus,
        },
    }
    code2, resp = _http_post("/v1/result", body)
    assert code2 == 403, f"expected 403, got {code2}: {resp}"
    err_text = json.dumps(resp).lower()
    assert "commit_mismatch" in err_text, resp
    # Release the assignment so the wave-cap stays clean.
    _http_post("/v1/release", {
        "assignment_id": task["assignment_id"],
        "worker_id": "gen-mismatch",
    })
    print("[test_coordinator] OK   /v1/result commit-mismatch -> 403 commit_mismatch")


def run_test_ledger_persisted(stub: Path, expected_min: int) -> None:
    """Ledger file should contain at least expected_min lines."""
    ledger = stub / "outputs" / "attempts.jsonl"
    n = sum(1 for _ in ledger.read_text().splitlines() if _.strip())
    assert n >= expected_min, f"ledger has {n} lines, expected >= {expected_min}"
    print(f"[test_coordinator] OK   ledger has {n} attempts persisted")


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="coord_e2e_") as tmp:
        tmp_path = Path(tmp)
        stub = _stage_stub_repo(tmp_path)
        proc = _start_coordinator(stub)
        try:
            run_test_health()
            run_test_manifest()
            run_test_task_role_mismatch()
            tasks = run_test_n_parallel_tasks(n=20)
            run_test_n_parallel_results(tasks)
            run_test_wrong_worker_submission(stub)
            run_test_double_submit_is_idempotent(stub)
            run_test_no_seed_pack_round_robin()
            run_test_prevalidation_rejects_bad_nogolog(stub)
            run_test_release_then_submit()
            # v0.4.2 Track B commit-pinning trio.
            coord_commit = run_test_health_carries_commit()
            run_test_task_carries_commit(coord_commit)
            run_test_result_commit_mismatch_rejected(coord_commit)
            run_test_dedup()
            run_test_dedup_register_then_lookup()
            # 20 tasks submitted + 1 double-submit (counts once) +
            # 1 wrong-worker (rejected, no merge) = 21 entries.
            run_test_ledger_persisted(stub, expected_min=20)
        finally:
            proc.send_signal(2)  # SIGINT
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()

    print("[test_coordinator] OK (all e2e cases passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
