#!/usr/bin/env python3
"""Coordinator HTTP server — Research Governance v0.1, MVP-0.2.

Stdlib-only `http.server.ThreadingHTTPServer`.  Endpoints:

    GET  /v1/health
    GET  /v1/manifest
    GET  /v1/task?role=gen|crit&worker_id=…&seed_pack=…&lease_seconds=…
    GET  /v1/dedup?content_hash=…
    POST /v1/result   (JSON body = ResultSubmission)
    POST /v1/release  (JSON body = {assignment_id, worker_id})

Phase B scope:
    * one process, one host, sqlite state (coordinator/state.db)
    * no JWT auth, no quota, no metrics endpoint
    * Generator / Critic role separation enforced at protocol level
      via worker_id prefix (gen-/crit-/rev-)

Run:
    python3 -m coordinator.server --bind 127.0.0.1 --port 8765

Stop with SIGINT; the EXIT path closes the sqlite connection.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import threading
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from uuid import uuid4

from . import __version__
from .dedup import hash_gen_candidate, hash_critic_report
from .leases import clamp_lease_seconds
from .ledger import (
    LedgerWriteError, append_attempt, append_nogolog, append_survivor,
)
from .metrics import Metrics
from .role_gate import enforce_commit_match, enforce_role_for_submission
from .schema import (
    DedupResponse, HealthStatus, ResultSubmission, TaskAssignment,
    principal_id_from_worker_id,
    validate_assignment_id, validate_role, validate_worker_id, write_json,
)
from .store import CoordinatorStore
from .wave_gate import WaveGate

ROOT = Path(__file__).resolve().parent.parent
SEED_PACKS_DIR = ROOT / "seed_packs"

# Phase B reads autoresearch_mvp version from the manifest at startup
# so /v1/health can report it without a recursive import.
def _read_autoresearch_mvp_version() -> str:
    try:
        import tomllib  # type: ignore[import]
    except ModuleNotFoundError:
        return "unknown"
    try:
        manifest_path = ROOT / "spec" / "version_manifest.toml"
        with manifest_path.open("rb") as f:
            data = tomllib.load(f)
    except Exception:
        return "unknown"
    snapshot = data.get("snapshot", {})
    ar = snapshot.get("autoresearch_mvp", {})
    return ar.get("version", "unknown") if isinstance(ar, dict) else "unknown"


# v0.4.2 Track B: commit pinning.  Read HEAD at startup so the
# coordinator can stamp every TaskAssignment with the commit it was
# launched on; workers refuse to run when their local HEAD differs.
def _read_git_commit() -> str:
    """Resolve full 40-char hex of HEAD or empty string on failure."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=5, check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if proc.returncode != 0:
        return ""
    out = proc.stdout.strip()
    if len(out) != 40 or any(c not in "0123456789abcdef" for c in out):
        return ""
    return out


def _read_git_ref() -> str:
    """Symbolic ref for HEAD (short branch name) or 'detached'."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "symbolic-ref", "--short", "-q", "HEAD"],
            capture_output=True, text=True, timeout=5, check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return "detached"
    if proc.returncode != 0:
        return "detached"
    out = proc.stdout.strip()
    return out or "detached"


def _scan_seed_packs() -> list[str]:
    """Return seed pack ids — every direct subdirectory of seed_packs/
    that contains a README.md, excluding `INFRA/` (those are infra
    briefs, not research seeds) and dotfiles."""
    if not SEED_PACKS_DIR.exists():
        return []
    out = []
    for child in sorted(SEED_PACKS_DIR.iterdir()):
        if not child.is_dir():
            continue
        if child.name.startswith("."):
            continue
        if child.name == "INFRA":
            continue
        if (child / "README.md").exists():
            out.append(child.name)
    return out


# ---------------------------------------------------------------------------
# Request handler.
# ---------------------------------------------------------------------------


class CoordinatorHandler(BaseHTTPRequestHandler):
    server_version = f"AutoresearchCoordinator/{__version__}"
    # Per-server shared state, attached by `serve()` below.
    coordinator_store: CoordinatorStore = None  # type: ignore[assignment]
    autoresearch_mvp_version: str = "unknown"
    wave_gate: WaveGate = None  # type: ignore[assignment]
    metrics: Metrics = None  # type: ignore[assignment]
    log_to_stderr: bool = True
    # v0.4.2 Track B: cached at server start; injected into TaskAssignment
    # and HealthStatus so workers can pre-check + stamp git_commit.
    coordinator_git_commit: str = ""
    coordinator_git_ref: str = "detached"

    # ------------------------------------------------------------------
    # Logging — quieter than the default, every request is one line.
    # ------------------------------------------------------------------

    def log_message(self, fmt: str, *args) -> None:  # type: ignore[override]
        if self.log_to_stderr:
            sys.stderr.write(
                "[coordinator] %s %s\n" % (self.address_string(), fmt % args))

    # ------------------------------------------------------------------
    # Top-level dispatch.
    # ------------------------------------------------------------------

    def do_GET(self) -> None:  # noqa: N802
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        try:
            if path == "/v1/health":
                self._handle_health()
            elif path == "/v1/manifest":
                self._handle_manifest()
            elif path == "/v1/task":
                self._handle_task(parsed)
            elif path == "/v1/dedup":
                self._handle_dedup(parsed)
            elif path == "/v1/metrics":
                self._handle_metrics()
            else:
                self._send_error(404, f"unknown path: {path!r}")
        except Exception as e:  # pragma: no cover
            self._send_error(500, f"internal error: {type(e).__name__}: {e}")

    def do_POST(self) -> None:  # noqa: N802
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        try:
            length = int(self.headers.get("Content-Length") or "0")
            body = self.rfile.read(length) if length else b""
            try:
                payload = json.loads(body) if body else {}
            except json.JSONDecodeError as e:
                self._send_error(400, f"body is not JSON: {e}")
                return
            if not isinstance(payload, dict):
                self._send_error(400, "body must be a JSON object")
                return
            if path == "/v1/result":
                self._handle_result(payload)
            elif path == "/v1/release":
                self._handle_release(payload)
            elif path == "/v1/dedup/register":
                self._handle_dedup_register(payload)
            else:
                self._send_error(404, f"unknown path: {path!r}")
        except Exception as e:  # pragma: no cover
            self._send_error(500, f"internal error: {type(e).__name__}: {e}")

    # ------------------------------------------------------------------
    # Endpoint handlers.
    # ------------------------------------------------------------------

    def _handle_health(self) -> None:
        # MVP-0.5.3 / PR 3: reclaim expired leases before counting
        # in-flight, so /v1/health reports the live (post-expiry)
        # state and so /v1/task's wave-cap check (which reads
        # counts_by_status) sees the freed capacity.
        self.coordinator_store.expire_due()
        counts = self.coordinator_store.counts_by_status()
        in_flight = int(counts.get("assigned", 0))
        # MVP-0.5 Phase E: surface gauges so /v1/metrics is fresh.
        if self.metrics is not None:
            self.metrics.set_gauge(
                "autoresearch_in_flight_assignments", in_flight)
            if self.wave_gate is not None:
                self.metrics.set_gauge(
                    "autoresearch_current_wave",
                    self.wave_gate.current_wave)
                self.metrics.set_gauge(
                    "autoresearch_worker_cap",
                    self.wave_gate.max_concurrent())
        current_wave = (self.wave_gate.current_wave
                        if self.wave_gate is not None else 0)
        status = HealthStatus(
            status="ok",
            coordinator_version=__version__,
            autoresearch_mvp_version=self.autoresearch_mvp_version,
            current_wave=current_wave,
            assigned_count=in_flight,
            completed_count=int(counts.get("submitted", 0)),
            abandoned_count=int(counts.get("expired", 0))
                            + int(counts.get("released", 0)),
            coordinator_git_commit=self.coordinator_git_commit,
            coordinator_git_ref=self.coordinator_git_ref,
        )
        self._send_json(200, status.to_json())

    def _handle_metrics(self) -> None:
        # Refresh gauges first so the scrape is point-in-time.
        self.coordinator_store.expire_due()  # PR 3
        counts = self.coordinator_store.counts_by_status()
        in_flight = int(counts.get("assigned", 0))
        if self.metrics is not None:
            self.metrics.set_gauge(
                "autoresearch_in_flight_assignments", in_flight)
            if self.wave_gate is not None:
                self.metrics.set_gauge(
                    "autoresearch_current_wave",
                    self.wave_gate.current_wave)
                self.metrics.set_gauge(
                    "autoresearch_worker_cap",
                    self.wave_gate.max_concurrent())
            body = self.metrics.render_prometheus()
        else:
            body = b"# coordinator/metrics.py not initialised\n"
        self.send_response(200)
        self.send_header("Content-Type",
                         "text/plain; version=0.0.4; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_manifest(self) -> None:
        manifest_path = ROOT / "spec" / "version_manifest.toml"
        if not manifest_path.exists():
            self._send_error(500, "spec/version_manifest.toml is missing")
            return
        body = manifest_path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", "application/toml; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_task(self, parsed: urllib.parse.ParseResult) -> None:
        params = urllib.parse.parse_qs(parsed.query)
        role = (params.get("role") or [""])[0]
        worker_id = (params.get("worker_id") or [""])[0]
        seed_pack_param = (params.get("seed_pack") or [""])[0]
        lease_param = (params.get("lease_seconds") or [None])[0]

        err = validate_role(role) or validate_worker_id(worker_id)
        if err:
            self._send_error(400, err)
            return
        # Generator / Critic role separation is enforced via worker_id
        # prefix; mismatch is a 403 (forbidden) rather than a 400.
        if not worker_id.startswith(role + "-"):
            self._send_error(
                403,
                f"worker_id {worker_id!r} does not match role {role!r}; "
                f"use prefix {role}-",
            )
            return
        seed_packs = _scan_seed_packs()
        if not seed_packs:
            self._send_error(503, "no seed packs available")
            return

        # v0.4.2 Track C3: critic auto-dispatcher.  When a critic
        # asks for work without specifying a seed_pack, the
        # coordinator picks an oldest verified gen attempt that
        # this critic's principal is allowed to critique and
        # stamps `supersedes` on the assignment.  When a seed_pack
        # IS specified, fall through to the legacy round-robin
        # path so ad-hoc re-critique against a specific pack still
        # works.
        crit_dispatch_payload: dict | None = None
        if role == "crit" and not seed_pack_param:
            from .critic_dispatcher import (
                NoPendingCriticAttempt, dispatch_critic_task,
            )
            try:
                crit_dispatch_payload = dispatch_critic_task(
                    store=self.coordinator_store,
                    crit_worker_id=worker_id,
                    attempts_jsonl_path=ROOT / "outputs" / "attempts.jsonl",
                )
            except NoPendingCriticAttempt as exc:
                if self.metrics is not None:
                    self.metrics.inc(
                        "autoresearch_tasks_refused_total",
                        {"reason": "no_pending_critic"})
                self._send_error(503, f"no_pending_critic: {exc}")
                return

        if seed_pack_param:
            if seed_pack_param not in seed_packs:
                self._send_error(
                    404, f"unknown seed_pack: {seed_pack_param!r}")
                return
            seed_pack_id = seed_pack_param
        elif crit_dispatch_payload is not None:
            sp = crit_dispatch_payload["seed_pack_id"]
            if sp and sp in seed_packs:
                seed_pack_id = sp
            else:
                # Gen attempt's seed_pack_id is unknown to us (e.g.
                # the seed pack was renamed or removed).  Fall back
                # to the first available seed pack — the critic
                # task is still well-defined because supersedes
                # carries the gen ATT id.
                seed_pack_id = seed_packs[0]
        else:
            # MVP-0.5.2 / PR 2: dedicated round-robin counter; no
            # rollback of the assignment_seq counter.  The previous
            # implementation peeked at next_assignment_seq() and
            # then UPDATE'd the value back, which under concurrent
            # /v1/task could lose assignment ids or duplicate them.
            rr = self.coordinator_store.next_seed_pack_rr()
            seed_pack_id = seed_packs[(rr - 1) % len(seed_packs)]

        try:
            lease_seconds = clamp_lease_seconds(
                int(lease_param) if lease_param is not None else None
            )
        except (ValueError, TypeError):
            self._send_error(400, f"invalid lease_seconds: {lease_param!r}")
            return

        # MVP-0.5 Phase E — wave-gate worker-cap enforcement.
        if self.wave_gate is not None:
            # MVP-0.5.3 / PR 3: reclaim expired leases first so the
            # cap reflects the live in-flight count, not stale
            # assignments from crashed workers.
            self.coordinator_store.expire_due()
            counts = self.coordinator_store.counts_by_status()
            in_flight = int(counts.get("assigned", 0))
            ok, msg = self.wave_gate.can_assign(in_flight)
            if not ok:
                if self.metrics is not None:
                    self.metrics.inc("autoresearch_tasks_refused_total",
                                     {"reason": "wave_cap"})
                self._send_error(503, msg or "wave cap reached")
                return

        assignment_id = self.coordinator_store.next_assignment_id()
        if crit_dispatch_payload is not None and \
                crit_dispatch_payload.get("candidate_id"):
            # v0.4.2 Track C3: dispatcher routes the critic at the
            # exact candidate_id of the gen attempt under critique.
            candidate_id = crit_dispatch_payload["candidate_id"]
        else:
            candidate_id = f"{seed_pack_id}_{uuid4().hex[:12]}"
        supersedes_for_assignment = (
            crit_dispatch_payload["supersedes"]
            if crit_dispatch_payload is not None else "")
        record = self.coordinator_store.create_assignment(
            assignment_id=assignment_id,
            candidate_id=candidate_id,
            seed_pack_id=seed_pack_id,
            role=role,
            worker_id=worker_id,
            lease_seconds=lease_seconds,
        )
        assignment = TaskAssignment(
            assignment_id=record["assignment_id"],
            candidate_id=record["candidate_id"],
            seed_pack_id=record["seed_pack_id"],
            role=record["role"],
            worker_id=record["worker_id"],
            lease_seconds=lease_seconds,
            deadline=record["deadline"],
            git_commit=self.coordinator_git_commit,
            git_ref=self.coordinator_git_ref,
            lease_id=record.get("lease_id", ""),
            supersedes=supersedes_for_assignment,
        )
        if self.metrics is not None:
            self.metrics.inc("autoresearch_tasks_assigned_total",
                             {"role": role})
        self._send_json(200, assignment.to_json())

    def _handle_dedup(self, parsed: urllib.parse.ParseResult) -> None:
        params = urllib.parse.parse_qs(parsed.query)
        content_hash = (params.get("content_hash") or [""])[0]
        if not content_hash or not all(
                c in "0123456789abcdef" for c in content_hash):
            self._send_error(
                400, f"content_hash must be lowercase hex: {content_hash!r}")
            return
        first = self.coordinator_store.lookup_dedup(content_hash)
        resp = DedupResponse(
            content_hash=content_hash,
            seen=first is not None,
            first_assignment_id=first,
        )
        self._send_json(200 if first is None else 409, resp.to_json())

    def _handle_result(self, payload: dict) -> None:
        try:
            sub = ResultSubmission.from_json(payload)
        except KeyError as e:
            self._send_error(400, f"missing field {e!s}")
            return
        err = (validate_assignment_id(sub.assignment_id)
               or validate_worker_id(sub.worker_id))
        if err:
            self._send_error(400, err)
            return
        rec = self.coordinator_store.get_assignment(sub.assignment_id)
        if rec is None:
            self._send_error(
                404, f"unknown assignment_id: {sub.assignment_id!r}")
            return
        if rec["worker_id"] != sub.worker_id:
            self._send_error(
                403,
                f"assignment {sub.assignment_id} was leased to "
                f"{rec['worker_id']!r}, not {sub.worker_id!r}",
            )
            return

        # MVP-0.5.1 / PR 1: idempotent retry.
        # If the assignment is already in `submitted` state and the
        # caller is the same worker that originally submitted it,
        # return the previously-merged attempt_id (200 OK) rather
        # than 409.  This makes /v1/result safe to retry under
        # network errors / lease-deadline-near-expiry.  Wrong-worker
        # / released / expired assignments still 4xx.
        if rec["status"] == "submitted":
            if rec.get("attempt_id"):
                self._send_json(200, {
                    "ok": True,
                    "assignment_id": sub.assignment_id,
                    "attempt_id": rec["attempt_id"],
                    "nogolog_id": None,        # not tracked across retries
                    "survivor_msg": None,
                    "idempotent_retry": True,
                })
                return
            self._send_error(
                500,
                f"assignment {sub.assignment_id} is submitted but no "
                f"attempt_id is recorded (coordinator state inconsistency)",
            )
            return
        if rec["status"] != "assigned":
            # released / expired / timed_out
            reason = ("stale_lease"
                      if rec["status"] == "timed_out"
                      else "non_assigned_state")
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": reason})
            self._send_error(
                409,
                f"assignment {sub.assignment_id} is in status "
                f"{rec['status']!r}; cannot accept result",
            )
            return

        # v0.4.2 Track C2: defence-in-depth — reject submissions whose
        # stamped lease_id no longer matches the current row.  Under
        # the present design this can only happen in pathological
        # cases (the reaper transitions assigned→timed_out atomically,
        # so a worker submitting after that should already have hit
        # the status check above).  Belt-and-suspenders for future
        # designs that re-issue lease_ids.
        attempt_lease = sub.attempt.get("lease_id")
        stored_lease = rec.get("lease_id") or ""
        if attempt_lease and stored_lease and attempt_lease != stored_lease:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "stale_lease"})
            self._send_error(
                409,
                f"stale_lease: attempt.lease_id {attempt_lease!r} "
                f"does not match current assignment lease "
                f"{stored_lease!r}",
            )
            return

        # Inject the candidate_id from the assignment into the
        # AttemptLedgerEntry so the worker cannot fabricate one.
        sub.attempt["candidate_id"] = rec["candidate_id"]

        # v0.4.2 Track C3: stamp generator_principal_id on every
        # gen-* result so the critic dispatcher can later refuse to
        # offer this attempt to a critic with the same principal.
        if rec["role"] == "gen":
            sub.attempt["generator_principal_id"] = (
                principal_id_from_worker_id(sub.worker_id))

        # v0.4.2 Track B — commit pinning.  Reject results that
        # reference a different HEAD than the coordinator's.  This
        # closes the audit-discovered hole that allowed workers on
        # `work` to submit results against a stale branch.
        commit_err = enforce_commit_match(
            attempt=sub.attempt,
            coordinator_git_commit=self.coordinator_git_commit,
        )
        if commit_err is not None:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "commit_mismatch"})
            self._send_error(403, commit_err)
            return

        # MVP-0.4 / Phase D — Generator/Critic role-gate.
        gate_err = enforce_role_for_submission(
            role=rec["role"],
            worker_id=sub.worker_id,
            attempt=sub.attempt,
            store=self.coordinator_store,
        )
        if gate_err is not None:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_role_gate_violations_total",
                    {"rule": rec["role"]})
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "role_gate"})
            self._send_error(403, gate_err)
            return

        # MVP-0.5.1 / PR 1: pre-validate every payload BEFORE any
        # canonical-ledger append.  This guarantees we never enter
        # the "main attempt appended, auxiliary append failed,
        # assignment not yet marked submitted" state where a
        # client retry produces a duplicate canonical entry.
        prevalidation_err = self._prevalidate_submission(sub)
        if prevalidation_err is not None:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "prevalidate"})
            self._send_error(400, prevalidation_err)
            return

        try:
            attempt_id = append_attempt(sub.attempt)
        except LedgerWriteError as e:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "ledger_validate"})
            self._send_error(400, f"attempt ledger rejected: {e.stderr}")
            return

        # MVP-0.5.1 / PR 1: mark submitted IMMEDIATELY after the
        # canonical attempt append.  Auxiliary log appends below
        # MUST NOT block the assignment transition.  Once the
        # canonical ledger has the attempt, the assignment is
        # "consumed" — even if the auxiliary writes fail, the
        # client should not be able to retry the main append.
        if not self.coordinator_store.mark_submitted(
                sub.assignment_id, attempt_id):
            # Concurrent transition (impossible under the
            # assigned-status check above, but defensive).
            self._send_error(
                500,
                f"attempt {attempt_id} merged but assignment "
                f"{sub.assignment_id} could not be marked submitted",
            )
            return

        # Auxiliary log appends — best-effort, NEVER roll back the
        # main attempt or unmark the assignment.  Failures here
        # surface as a `partial` field in the 200 response so the
        # operator can investigate (the canonical attempt is
        # already merged; auxiliary entries can be retried out-of-
        # band by Reviewer or backfilled from
        # outputs/attempts.jsonl).
        nogo_id: str | None = None
        survivor_msg: str | None = None
        partial: list[str] = []
        if sub.nogolog_entry is not None:
            try:
                nogo_id = append_nogolog(sub.nogolog_entry)
            except LedgerWriteError as e:
                partial.append(f"nogolog_append_failed: {e.stderr.strip()}")
        if sub.survivor_entry is not None:
            try:
                survivor_msg = append_survivor(sub.survivor_entry)
            except LedgerWriteError as e:
                partial.append(f"survivor_append_failed: {e.stderr.strip()}")

        if self.metrics is not None:
            self.metrics.inc(
                "autoresearch_results_merged_total",
                {
                    "role": rec["role"],
                    "verifier_status": str(
                        sub.attempt.get("verifier_status", "unknown")),
                    "critic_status": str(
                        sub.attempt.get("critic_status", "unknown")),
                },
            )
            if nogo_id is not None and sub.nogolog_entry is not None:
                self.metrics.inc(
                    "autoresearch_nogolog_appended_total",
                    {
                        "failure_class": str(
                            sub.nogolog_entry.get("failure_class", "other")),
                    },
                )

        resp_body: dict[str, Any] = {
            "ok": True,
            "assignment_id": sub.assignment_id,
            "attempt_id": attempt_id,
            "nogolog_id": nogo_id,
            "survivor_msg": survivor_msg,
        }
        if partial:
            resp_body["partial"] = partial
        self._send_json(200, resp_body)

    def _handle_dedup_register(self, payload: dict) -> None:
        """MVP-0.5.4 / PR 4: atomic check-and-set for content_hash.

        Workers compute their candidate's content_hash via
        coordinator.dedup.hash_gen_candidate() (or
        hash_critic_report() for crit role) and call this endpoint
        BEFORE running the verifier — if 200, they proceed; if 409,
        they release the assignment and pick a different one.

        Body shape:
            {
              "content_hash":  "<sha256 hex>",
              "assignment_id": "ASN-NNNNNN"
            }

        Responses:
            200 — newly registered; field `first_assignment_id`
                  equals the supplied `assignment_id`.
            409 — already seen; `first_assignment_id` is the
                  earlier assignment that registered the same hash.
            400 — body invalid.
        """
        content_hash = payload.get("content_hash", "")
        assignment_id = payload.get("assignment_id", "")
        if not isinstance(content_hash, str) or not content_hash \
                or not all(c in "0123456789abcdef" for c in content_hash):
            self._send_error(
                400,
                f"content_hash must be lowercase hex: {content_hash!r}")
            return
        err = validate_assignment_id(assignment_id)
        if err:
            self._send_error(400, err)
            return
        # Confirm the assignment exists (so workers can't pollute
        # the dedup table with hashes for non-existent assignments).
        rec = self.coordinator_store.get_assignment(assignment_id)
        if rec is None:
            self._send_error(
                404, f"unknown assignment_id: {assignment_id!r}")
            return
        inserted = self.coordinator_store.remember_dedup(
            content_hash, assignment_id)
        first = self.coordinator_store.lookup_dedup(content_hash)
        resp = DedupResponse(
            content_hash=content_hash,
            seen=not inserted,
            first_assignment_id=first,
        )
        self._send_json(200 if inserted else 409, resp.to_json())

    def _handle_release(self, payload: dict) -> None:
        assignment_id = payload.get("assignment_id", "")
        worker_id = payload.get("worker_id", "")
        err = (validate_assignment_id(assignment_id)
               or validate_worker_id(worker_id))
        if err:
            self._send_error(400, err)
            return
        ok = self.coordinator_store.release(assignment_id, worker_id)
        self._send_json(200 if ok else 409, {
            "ok": ok,
            "assignment_id": assignment_id,
        })

    # ------------------------------------------------------------------
    # Helpers.
    # ------------------------------------------------------------------

    # ------------------------------------------------------------------
    # Pre-validation (MVP-0.5.1 / PR 1).
    # ------------------------------------------------------------------

    def _prevalidate_submission(
        self, sub: ResultSubmission,
    ) -> str | None:
        """Validate every payload (attempt + nogolog + survivor) BEFORE
        any canonical-ledger append.  If a validator rejects, return
        a one-line reason; the HTTP layer translates that into 400.

        This guarantees we never enter the dangerous state where the
        main attempt has been appended but a subsequent auxiliary
        append rejects, leaving the canonical ledger updated and the
        assignment still in 'assigned'.
        """
        # Lazy import to avoid bloating module-load time.
        try:
            sys.path.insert(0, str(ROOT / "scripts"))
            from validate_jsonl import (   # noqa: E402
                validate_attempt as _vattempt,
                validate_nogo as _vnogo,
                validate_survivor as _vsurvivor,
            )
        except ImportError as e:           # pragma: no cover
            return f"validator import failed: {e}"

        # The attempt validator wants `id` and `created_at` to be
        # present; the writer script fills those in inside the lock.
        # We supply transient placeholders for prevalidation so we
        # don't reject a payload that the writer would have accepted.
        from datetime import datetime, timezone
        attempt_probe = dict(sub.attempt)
        attempt_probe.setdefault("id", "ATT-000000")
        attempt_probe.setdefault("created_at",
                                 datetime.now(tz=timezone.utc).strftime(
                                     "%Y-%m-%dT%H:%M:%SZ"))
        errs = _vattempt(attempt_probe)
        if errs:
            return f"attempt prevalidation failed: {errs}"

        if sub.nogolog_entry is not None:
            nogo_probe = dict(sub.nogolog_entry)
            nogo_probe.setdefault("id", "NOGO-000000")
            nogo_probe.setdefault("created_at",
                                  attempt_probe["created_at"])
            errs = _vnogo(nogo_probe)
            if errs:
                return f"nogolog prevalidation failed: {errs}"

        if sub.survivor_entry is not None:
            survivor_probe = dict(sub.survivor_entry)
            survivor_probe.setdefault("created_at",
                                      attempt_probe["created_at"])
            errs = _vsurvivor(survivor_probe)
            if errs:
                return f"survivor prevalidation failed: {errs}"

        return None

    def _send_json(self, status: int, body: dict) -> None:
        encoded = write_json(body)
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded)))
        self.end_headers()
        self.wfile.write(encoded)

    def _send_error(self, status: int, message: str) -> None:
        self._send_json(status, {"ok": False, "error": message})


# ---------------------------------------------------------------------------
# Server lifecycle.
# ---------------------------------------------------------------------------


def serve(
    bind_host: str = "127.0.0.1",
    bind_port: int = 8765,
    db_path: Path | None = None,
    quiet: bool = False,
    wave_gate: WaveGate | None = None,
    metrics: Metrics | None = None,
    enable_cost_budget_reaper: bool = True,
) -> tuple[ThreadingHTTPServer, threading.Thread, CoordinatorStore]:
    """Start the coordinator in a background thread.

    Returns (httpd, thread, store) so callers (especially the e2e
    test) can shut it down cleanly via httpd.shutdown() + thread.join()
    + store.close().
    """
    store = CoordinatorStore(db_path=db_path)
    autoresearch_mvp_version = _read_autoresearch_mvp_version()

    if wave_gate is None:
        try:
            wave_gate = WaveGate()
        except FileNotFoundError:
            # Missing thresholds file → degrade to capless (single
            # legitimate fallback, e.g. local-dev runs without spec/).
            wave_gate = None
        except ValueError:
            # MVP-0.5.5 / PR 5: AUTORESEARCH_INITIAL_WAVE > 0
            # without AUTORESEARCH_PROMOTION_FORCE=true raises
            # ValueError; let it propagate so the operator sees the
            # refusal at startup time, not silently runs capless.
            raise
    if metrics is None:
        metrics = Metrics()

    class BoundHandler(CoordinatorHandler):
        pass

    BoundHandler.coordinator_store = store
    BoundHandler.autoresearch_mvp_version = autoresearch_mvp_version
    BoundHandler.wave_gate = wave_gate
    BoundHandler.metrics = metrics
    BoundHandler.log_to_stderr = not quiet
    # v0.4.2 Track B: cache HEAD at startup so workers can verify
    # the coordinator's commit before doing any work, and so every
    # AttemptLedgerEntry can carry a coordinator-confirmed git_commit.
    coord_commit = _read_git_commit()
    BoundHandler.coordinator_git_commit = coord_commit
    BoundHandler.coordinator_git_ref = _read_git_ref()

    # v0.4.2 Track C2: cost-budget reaper.
    if enable_cost_budget_reaper:
        from .cost_budget import CostBudgetReaper, CostBudgetThresholds
        thresholds_path = ROOT / "spec" / "cost_budget_thresholds.toml"
        thresholds = CostBudgetThresholds(
            thresholds_path if thresholds_path.exists() else None)
        def _on_autofail(info: dict) -> None:
            if metrics is not None:
                metrics.inc(
                    "autoresearch_attempts_auto_failed_total",
                    {"reason": "timeout"})
        reaper = CostBudgetReaper(
            store=store,
            thresholds=thresholds,
            coordinator_git_commit=coord_commit,
            on_autofail=_on_autofail,
        )
        reaper.start()
        # Stash on the handler class so callers shutting down the
        # server can stop the reaper too.
        BoundHandler._cost_budget_reaper = reaper  # type: ignore[attr-defined]

    httpd = ThreadingHTTPServer((bind_host, bind_port), BoundHandler)
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    return httpd, thread, store


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="coordinator.server",
        description="Autoresearch coordinator HTTP service (MVP-0.2).",
    )
    parser.add_argument("--bind", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--db", type=Path, default=None,
                        help="SQLite state path (default coordinator/state.db)")
    parser.add_argument("--quiet", action="store_true",
                        help="Suppress per-request stderr logging.")
    args = parser.parse_args(argv[1:])

    httpd, thread, store = serve(
        bind_host=args.bind, bind_port=args.port,
        db_path=args.db, quiet=args.quiet,
    )
    sys.stderr.write(
        f"[coordinator] listening on http://{args.bind}:{args.port}\n")
    try:
        thread.join()
    except KeyboardInterrupt:
        sys.stderr.write("[coordinator] shutting down\n")
    finally:
        httpd.shutdown()
        store.close()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
