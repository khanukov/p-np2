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
import sys
import threading
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from uuid import uuid4

from . import __version__
from .dedup import hash_gen_candidate, hash_critic_report
from .leases import clamp_lease_seconds
from .ledger import (
    LedgerWriteError, append_attempt, append_nogolog, append_survivor,
)
from .metrics import Metrics
from .role_gate import enforce_role_for_submission
from .schema import (
    DedupResponse, HealthStatus, ResultSubmission, TaskAssignment,
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
            else:
                self._send_error(404, f"unknown path: {path!r}")
        except Exception as e:  # pragma: no cover
            self._send_error(500, f"internal error: {type(e).__name__}: {e}")

    # ------------------------------------------------------------------
    # Endpoint handlers.
    # ------------------------------------------------------------------

    def _handle_health(self) -> None:
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
        )
        self._send_json(200, status.to_json())

    def _handle_metrics(self) -> None:
        # Refresh gauges first so the scrape is point-in-time.
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
        if seed_pack_param:
            if seed_pack_param not in seed_packs:
                self._send_error(
                    404, f"unknown seed_pack: {seed_pack_param!r}")
                return
            seed_pack_id = seed_pack_param
        else:
            # Round-robin via assignment seq mod #packs.
            seq = self.coordinator_store._next_assignment_seq() - 1
            self.coordinator_store._conn.execute(  # roll the counter back
                "UPDATE counters SET value = ? WHERE name = 'assignment_seq'",
                (seq,),
            )
            seed_pack_id = seed_packs[seq % len(seed_packs)]

        try:
            lease_seconds = clamp_lease_seconds(
                int(lease_param) if lease_param is not None else None
            )
        except (ValueError, TypeError):
            self._send_error(400, f"invalid lease_seconds: {lease_param!r}")
            return

        # MVP-0.5 Phase E — wave-gate worker-cap enforcement.
        if self.wave_gate is not None:
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
        candidate_id = f"{seed_pack_id}_{uuid4().hex[:12]}"
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
        if rec["status"] != "assigned":
            self._send_error(
                409,
                f"assignment {sub.assignment_id} is in status "
                f"{rec['status']!r}; cannot accept result",
            )
            return

        # Inject the candidate_id from the assignment into the
        # AttemptLedgerEntry so the worker cannot fabricate one.
        sub.attempt["candidate_id"] = rec["candidate_id"]

        # MVP-0.4 / Phase D — Generator/Critic role-gate.
        # Server-side enforcement that:
        #   role=gen  => attempt.critic_status == "not_run", no supersedes;
        #   role=crit => attempt.critic_status in {pass, fail},
        #                attempt.supersedes points at an existing
        #                gen attempt, AND worker_id != that gen attempt's
        #                worker_id (Rule 12).
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

        try:
            attempt_id = append_attempt(sub.attempt)
        except LedgerWriteError as e:
            if self.metrics is not None:
                self.metrics.inc(
                    "autoresearch_results_rejected_total",
                    {"reason": "ledger_validate"})
            self._send_error(400, f"attempt ledger rejected: {e.stderr}")
            return

        nogo_id = None
        survivor_msg = None
        if sub.nogolog_entry is not None:
            try:
                nogo_id = append_nogolog(sub.nogolog_entry)
            except LedgerWriteError as e:
                # Attempt was already merged; nogolog is auxiliary,
                # report the failure but don't roll back.
                self._send_error(
                    500,
                    f"attempt {attempt_id} merged, but nogolog rejected: "
                    f"{e.stderr}",
                )
                return
        if sub.survivor_entry is not None:
            try:
                survivor_msg = append_survivor(sub.survivor_entry)
            except LedgerWriteError as e:
                self._send_error(
                    500,
                    f"attempt {attempt_id} merged, but survivor rejected: "
                    f"{e.stderr}",
                )
                return

        if not self.coordinator_store.mark_submitted(
                sub.assignment_id, attempt_id):
            # Should not happen — we held the assignment row check
            # above and assignments has a single-writer invariant.
            self._send_error(
                500,
                f"attempt {attempt_id} merged but assignment "
                f"{sub.assignment_id} could not be marked submitted",
            )
            return

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

        self._send_json(200, {
            "ok": True,
            "assignment_id": sub.assignment_id,
            "attempt_id": attempt_id,
            "nogolog_id": nogo_id,
            "survivor_msg": survivor_msg,
        })

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
        except Exception:
            wave_gate = None  # missing thresholds → run capless
    if metrics is None:
        metrics = Metrics()

    class BoundHandler(CoordinatorHandler):
        pass

    BoundHandler.coordinator_store = store
    BoundHandler.autoresearch_mvp_version = autoresearch_mvp_version
    BoundHandler.wave_gate = wave_gate
    BoundHandler.metrics = metrics
    BoundHandler.log_to_stderr = not quiet

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
