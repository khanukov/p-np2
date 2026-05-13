"""Coordinator request/response schemas — Research Governance v0.1, MVP-0.2.

Stdlib-only dataclasses + manual JSON (de)serialisation.  Every shape
mirrors a canonical type from `spec/nogolog_schema.json` or is defined
explicitly here for the coordinator HTTP API.

The coordinator does NOT introduce a new ledger format; it accepts an
AttemptLedgerEntry payload (per `spec/nogolog_schema.json`) and merges
it via `scripts/attempts_append.py` to the canonical ledger.
"""

from __future__ import annotations

import dataclasses
import json
import re
from typing import Any


WORKER_ID_RE = re.compile(r"^(gen|crit|rev)-[a-z0-9_-]{1,64}$")
ASSIGNMENT_ID_RE = re.compile(r"^ASN-[0-9]{6}$")
CANDIDATE_ID_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,127}$")


@dataclasses.dataclass
class TaskAssignment:
    """Response shape for `GET /v1/task`.

    The coordinator hands the worker a candidate_id, points it at a
    seed pack to read, and gives it a deadline by which the worker
    must `POST /v1/result` (or the lease is reclaimed).

    `git_commit` / `git_ref` carry the coordinator's HEAD at startup.
    Workers MUST refuse to run on a different commit and MUST stamp
    `git_commit` on every submitted AttemptLedgerEntry (v0.4.2 Track B).

    `lease_id` is a UUID4 minted at lease creation time; the worker
    stamps it on the AttemptLedgerEntry so the cost-budget reaper's
    compare-and-set can never produce two ledger entries for one
    assignment slot (v0.4.2 Track C2).
    """
    assignment_id: str
    candidate_id: str
    seed_pack_id: str
    role: str  # "gen" | "crit"
    worker_id: str
    lease_seconds: int
    deadline: str  # ISO 8601 UTC
    git_commit: str = ""
    git_ref: str = ""
    lease_id: str = ""
    # v0.4.2 Track C3: when a critic task is dispatched against a
    # specific verified gen attempt, the coordinator stamps the
    # ATT-NNNNNN id here so the critic worker knows which gen
    # attempt to critique without manual lookup.  Empty string
    # otherwise (legacy / fresh-candidate critic).
    supersedes: str = ""

    def to_json(self) -> dict[str, Any]:
        return dataclasses.asdict(self)

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "TaskAssignment":
        return cls(
            assignment_id=data["assignment_id"],
            candidate_id=data["candidate_id"],
            seed_pack_id=data["seed_pack_id"],
            role=data["role"],
            worker_id=data["worker_id"],
            lease_seconds=data["lease_seconds"],
            deadline=data["deadline"],
            git_commit=data.get("git_commit", ""),
            git_ref=data.get("git_ref", ""),
            lease_id=data.get("lease_id", ""),
            supersedes=data.get("supersedes", ""),
        )


@dataclasses.dataclass
class ResultSubmission:
    """Request body for `POST /v1/result`.

    Wraps an AttemptLedgerEntry plus optional NoGoLogEntry plus
    metadata the coordinator needs to validate the lease.
    """
    assignment_id: str
    worker_id: str
    attempt: dict[str, Any]            # AttemptLedgerEntry payload
    nogolog_entry: dict[str, Any] | None = None
    survivor_entry: dict[str, Any] | None = None

    def to_json(self) -> dict[str, Any]:
        out = dataclasses.asdict(self)
        # Drop None-valued optional entries for cleanliness.
        if out.get("nogolog_entry") is None:
            out.pop("nogolog_entry", None)
        if out.get("survivor_entry") is None:
            out.pop("survivor_entry", None)
        return out

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "ResultSubmission":
        return cls(
            assignment_id=data["assignment_id"],
            worker_id=data["worker_id"],
            attempt=data["attempt"],
            nogolog_entry=data.get("nogolog_entry"),
            survivor_entry=data.get("survivor_entry"),
        )


@dataclasses.dataclass
class HealthStatus:
    """Response shape for `GET /v1/health`."""
    status: str  # "ok" | "draining" | "shutdown"
    coordinator_version: str
    autoresearch_mvp_version: str
    current_wave: int
    assigned_count: int
    completed_count: int
    abandoned_count: int
    coordinator_git_commit: str = ""
    coordinator_git_ref: str = ""

    def to_json(self) -> dict[str, Any]:
        return dataclasses.asdict(self)


@dataclasses.dataclass
class DedupResponse:
    """Response shape for `GET /v1/dedup?content_hash=…`."""
    content_hash: str
    seen: bool
    first_assignment_id: str | None  # populated when seen=True

    def to_json(self) -> dict[str, Any]:
        return dataclasses.asdict(self)


def validate_worker_id(worker_id: str) -> str | None:
    """Return None if valid, else an error message."""
    if not isinstance(worker_id, str):
        return f"worker_id must be a string, got {type(worker_id).__name__}"
    if not WORKER_ID_RE.match(worker_id):
        return (f"worker_id must match {WORKER_ID_RE.pattern} "
                f"(role prefix gen-/crit-/rev-): {worker_id!r}")
    return None


def principal_id_from_worker_id(worker_id: str) -> str:
    """v0.4.2 Track C3: extract the principal id (suffix after the
    role prefix) from a worker_id.

    Examples:
        gen-alice         -> "alice"
        crit-alice        -> "alice"
        rev-bob_team-1    -> "bob_team-1"
        gen-              -> ""        (degenerate)

    The principal id is a *protocol-level integrity guard* — workers
    self-declare their worker_id, so two different humans can both
    claim the same principal "alice" simply by both running with
    `--worker-id gen-alice` / `--worker-id crit-alice`.  Until the
    deferred Phase C-3 JWT auth track ships, principal-identity
    enforcement closes the prefix-only bypass (gen-alice -> crit-alice)
    but does NOT close impersonation.
    """
    if not isinstance(worker_id, str):
        return ""
    if "-" not in worker_id:
        return worker_id
    return worker_id.split("-", 1)[1]


def validate_role(role: str) -> str | None:
    if role not in ("gen", "crit", "rev"):
        return f"role must be one of gen/crit/rev: {role!r}"
    return None


def validate_assignment_id(asn_id: str) -> str | None:
    if not isinstance(asn_id, str) or not ASSIGNMENT_ID_RE.match(asn_id):
        return f"assignment_id must match {ASSIGNMENT_ID_RE.pattern}: {asn_id!r}"
    return None


def write_json(payload: dict[str, Any]) -> bytes:
    """Canonicalise JSON output (sorted keys, no trailing newline)."""
    return json.dumps(payload, sort_keys=True, ensure_ascii=False).encode(
        "utf-8")
