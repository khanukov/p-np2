"""Coordinator state store — sqlite, single-machine, single-writer.

Holds:
  * assignments — (assignment_id, candidate_id, seed_pack_id, role,
                    worker_id, leased_at, deadline, status)
  * dedup       — (content_hash, first_assignment_id, first_seen_at)

The canonical ledger continues to live at outputs/attempts.jsonl;
this store is internal coordinator bookkeeping.  The store file lives
at coordinator/state.db and is gitignored.

Phase-B scope (single-machine, ~1K worker ceiling) is comfortable for
sqlite.  Phase F replaces this with a sharded backend.
"""

from __future__ import annotations

import sqlite3
import threading
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

DEFAULT_DB_PATH = Path(__file__).resolve().parent / "state.db"

ASSIGNMENT_STATUS_VALUES = (
    "assigned",       # lease active, worker has not yet submitted
    "submitted",      # worker submitted; coordinator merged result
    "expired",        # lease expired without submission; reclaimable
    "released",       # worker explicitly cancelled (POST /v1/release)
    # v0.4.2 Track C2: cost-budget reaper claimed this row for
    # auto-fail and is in the middle of writing FAIL_TIMEOUT to the
    # canonical ledger.  Terminal transition `timed_out -> submitted`
    # follows.  /v1/result on a timed_out assignment returns 409.
    "timed_out",
)


_INIT_SQL = """
CREATE TABLE IF NOT EXISTS assignments (
    assignment_id   TEXT PRIMARY KEY,
    candidate_id    TEXT NOT NULL,
    seed_pack_id    TEXT NOT NULL,
    role            TEXT NOT NULL CHECK (role IN ('gen','crit','rev')),
    worker_id       TEXT NOT NULL,
    leased_at       TEXT NOT NULL,
    deadline        TEXT NOT NULL,
    status          TEXT NOT NULL DEFAULT 'assigned'
                    CHECK (status IN ('assigned','submitted','expired','released','timed_out')),
    submitted_at    TEXT,
    attempt_id      TEXT,
    lease_id        TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS ix_assignments_status
    ON assignments(status, deadline);

CREATE INDEX IF NOT EXISTS ix_assignments_worker
    ON assignments(worker_id, status);

CREATE TABLE IF NOT EXISTS dedup (
    content_hash             TEXT PRIMARY KEY,
    first_assignment_id      TEXT NOT NULL,
    first_seen_at            TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS counters (
    name   TEXT PRIMARY KEY,
    value  INTEGER NOT NULL
);
"""


def _migrate(conn: sqlite3.Connection) -> None:
    """v0.4.2 Track C2: ensure pre-existing assignments tables get the
    `lease_id` column.  Older state.db files predate the column; ALTER
    TABLE is idempotent under sqlite when guarded by a PRAGMA check.
    """
    cols = {r[1] for r in conn.execute(
        "PRAGMA table_info(assignments)").fetchall()}
    if "lease_id" not in cols:
        conn.execute(
            "ALTER TABLE assignments ADD COLUMN lease_id "
            "TEXT NOT NULL DEFAULT ''")


class CoordinatorStore:
    """Thread-safe SQLite-backed coordinator state.

    Concurrency model:
      * One connection per `CoordinatorStore` instance.
      * All write methods take an instance-level `RLock` so that
        the read-modify-write logic for assignment_id allocation
        and dedup insertion is atomic across the threads of one
        process.
      * Sqlite's own WAL mode handles cross-process consistency
        (Phase B is single-process, but WAL is cheap insurance).
    """

    def __init__(self, db_path: Path | None = None) -> None:
        self.db_path = Path(db_path) if db_path else DEFAULT_DB_PATH
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(
            str(self.db_path),
            check_same_thread=False,
            isolation_level=None,  # autocommit; we do our own BEGIN
        )
        self._conn.execute("PRAGMA journal_mode = WAL;")
        self._conn.execute("PRAGMA synchronous = NORMAL;")
        self._conn.executescript(_INIT_SQL)
        _migrate(self._conn)

    # ------------------------------------------------------------------
    # Counters / id allocation.
    # ------------------------------------------------------------------

    def _next_assignment_seq(self) -> int:
        with self._lock:
            row = self._conn.execute(
                "SELECT value FROM counters WHERE name = 'assignment_seq'"
            ).fetchone()
            if row is None:
                self._conn.execute(
                    "INSERT INTO counters(name, value) VALUES "
                    "('assignment_seq', 1)"
                )
                return 1
            new_value = int(row[0]) + 1
            self._conn.execute(
                "UPDATE counters SET value = ? WHERE name = 'assignment_seq'",
                (new_value,),
            )
            return new_value

    def next_assignment_id(self) -> str:
        return f"ASN-{self._next_assignment_seq():06d}"

    def next_seed_pack_rr(self) -> int:
        """Monotonic counter for seed-pack round-robin selection.

        Separate from `assignment_seq` so the seed-pack rotation
        does not piggy-back on the assignment id allocator (which
        would force a counter rollback under concurrency — the
        bug PR 2 / MVP-0.5.2 closes).
        """
        with self._lock:
            row = self._conn.execute(
                "SELECT value FROM counters WHERE name = 'seed_pack_rr_seq'"
            ).fetchone()
            if row is None:
                self._conn.execute(
                    "INSERT INTO counters(name, value) VALUES "
                    "('seed_pack_rr_seq', 1)"
                )
                return 1
            new_value = int(row[0]) + 1
            self._conn.execute(
                "UPDATE counters SET value = ? "
                " WHERE name = 'seed_pack_rr_seq'",
                (new_value,),
            )
            return new_value

    # ------------------------------------------------------------------
    # Assignments.
    # ------------------------------------------------------------------

    def create_assignment(
        self,
        assignment_id: str,
        candidate_id: str,
        seed_pack_id: str,
        role: str,
        worker_id: str,
        lease_seconds: int,
    ) -> dict[str, str]:
        now = datetime.now(tz=timezone.utc)
        deadline = now + timedelta(seconds=lease_seconds)
        leased_at_s = now.strftime("%Y-%m-%dT%H:%M:%SZ")
        deadline_s = deadline.strftime("%Y-%m-%dT%H:%M:%SZ")
        # v0.4.2 Track C2: every lease gets a UUID4 lease_id.  The
        # reaper uses (assignment_id, lease_id) for compare-and-set
        # so a worker submitting at the same instant as the reaper
        # can never produce two ledger entries for one slot.
        lease_id = str(uuid.uuid4())
        with self._lock:
            self._conn.execute(
                "INSERT INTO assignments(assignment_id, candidate_id, "
                " seed_pack_id, role, worker_id, leased_at, deadline, "
                " lease_id) "
                " VALUES(?,?,?,?,?,?,?,?)",
                (assignment_id, candidate_id, seed_pack_id, role,
                 worker_id, leased_at_s, deadline_s, lease_id),
            )
        return {
            "assignment_id": assignment_id,
            "candidate_id": candidate_id,
            "seed_pack_id": seed_pack_id,
            "role": role,
            "worker_id": worker_id,
            "leased_at": leased_at_s,
            "deadline": deadline_s,
            "lease_id": lease_id,
        }

    def get_assignment(self, assignment_id: str) -> dict[str, str] | None:
        with self._lock:
            row = self._conn.execute(
                "SELECT assignment_id, candidate_id, seed_pack_id, role, "
                " worker_id, leased_at, deadline, status, submitted_at, "
                " attempt_id, lease_id FROM assignments WHERE assignment_id = ?",
                (assignment_id,),
            ).fetchone()
        if row is None:
            return None
        return {
            "assignment_id": row[0],
            "candidate_id": row[1],
            "seed_pack_id": row[2],
            "role": row[3],
            "worker_id": row[4],
            "leased_at": row[5],
            "deadline": row[6],
            "status": row[7],
            "submitted_at": row[8],
            "attempt_id": row[9],
            "lease_id": row[10],
        }

    # ------------------------------------------------------------------
    # v0.4.2 Track C2 — cost-budget reaper helpers.
    # ------------------------------------------------------------------

    def find_overdue_for_autofail(self, now_iso: str) -> list[dict]:
        """Return assigned-status assignments whose deadline has
        passed.  Each row carries `assignment_id` + `lease_id` plus
        the candidate metadata the reaper needs to synthesise an
        AttemptLedgerEntry.  Used only by the cost-budget reaper.
        """
        with self._lock:
            rows = self._conn.execute(
                "SELECT assignment_id, candidate_id, seed_pack_id, "
                " role, worker_id, lease_id "
                " FROM assignments "
                " WHERE status = 'assigned' AND deadline < ? "
                " AND lease_id != ''",
                (now_iso,),
            ).fetchall()
        return [
            {
                "assignment_id": r[0],
                "candidate_id": r[1],
                "seed_pack_id": r[2],
                "role": r[3],
                "worker_id": r[4],
                "lease_id": r[5],
            }
            for r in rows
        ]

    def claim_for_timeout(
        self, assignment_id: str, lease_id: str,
    ) -> bool:
        """Atomic compare-and-set: assigned -> timed_out, only if
        `lease_id` still matches.  Returns True if the reaper now
        owns this row, False if the worker beat us (assignment
        already moved to submitted/released/expired) or the
        lease_id has changed.
        """
        with self._lock:
            cur = self._conn.execute(
                "UPDATE assignments SET status = 'timed_out' "
                " WHERE assignment_id = ? AND lease_id = ? "
                " AND status = 'assigned'",
                (assignment_id, lease_id),
            )
            return cur.rowcount == 1

    def finalize_timed_out(
        self, assignment_id: str, attempt_id: str,
    ) -> bool:
        """Terminal transition timed_out -> submitted with the
        FAIL_TIMEOUT attempt_id the reaper synthesised.
        """
        now_s = datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        with self._lock:
            cur = self._conn.execute(
                "UPDATE assignments SET status = 'submitted', "
                " submitted_at = ?, attempt_id = ? "
                " WHERE assignment_id = ? AND status = 'timed_out'",
                (now_s, attempt_id, assignment_id),
            )
            return cur.rowcount == 1

    def mark_submitted(
        self, assignment_id: str, attempt_id: str,
    ) -> bool:
        """Atomic transition assigned → submitted.  Returns True on
        success, False if the assignment is missing, already-submitted,
        expired, or released.
        """
        now_s = datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        with self._lock:
            cur = self._conn.execute(
                "UPDATE assignments SET status = 'submitted', "
                " submitted_at = ?, attempt_id = ? "
                " WHERE assignment_id = ? AND status = 'assigned'",
                (now_s, attempt_id, assignment_id),
            )
            return cur.rowcount == 1

    def expire_due(self) -> int:
        """Mark all assigned-but-deadline-passed assignments as expired.
        Returns the number of rows affected."""
        now_s = datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        with self._lock:
            cur = self._conn.execute(
                "UPDATE assignments SET status = 'expired' "
                " WHERE status = 'assigned' AND deadline < ?",
                (now_s,),
            )
            return cur.rowcount

    def release(self, assignment_id: str, worker_id: str) -> bool:
        """Atomic transition assigned → released for explicit cancel."""
        with self._lock:
            cur = self._conn.execute(
                "UPDATE assignments SET status = 'released' "
                " WHERE assignment_id = ? AND worker_id = ? "
                " AND status = 'assigned'",
                (assignment_id, worker_id),
            )
            return cur.rowcount == 1

    def find_worker_for_attempt(
        self, attempt_id: str,
    ) -> str | None:
        """Return the `worker_id` that submitted `attempt_id`, or None
        if no assignment row carries it.  Used by the role-gate
        (MVP-0.4 / Phase D) to enforce that a Critic is not the same
        worker as the original Generator."""
        with self._lock:
            row = self._conn.execute(
                "SELECT worker_id FROM assignments "
                " WHERE attempt_id = ? LIMIT 1",
                (attempt_id,),
            ).fetchone()
        return row[0] if row else None

    def find_pending_critic_attempt(
        self,
        crit_principal_id: str,
        attempts_jsonl_path: Path,
    ) -> dict | None:
        """v0.4.2 Track C3: scan the canonical attempts ledger for
        the oldest gen attempt that:

          * has `verifier_status` in {PASS, PASS_SHAPE_ONLY}
          * has `critic_status` == "not_run"
          * is not already pointed at by a later `supersedes`
          * has `generator_principal_id` != `crit_principal_id`

        Returns the matching ledger entry as a dict, or None if no
        match (in which case the caller should 503 with reason
        `no_pending_critic`).

        This reads `outputs/attempts.jsonl` directly; it does NOT
        consult sqlite.  At <=20 workers this is fine; sharding
        revisits the design.
        """
        if not attempts_jsonl_path.exists():
            return None
        # First pass: collect all `supersedes` values (which gen
        # attempts have already been critiqued).
        critiqued: set[str] = set()
        candidates: list[dict] = []
        try:
            with attempts_jsonl_path.open(encoding="utf-8") as f:
                for raw in f:
                    line = raw.strip()
                    if not line:
                        continue
                    try:
                        import json as _json
                        entry = _json.loads(line)
                    except Exception:
                        continue
                    if not isinstance(entry, dict):
                        continue
                    sup = entry.get("supersedes")
                    if isinstance(sup, str) and sup.startswith("ATT-"):
                        critiqued.add(sup)
                    if (entry.get("verifier_status") in
                            ("PASS", "PASS_SHAPE_ONLY")
                            and entry.get("critic_status") == "not_run"):
                        candidates.append(entry)
        except OSError:
            return None
        # Second pass: pick oldest unmatched whose gen principal
        # differs from the critic's.
        for entry in candidates:
            entry_id = entry.get("id")
            if not isinstance(entry_id, str):
                continue
            if entry_id in critiqued:
                continue
            gen_principal = entry.get("generator_principal_id") or ""
            # Empty principal means we can't confirm separation.  In
            # that case, only allow if the worker prefixes also
            # differ — but the dispatcher's caller will additionally
            # enforce role_gate's worker_id check at submission time,
            # so we conservatively skip unknown principals.
            if not gen_principal:
                continue
            if gen_principal == crit_principal_id:
                continue
            return entry
        return None

    def counts_by_status(self) -> dict[str, int]:
        with self._lock:
            rows = self._conn.execute(
                "SELECT status, COUNT(*) FROM assignments GROUP BY status"
            ).fetchall()
        return {r[0]: int(r[1]) for r in rows}

    # ------------------------------------------------------------------
    # Dedup.
    # ------------------------------------------------------------------

    def lookup_dedup(self, content_hash: str) -> str | None:
        """Return the first_assignment_id for a known content_hash,
        else None."""
        with self._lock:
            row = self._conn.execute(
                "SELECT first_assignment_id FROM dedup "
                " WHERE content_hash = ?",
                (content_hash,),
            ).fetchone()
        return row[0] if row else None

    def remember_dedup(
        self, content_hash: str, assignment_id: str,
    ) -> bool:
        """Insert a (content_hash → assignment_id) mapping if absent.
        Returns True on insert, False if already present."""
        now_s = datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        with self._lock:
            try:
                self._conn.execute(
                    "INSERT INTO dedup(content_hash, "
                    " first_assignment_id, first_seen_at) "
                    " VALUES(?,?,?)",
                    (content_hash, assignment_id, now_s),
                )
                return True
            except sqlite3.IntegrityError:
                return False

    # ------------------------------------------------------------------
    # Lifecycle.
    # ------------------------------------------------------------------

    def close(self) -> None:
        with self._lock:
            self._conn.close()
