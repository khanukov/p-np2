"""Generator/Critic role-gate — Research Governance v0.1, MVP-0.4 (Phase D).

Enforces Rule 12 (Generator/Critic separation) at the infrastructure
level.  The HTTP layer delegates to these pure functions on every
`POST /v1/result`.

Rules:

    role = "gen"
        attempt.critic_status MUST be "not_run".
        attempt MUST NOT carry `supersedes`.

    role = "crit"
        attempt.critic_status MUST be in {"pass", "fail"}.
        attempt MUST carry `supersedes = "ATT-NNNNNN"` of the gen
            attempt being critiqued.
        worker_id MUST differ from the worker_id that originally
            generated `supersedes`.

The "differ" check is the heart of Rule 12: a worker that played
the Generator role for a candidate may NOT subsequently play the
Critic role for the same candidate.  This was protocol-only in
MVP-0.2 (Phase B); MVP-0.4 (Phase D) makes it an HTTP-server-side
hard reject.

Phase E adds a dispatcher that automatically issues
`role=crit` tasks against pending gen attempts; that is OUT OF
SCOPE here.
"""

from __future__ import annotations

from typing import Any, Optional, Protocol


class _StoreLike(Protocol):
    """Minimal subset of `coordinator.store.CoordinatorStore` used by
    the role gate.  Defined as a Protocol so the test fixture can
    pass a stub."""

    def find_worker_for_attempt(
        self, attempt_id: str,
    ) -> Optional[str]: ...


def enforce_commit_match(
    attempt: dict[str, Any],
    coordinator_git_commit: str,
) -> str | None:
    """v0.4.2 Track B / v0.4.3 Blocker-1: reject results submitted
    from a different commit OR with no git_commit at all.

    `attempt.git_commit` MUST equal the coordinator's HEAD that was
    cached at server start.  Returns a non-None error string on
    mismatch or absence (caller maps that to a 403).

    Backwards-compat policy:

      * Coordinator HEAD unresolved (`coordinator_git_commit == ""`):
        gate degrades to no-op so a non-git-managed deployment
        still works.
      * Coordinator HEAD resolved AND
        `attempt.git_commit` missing/empty:
        REJECTED with `commit_missing` (v0.4.3 Blocker-1).
        Backwards-compat for old jsonl ENTRIES that predate the
        cutoff date is enforced ONLY by
        `scripts/validate_jsonl.py`'s on-disk validation; live
        HTTP submissions MUST stamp the field.
    """
    if not coordinator_git_commit:
        return None  # coordinator can't resolve HEAD; degrade
    attempt_commit = attempt.get("git_commit")
    if attempt_commit is None or attempt_commit == "":
        return ("commit_missing: coordinator HEAD is "
                f"{coordinator_git_commit!r} but attempt.git_commit is "
                "absent or empty.  Workers MUST stamp git_commit on "
                "every /v1/result; backwards-compat windows apply only "
                "to ledger entries on disk, not live submissions.")
    if not isinstance(attempt_commit, str):
        return f"attempt.git_commit must be a string, got {type(attempt_commit).__name__}"
    # Accept short prefix match too (>=7 hex chars), since some clients
    # may stamp short hashes; both must agree on the prefix.
    short = max(7, min(len(attempt_commit), len(coordinator_git_commit)))
    if attempt_commit[:short] != coordinator_git_commit[:short]:
        return (f"commit_mismatch: attempt.git_commit={attempt_commit!r} "
                f"does not match coordinator HEAD "
                f"{coordinator_git_commit!r}; worker is on a different "
                "branch / commit and must re-checkout before submitting.")
    return None


def enforce_role_for_submission(
    role: str,
    worker_id: str,
    attempt: dict[str, Any],
    store: _StoreLike,
) -> str | None:
    """Return None if the (role, worker_id, attempt) tuple is
    well-formed; otherwise return a one-line human-readable error.

    The caller is `server.py::_handle_result`, which translates a
    non-None return into a 4xx response.
    """
    if not isinstance(attempt, dict):
        return "attempt payload must be a JSON object"

    if role == "gen":
        return _enforce_gen(worker_id, attempt)
    if role == "crit":
        return _enforce_crit(worker_id, attempt, store)
    if role == "rev":
        # Reviewers (humans) operate outside the autoresearch
        # cycle; Phase D leaves them unrestricted by role-gate.
        return None
    return f"unknown role {role!r}"


def _enforce_gen(worker_id: str, attempt: dict[str, Any]) -> str | None:
    cs = attempt.get("critic_status")
    if cs != "not_run":
        return (f"Generator (worker_id={worker_id!r}) submission "
                f"must have attempt.critic_status='not_run'; got "
                f"{cs!r}.  Critic verdicts come from a separate "
                "crit-* worker.")
    if "supersedes" in attempt and attempt["supersedes"] is not None:
        return (f"Generator submission must NOT carry 'supersedes'; "
                f"got {attempt.get('supersedes')!r}.  Supersedes is "
                "reserved for Critic verdicts that re-classify a "
                "previous gen attempt.")
    return None


def _enforce_crit(
    worker_id: str,
    attempt: dict[str, Any],
    store: _StoreLike,
) -> str | None:
    cs = attempt.get("critic_status")
    if cs not in ("pass", "fail"):
        return (f"Critic (worker_id={worker_id!r}) submission must "
                f"have attempt.critic_status in {{'pass','fail'}}; "
                f"got {cs!r}.")
    supersedes = attempt.get("supersedes")
    if not isinstance(supersedes, str) or not supersedes.startswith("ATT-"):
        return ("Critic submission must carry "
                f"'supersedes'='ATT-NNNNNN' of the gen attempt being "
                f"critiqued; got {supersedes!r}.")
    gen_worker = store.find_worker_for_attempt(supersedes)
    if gen_worker is None:
        return (f"Critic submission's supersedes target {supersedes} "
                "is unknown to the coordinator (no assignment row "
                "with this attempt_id).")
    if gen_worker == worker_id:
        return ("Rule 12 violation: worker "
                f"{worker_id!r} previously generated attempt "
                f"{supersedes} and is now attempting to criticise "
                "the same candidate.  Generator and Critic must be "
                "different workers.")
    # v0.4.2 Track C3: principal-identity check (protocol-level
    # integrity guard, NOT authentication — see spec/worker_roles.md).
    # gen-alice + crit-alice would pass the worker_id check above
    # but fail this one.
    from .schema import principal_id_from_worker_id  # avoid cycle
    crit_principal = principal_id_from_worker_id(worker_id)
    gen_principal = principal_id_from_worker_id(gen_worker)
    if crit_principal and gen_principal and crit_principal == gen_principal:
        return ("Rule 12 violation (principal): worker "
                f"{worker_id!r} shares principal id "
                f"{crit_principal!r} with the gen worker "
                f"{gen_worker!r} that produced {supersedes}.  "
                "Same principal cannot generate AND criticise the "
                "same candidate, regardless of role prefix.")
    if cs == "fail":
        if not isinstance(attempt.get("critic_break_class"), str):
            return ("Critic submission with critic_status='fail' "
                    "must carry a non-null critic_break_class.")
    return None
