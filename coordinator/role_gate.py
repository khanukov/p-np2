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
    if cs == "fail":
        if not isinstance(attempt.get("critic_break_class"), str):
            return ("Critic submission with critic_status='fail' "
                    "must carry a non-null critic_break_class.")
    return None
