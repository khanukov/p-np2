"""Critic dispatcher — Research Governance v0.1, Autoresearch MVP-0.5.6.

v0.4.2 Track C3.  When `GET /v1/task?role=crit&worker_id=crit-X` is
called WITHOUT an explicit `seed_pack` parameter, the dispatcher
finds an oldest-pending verified gen attempt that the requesting
critic is allowed to critique under Rule 12 + principal identity,
and returns a TaskAssignment carrying the gen attempt's
candidate_id and `supersedes=ATT-NNNNNN`.

Rule 12 is enforced at TWO layers:

  * dispatcher (this module): refuses to OFFER a gen attempt to a
    critic whose principal id matches the gen attempt's
    `generator_principal_id`.  Gen-alice's attempt is never
    offered to a crit-alice request.
  * role_gate (`coordinator/role_gate.py::_enforce_crit`): on
    submission, double-checks that worker_id != gen worker_id AND
    principal != gen principal.  Belt-and-suspenders against ad-hoc
    re-critique requests that bypass the dispatcher.

Threat model.  Principal id is the suffix of worker_id (e.g.
`gen-alice` -> "alice").  A worker can self-declare any worker_id
until JWT auth ships (deferred).  This dispatcher is therefore a
*protocol-level integrity guard* for honest, coordinated workers.
It is not authentication.
"""

from __future__ import annotations

from pathlib import Path
from typing import Optional

from .schema import principal_id_from_worker_id
from .store import CoordinatorStore


class NoPendingCriticAttempt(Exception):
    """Raised by the dispatcher when no gen attempt is available
    for the requesting critic principal."""


def dispatch_critic_task(
    store: CoordinatorStore,
    crit_worker_id: str,
    attempts_jsonl_path: Path,
) -> dict:
    """Return a dict with the keys the caller (`_handle_task`) needs
    to mint a TaskAssignment:

        {
          "candidate_id":    str,   # gen attempt's candidate_id
          "seed_pack_id":    str,   # gen attempt's seed_pack_id (or "")
          "supersedes":      str,   # ATT-NNNNNN of the gen attempt
        }

    Raises `NoPendingCriticAttempt` if no eligible gen attempt is
    available for this critic's principal id.
    """
    crit_principal = principal_id_from_worker_id(crit_worker_id)
    entry: Optional[dict] = store.find_pending_critic_attempt(
        crit_principal_id=crit_principal,
        attempts_jsonl_path=attempts_jsonl_path,
    )
    if entry is None:
        raise NoPendingCriticAttempt(
            "no pending gen attempt is available to a critic with "
            f"principal_id={crit_principal!r}; either no verified "
            "attempts await Critic, or all of them share the "
            "critic's principal id (Rule 12 / principal identity).")
    return {
        "candidate_id": entry.get("candidate_id", ""),
        "seed_pack_id": entry.get("seed_pack_id", "") or "",
        "supersedes": entry.get("id", ""),
    }
