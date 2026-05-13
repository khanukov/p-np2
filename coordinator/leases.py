"""Coordinator lease state machine — Research Governance v0.1, MVP-0.2.

A lease is the right to attempt one (seed_pack_id, candidate_id) pair
within a deadline.  States:

    assigned    — lease active; worker has not yet POSTed a result
    submitted   — worker submitted a result; coordinator merged it
    expired     — deadline passed without submission; reclaimable
    released    — worker explicitly cancelled (POST /v1/release)

Transitions:

    *           --create_assignment-->  assigned
    assigned    --POST /v1/result   -->  submitted
    assigned    --POST /v1/release  -->  released
    assigned    --deadline passed   -->  expired  (via expire_due())

Once a lease has reached submitted/expired/released, no further
transitions are allowed.  The coordinator MAY allocate a NEW lease
for the same (seed_pack_id, candidate_id) pair after the previous
one expires; each allocation gets a fresh assignment_id.

Lease defaults (Phase B):

    DEFAULT_LEASE_SECONDS = 1800  # 30 minutes per attempt
    MAX_LEASE_SECONDS     = 7200  # 2-hour ceiling

These are intentionally generous so a real Lean kernel-check on a
log-width adversary fits comfortably; Phase E's
coordinator/cost_budget.py tightens them per-role.
"""

from __future__ import annotations

DEFAULT_LEASE_SECONDS = 1800
MAX_LEASE_SECONDS = 7200
MIN_LEASE_SECONDS = 30


def clamp_lease_seconds(requested: int | None) -> int:
    """Clamp a worker-requested lease to [MIN, MAX]; default if None."""
    if requested is None:
        return DEFAULT_LEASE_SECONDS
    if requested < MIN_LEASE_SECONDS:
        return MIN_LEASE_SECONDS
    if requested > MAX_LEASE_SECONDS:
        return MAX_LEASE_SECONDS
    return int(requested)
