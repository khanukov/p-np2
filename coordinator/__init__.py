"""Autoresearch Coordinator — Research Governance v0.1, MVP-0.2 (Phase B).

Single-machine coordinator service that brokers task assignments to
parallel workers and atomically merges their results into the
canonical append-only JSONL ledgers under outputs/.

Scope (MVP-0.2 / Phase B):
    * one host, sqlite state, 1K worker ceiling
    * no auth, no quota, no metrics
    * Phase A flock primitives are reused for canonical ledger writes
    * Generator/Critic role separation enforced at protocol level only
      (Phase D moves it to infrastructure level)

See spec/coordinator_protocol.md for the HTTP API contract.
"""

__version__ = "0.2.0"
