"""Coordinator metrics — Research Governance v0.1, MVP-0.5 (Phase E).

Stdlib-only Prometheus exposition format on `GET /v1/metrics`.

Counters and gauges are kept in-process (threading.Lock-protected).
On Phase F (sharded coordinator) the metrics layer is replaced by
a real Prometheus client; the API surface here is the stable
contract.

Exposed metric families (all increase monotonically except gauges):

  Counters:
    autoresearch_tasks_assigned_total{role}
    autoresearch_tasks_refused_total{reason}     # cap, dedup, role-prefix
    autoresearch_results_merged_total{role,verifier_status,critic_status}
    autoresearch_results_rejected_total{reason}  # role-gate, ledger-validate
    autoresearch_nogolog_appended_total{failure_class}
    autoresearch_role_gate_violations_total{rule}
  Gauges:
    autoresearch_in_flight_assignments
    autoresearch_current_wave
    autoresearch_worker_cap
"""

from __future__ import annotations

import threading
from collections import defaultdict
from typing import Any


_HELP = {
    "autoresearch_tasks_assigned_total":
        "Total /v1/task assignments issued.",
    "autoresearch_tasks_refused_total":
        "Total /v1/task refusals.",
    "autoresearch_results_merged_total":
        "Total /v1/result merges into outputs/attempts.jsonl.",
    "autoresearch_results_rejected_total":
        "Total /v1/result rejections (4xx).",
    "autoresearch_nogolog_appended_total":
        "Total NoGoLog appends.",
    "autoresearch_role_gate_violations_total":
        "Rule-12 / role-gate refusals (subset of results_rejected).",
    "autoresearch_in_flight_assignments":
        "Current count of leases in 'assigned' state.",
    "autoresearch_current_wave":
        "Current Wave-N (0..4).",
    "autoresearch_worker_cap":
        "Concurrent-worker cap for the current Wave.",
}


class Metrics:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._counters: dict[str, dict[tuple[tuple[str, str], ...], int]] = (
            defaultdict(lambda: defaultdict(int)))
        self._gauges: dict[str, int] = defaultdict(int)

    # ------------------------------------------------------------------
    # Mutation API.
    # ------------------------------------------------------------------

    def inc(self, name: str, labels: dict[str, str] | None = None,
            value: int = 1) -> None:
        key = self._labels_key(labels)
        with self._lock:
            self._counters[name][key] += value

    def set_gauge(self, name: str, value: int) -> None:
        with self._lock:
            self._gauges[name] = value

    # ------------------------------------------------------------------
    # Exposition.
    # ------------------------------------------------------------------

    def render_prometheus(self) -> bytes:
        lines: list[str] = []
        with self._lock:
            counters_snapshot = {
                k: dict(v) for k, v in self._counters.items()
            }
            gauges_snapshot = dict(self._gauges)
        for name, values in sorted(counters_snapshot.items()):
            lines.append(f"# HELP {name} {_HELP.get(name, '')}")
            lines.append(f"# TYPE {name} counter")
            for label_tuple, value in sorted(values.items()):
                if label_tuple:
                    label_str = "{" + ",".join(
                        f'{k}="{_escape_label(v)}"'
                        for k, v in label_tuple
                    ) + "}"
                else:
                    label_str = ""
                lines.append(f"{name}{label_str} {value}")
        for name, value in sorted(gauges_snapshot.items()):
            lines.append(f"# HELP {name} {_HELP.get(name, '')}")
            lines.append(f"# TYPE {name} gauge")
            lines.append(f"{name} {value}")
        text = "\n".join(lines) + "\n"
        return text.encode("utf-8")

    # ------------------------------------------------------------------
    # Helpers.
    # ------------------------------------------------------------------

    @staticmethod
    def _labels_key(
        labels: dict[str, str] | None,
    ) -> tuple[tuple[str, str], ...]:
        if not labels:
            return ()
        return tuple(sorted((k, str(v)) for k, v in labels.items()))


def _escape_label(value: str) -> str:
    return (value.replace("\\", r"\\")
                 .replace("\n", r"\n")
                 .replace('"', r'\"'))
