"""Idea registry: storage layer for the idea-search machine.

Each idea lives under ``registry/ideas/<idea_id>/`` and is also
indexed by one JSON line in ``registry/index.jsonl``.  The on-disk
layout matches the seed-pack convention from
``pnp3/Docs/IDEA_SEARCH_PIPELINE.md``.
"""

from __future__ import annotations

import json
import os
import secrets
import time
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional


# Default registry directory (resolved relative to this module).
REGISTRY_DIR = Path(__file__).resolve().parent / "registry"
INDEX_FILE = REGISTRY_DIR / "index.jsonl"
IDEAS_DIR = REGISTRY_DIR / "ideas"


@dataclass
class StageResult:
    """One stage's verdict + saved markdown report filename."""

    stage: str
    verdict: str
    ran_at: str
    report_file: str
    model: str
    is_mock: bool


@dataclass
class Idea:
    """In-memory representation of one idea record."""

    id: str
    created_at: str
    thesis: str
    prerequisites: List[str] = field(default_factory=list)
    mechanism: str = ""
    target_interface: str = ""
    novelty_self_assessment: str = ""
    stages: Dict[str, StageResult] = field(default_factory=dict)
    final_verdict: str = "OPEN"

    def to_dict(self) -> dict:
        d = asdict(self)
        d["stages"] = {k: asdict(v) for k, v in self.stages.items()}
        return d

    @classmethod
    def from_dict(cls, d: dict) -> "Idea":
        stages = {k: StageResult(**v) for k, v in d.get("stages", {}).items()}
        idea = cls(
            id=d["id"],
            created_at=d["created_at"],
            thesis=d.get("thesis", ""),
            prerequisites=d.get("prerequisites", []),
            mechanism=d.get("mechanism", ""),
            target_interface=d.get("target_interface", ""),
            novelty_self_assessment=d.get("novelty_self_assessment", ""),
            stages=stages,
            final_verdict=d.get("final_verdict", "OPEN"),
        )
        return idea


def _ensure_dirs() -> None:
    REGISTRY_DIR.mkdir(parents=True, exist_ok=True)
    IDEAS_DIR.mkdir(parents=True, exist_ok=True)


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def new_idea_id() -> str:
    """Create a fresh idea id with timestamp + short random suffix."""
    return f"idea-{int(time.time())}-{secrets.token_hex(3)}"


def idea_dir(idea_id: str) -> Path:
    return IDEAS_DIR / idea_id


def save_idea(idea: Idea) -> Path:
    """Write idea metadata to disk and append to the JSONL index."""
    _ensure_dirs()
    d = idea_dir(idea.id)
    d.mkdir(parents=True, exist_ok=True)
    (d / "idea.json").write_text(json.dumps(idea.to_dict(), indent=2) + "\n")
    _append_index_line(idea)
    return d


def load_idea(idea_id: str) -> Idea:
    p = idea_dir(idea_id) / "idea.json"
    if not p.exists():
        raise FileNotFoundError(f"unknown idea id: {idea_id}")
    return Idea.from_dict(json.loads(p.read_text()))


def list_ideas() -> List[Idea]:
    _ensure_dirs()
    out: List[Idea] = []
    for entry in sorted(IDEAS_DIR.iterdir() if IDEAS_DIR.exists() else []):
        ij = entry / "idea.json"
        if ij.exists():
            try:
                out.append(Idea.from_dict(json.loads(ij.read_text())))
            except Exception:
                continue
    return out


def save_stage_report(idea: Idea, stage_name: str, markdown: str) -> str:
    """Save the markdown report for one stage and return the filename."""
    _ensure_dirs()
    d = idea_dir(idea.id)
    d.mkdir(parents=True, exist_ok=True)
    filename = f"{stage_name}.md"
    (d / filename).write_text(markdown)
    return filename


def write_verdict_summary(idea: Idea) -> Path:
    """Write/update verdict.md for the idea."""
    d = idea_dir(idea.id)
    d.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("# Final verdict\n")
    lines.append(f"\nIdea id: `{idea.id}`")
    lines.append(f"Created: {idea.created_at}")
    lines.append(f"Status: **{idea.final_verdict}**\n")
    lines.append("## Stage outcomes\n")
    lines.append("| Stage | Verdict | Model | Mock | Ran at |")
    lines.append("|---|---|---|---|---|")
    for k, v in idea.stages.items():
        lines.append(
            f"| {k} | {v.verdict} | {v.model} | {'yes' if v.is_mock else 'no'} | {v.ran_at} |"
        )
    lines.append("\n## Thesis\n")
    lines.append(idea.thesis)
    lines.append("")
    p = d / "verdict.md"
    p.write_text("\n".join(lines) + "\n")
    return p


def _append_index_line(idea: Idea) -> None:
    """Maintain a JSONL index of all ideas for quick scanning."""
    _ensure_dirs()
    # Rewrite the entire index file from current state on every save —
    # cheap for typical registry sizes, avoids dedup issues.
    ideas = list_ideas()
    have = {i.id for i in ideas}
    if idea.id not in have:
        ideas.append(idea)
    else:
        # replace in-place
        ideas = [i if i.id != idea.id else idea for i in ideas]
    with INDEX_FILE.open("w") as fh:
        for i in ideas:
            row = {
                "id": i.id,
                "created_at": i.created_at,
                "final_verdict": i.final_verdict,
                "thesis_excerpt": i.thesis[:120].replace("\n", " "),
                "stage_verdicts": {k: v.verdict for k, v in i.stages.items()},
            }
            fh.write(json.dumps(row) + "\n")


def status_summary() -> Dict[str, int]:
    """Return aggregated counts for status reporting."""
    counts: Dict[str, int] = {"total": 0}
    for idea in list_ideas():
        counts["total"] += 1
        v = idea.final_verdict
        counts[v] = counts.get(v, 0) + 1
        for stage_name, sr in idea.stages.items():
            key = f"{stage_name}:{sr.verdict}"
            counts[key] = counts.get(key, 0) + 1
    return counts
