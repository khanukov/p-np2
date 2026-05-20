"""Scan pnp3 / pnp4 for live route definitions and barrier surfaces.

Returns a markdown excerpt suitable for embedding into the Stage 3
prompt.  Output is bounded so that it fits within the LLM context.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
PNP3_MAINLINE = REPO_ROOT / "pnp3" / "Magnification" / "FinalResultMainline.lean"
PNP4_FRONTIER = REPO_ROOT / "pnp4" / "Pnp4" / "Frontier"
PNP4_ALGS = REPO_ROOT / "pnp4" / "Pnp4" / "AlgorithmsToLowerBounds"


_ROUTE_PATTERN = re.compile(r"^def\s+(\w*Route\w*)\s", re.MULTILINE)
_STRUCT_PATTERN = re.compile(r"^structure\s+(\w+)\s", re.MULTILINE)


def _extract_def_lines(path: Path) -> list[str]:
    if not path.exists():
        return []
    txt = path.read_text(errors="ignore")
    routes = _ROUTE_PATTERN.findall(txt)
    structs = _STRUCT_PATTERN.findall(txt)
    rel = path.relative_to(REPO_ROOT)
    lines: list[str] = []
    for name in routes:
        lines.append(f"- `{name}` (def, {rel})")
    for name in structs:
        # Limit struct list to the interesting frontier objects, not
        # every supporting structure.
        if any(
            keyword in name
            for keyword in (
                "Route",
                "Source",
                "WeakLowerBound",
                "MagnificationContract",
                "Compression",
                "VerifiedNPDAG",
            )
        ):
            lines.append(f"- `{name}` (structure, {rel})")
    return lines


def live_routes_excerpt(*, max_chars: int = 4000) -> str:
    """Return a markdown excerpt of live route surfaces."""
    sections: list[str] = []
    sections.append("### pnp3 mainline routes (`FinalResultMainline.lean`)")
    sections.extend(_extract_def_lines(PNP3_MAINLINE))

    sections.append("")
    sections.append("### pnp4 frontier surfaces")
    if PNP4_FRONTIER.exists():
        for p in sorted(PNP4_FRONTIER.glob("*.lean")):
            sections.extend(_extract_def_lines(p))
    if PNP4_ALGS.exists():
        for p in sorted(PNP4_ALGS.rglob("*.lean")):
            sections.extend(_extract_def_lines(p))

    out = "\n".join(sections)
    if len(out) > max_chars:
        out = out[:max_chars] + "\n\n(... excerpt truncated ...)"
    return out


if __name__ == "__main__":
    print(live_routes_excerpt())
