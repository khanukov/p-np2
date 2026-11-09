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

    primary = current_context()
    if max_chars < len(primary):
        raise ValueError('context bound cannot contain all primary routes')
    # Whole optional lines only; the primary declarations are never truncated.
    out = primary
    for line in ['\n### Optional historical route context'] + sections:
        if len(out) + len(line) + 1 > max_chars:
            break
        out += '\n' + line
    return out


def current_context() -> str:
    """Read literal primary definitions, with separate import roots for addons."""
    specs = [
        ('ConditionalSeparation.OpenProblem.R',
         'conditional_separation/ConditionalSeparation/OpenProblem.lean',
         'def R : Prop :=', '\n#check'),
        ('Research.LengthwiseSearch.LengthwiseR',
         'research/lengthwise_search/Attempt/RNormalForm.lean',
         'def LengthwiseAt', '\ntheorem lengthwiseAt_iff'),
        ('Research.SolverToDag.LowerBound.TreeMCSPDAGLowerBound',
         'research/solver_to_dag/Attempt/LowerBound.lean',
         'def FixedKTreeMCSPDAGExclusion', '\ntheorem fixedK_excludes_solver'),
    ]
    lines = ['### Current conditional research premises (Infrastructure)']
    for name, relative, start, end in specs:
        text = (REPO_ROOT / relative).read_text()
        body = text[text.index(start):text.index(end)].strip()
        lines += [f'`{name}` — `{relative}`', '```lean', body, '```']
    lines += [
        'R <-> LengthwiseR: Research.LengthwiseSearch.R_iff_lengthwise in RNormalForm.lean.',
        'TreeMCSPDAGLowerBound -> R ONLY: Research.SolverToDag.LowerBound.lowerBound_implies_R.',
        'R and the lower bound remain unproved. One k precedes every degree; '
        'N=2^n, per-output solver size, promise correctness, TREE witnesses versus DAG solvers.',
        'Separate addon Attempt module roots cannot be combined in one import map. '
        'Legacy routes are optional context, not a mandatory method.',
    ]
    return '\n'.join(lines)


if __name__ == "__main__":
    print(live_routes_excerpt())
