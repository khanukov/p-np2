#!/usr/bin/env python3
"""
Critic report validator — Research Governance v0.1, Autoresearch MVP-0.1.1.

Parses a Critic report Markdown file (per `spec/critic_protocol.md`)
and reports its state along three orthogonal axes:

* `is_template`   — the file is the empty template at
                    `pnp3/Candidates/_template/critic_report.md`
                    (or a copy that still carries the TEMPLATE marker
                    or per-section placeholders).
* `completed`     — every required structural element is present and
                    no section is in placeholder shape.
* `verdict_status` — the parsed value of the `critic_status:` line in
                    the Verdict block (`"pass"`, `"fail"`,
                    `"TEMPLATE"`, or `null`).

Used by:

* `scripts/validate_jsonl.py::validate_attempt` — cross-field check
  that any `outputs/attempts.jsonl` line with
  `critic_status ∈ {pass, fail}` cites a `critic_report_path` that
  resolves to a real file whose `is_template=false` and
  `completed=true`.
* `scripts/verify_candidate.sh` — surfaces `critic_report_present`,
  `critic_report_is_template`, `critic_completed`, `critic_status`
  in `result.json`.
* manual smoke at `scripts/test_attempts_validator.sh`.

Exit codes (when invoked as a CLI):
  0   the file parses; print a JSON summary to stdout
  1   the file is missing or unreadable
  2   the file parses but is in template / incomplete state (and
      `--require-completed` was passed)

Stdlib-only.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Markers and per-section schema.
# ---------------------------------------------------------------------------

# Any of these strings, present anywhere in the file, marks the report
# as a TEMPLATE clone (regardless of other content).  Adding a new
# marker here AUTOMATICALLY hardens detection — keep this list synced
# with `pnp3/Candidates/_template/critic_report.md`.
TEMPLATE_MARKERS = (
    "TEMPLATE FILE",
    "Template placeholder",
    "Template caveat",
    "TEMPLATE marker",
    "Template — fill",
    "Template note.",
    "DO NOT USE AS A REAL CRITIC OUTPUT",
)

# These strings appear in the empty template's per-section evidence
# blocks; their presence is a strong template signal but not by itself
# decisive (a real report could legitimately mention "Template" in a
# justification).  We require strictly more than just one of these to
# flag the file.
SOFT_TEMPLATE_MARKERS = (
    "Template.",
)

ATTACK_HEADER_RE = re.compile(
    r"^##\s+Attack\s+([1-6])\s*:\s*(.+?)\s*$",
    flags=re.MULTILINE,
)

VERDICT_HEADER_RE = re.compile(r"^##\s+Verdict\s*$", flags=re.MULTILINE)

# Inside an attack section we look for the three required fields.
STATUS_RE = re.compile(
    r"^\s*-\s*\*\*status:\*\*\s*`?([^`\n]+?)`?\s*$",
    flags=re.MULTILINE,
)
SUMMARY_RE = re.compile(
    r"^\s*-\s*\*\*summary:\*\*\s*(.+?)$",
    flags=re.MULTILINE,
)
EVIDENCE_HEADER_RE = re.compile(
    r"^\s*-\s*\*\*evidence:\*\*\s*$",
    flags=re.MULTILINE,
)

# Verdict-block field parsers.
CRITIC_STATUS_RE = re.compile(
    r"^\s*-\s*\*\*critic_status:\*\*\s*`?([^`\n]+?)`?\s*$",
    flags=re.MULTILINE,
)
DOMINANT_BREAK_CLASS_RE = re.compile(
    r"^\s*-\s*\*\*dominant_break_class:\*\*\s*`?([^`\n]+?)`?\s*$",
    flags=re.MULTILINE,
)
DOMINANT_BREAK_SECTION_RE = re.compile(
    r"^\s*-\s*\*\*dominant_break_section:\*\*\s*`?([^`\n]+?)`?\s*$",
    flags=re.MULTILINE,
)

# Allowed status values per section, per spec/critic_protocol.md §2.
ALLOWED_SECTION_STATUSES = (
    "no break found",
    "break found",
    "attack not applicable",
)

# Allowed verdict critic_status values; "TEMPLATE" is a synthetic
# value used by the empty template only and never appears in a real
# Critic report.
ALLOWED_VERDICT_STATUSES = ("pass", "fail")
TEMPLATE_VERDICT_STATUS = "TEMPLATE"

# ---------------------------------------------------------------------------
# Result type.
# ---------------------------------------------------------------------------


@dataclass
class CriticReportState:
    """Result of parsing a Critic report Markdown file."""
    path: str
    exists: bool = False
    parse_error: str | None = None

    # Structural state.
    sections_found: list[int] = field(default_factory=list)
    all_six_sections: bool = False
    verdict_block_present: bool = False

    # Template signals.
    has_template_banner: bool = False         # any TEMPLATE_MARKERS hit
    is_template: bool = False                 # final template flag

    # Per-section status values (1..6 → status string, or None if missing).
    section_statuses: dict[int, str | None] = field(default_factory=dict)

    # Heuristic: every present section is `attack not applicable`.
    all_sections_attack_not_applicable: bool = False

    # Verdict fields.
    verdict_critic_status: str | None = None
    verdict_dominant_break_class: str | None = None
    verdict_dominant_break_section: str | None = None

    # Final completeness verdict (true only if no template signals,
    # all six sections present with allowed status values, verdict
    # block present, verdict critic_status ∈ {pass, fail}).
    completed: bool = False

    # Errors accumulated during validation.
    errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "path": self.path,
            "exists": self.exists,
            "parse_error": self.parse_error,
            "sections_found": self.sections_found,
            "all_six_sections": self.all_six_sections,
            "verdict_block_present": self.verdict_block_present,
            "has_template_banner": self.has_template_banner,
            "is_template": self.is_template,
            "section_statuses": {
                str(k): v for k, v in self.section_statuses.items()
            },
            "all_sections_attack_not_applicable":
                self.all_sections_attack_not_applicable,
            "verdict_critic_status": self.verdict_critic_status,
            "verdict_dominant_break_class": self.verdict_dominant_break_class,
            "verdict_dominant_break_section":
                self.verdict_dominant_break_section,
            "completed": self.completed,
            "errors": self.errors,
        }


# ---------------------------------------------------------------------------
# Parsing.
# ---------------------------------------------------------------------------


def _split_attack_sections(text: str) -> dict[int, str]:
    """Extract each attack section's body keyed by section number.

    The section body is the substring between this section's header
    and the next attack header (or the Verdict header, or EOF).
    """
    headers: list[tuple[int, str, int]] = []
    for m in ATTACK_HEADER_RE.finditer(text):
        try:
            num = int(m.group(1))
        except ValueError:
            continue
        headers.append((num, m.group(2), m.start()))
    verdict_match = VERDICT_HEADER_RE.search(text)
    verdict_pos = verdict_match.start() if verdict_match else len(text)

    sections: dict[int, str] = {}
    for i, (num, _name, start) in enumerate(headers):
        if i + 1 < len(headers):
            end = headers[i + 1][2]
        else:
            end = verdict_pos
        sections[num] = text[start:end]
    return sections


def _verdict_block(text: str) -> str:
    """Extract the body of the Verdict section (everything from the
    Verdict header to EOF).  Empty string if not present."""
    m = VERDICT_HEADER_RE.search(text)
    if not m:
        return ""
    return text[m.start():]


def parse_critic_report(text: str, path: str = "") -> CriticReportState:
    """Parse a Critic report's Markdown source and return state."""
    s = CriticReportState(path=path, exists=True)

    # Template-marker scan.
    s.has_template_banner = any(m in text for m in TEMPLATE_MARKERS)

    # Section breakdown.
    sections = _split_attack_sections(text)
    s.sections_found = sorted(sections.keys())
    s.all_six_sections = (s.sections_found == [1, 2, 3, 4, 5, 6])

    # Per-section status.
    for num in (1, 2, 3, 4, 5, 6):
        body = sections.get(num)
        if not body:
            s.section_statuses[num] = None
            continue
        m = STATUS_RE.search(body)
        if not m:
            s.section_statuses[num] = None
        else:
            val = m.group(1).strip()
            s.section_statuses[num] = val

    present_statuses = [v for v in s.section_statuses.values() if v]
    s.all_sections_attack_not_applicable = bool(
        present_statuses
        and all(v == "attack not applicable" for v in present_statuses)
    )

    # Verdict.
    vbody = _verdict_block(text)
    s.verdict_block_present = bool(vbody)
    if vbody:
        m = CRITIC_STATUS_RE.search(vbody)
        if m:
            s.verdict_critic_status = m.group(1).strip()
        m = DOMINANT_BREAK_CLASS_RE.search(vbody)
        if m:
            s.verdict_dominant_break_class = m.group(1).strip()
        m = DOMINANT_BREAK_SECTION_RE.search(vbody)
        if m:
            s.verdict_dominant_break_section = m.group(1).strip()

    # Final flags.
    is_template_signals = (
        s.has_template_banner
        or s.verdict_critic_status == TEMPLATE_VERDICT_STATUS
        # Heuristic: every section defaulting to `attack not applicable`
        # AND the file containing soft template markers in evidence
        # blocks is also template.
        or (s.all_sections_attack_not_applicable
            and any(soft in text for soft in SOFT_TEMPLATE_MARKERS))
    )
    s.is_template = bool(is_template_signals)

    # Errors / completeness.
    if not s.all_six_sections:
        missing = [n for n in (1, 2, 3, 4, 5, 6) if n not in sections]
        s.errors.append(
            f"missing attack sections: {missing}"
        )
    for num in (1, 2, 3, 4, 5, 6):
        st = s.section_statuses.get(num)
        if st is None:
            s.errors.append(f"section {num}: missing 'status' field")
        elif st not in ALLOWED_SECTION_STATUSES \
                and not s.is_template:
            s.errors.append(
                f"section {num}: status {st!r} not in "
                f"{ALLOWED_SECTION_STATUSES}"
            )

    if not s.verdict_block_present:
        s.errors.append("Verdict section missing")
    elif s.verdict_critic_status is None:
        s.errors.append("Verdict: 'critic_status' missing")
    elif s.verdict_critic_status not in ALLOWED_VERDICT_STATUSES \
            and s.verdict_critic_status != TEMPLATE_VERDICT_STATUS:
        s.errors.append(
            f"Verdict: critic_status {s.verdict_critic_status!r} not in "
            f"{ALLOWED_VERDICT_STATUSES} (or '{TEMPLATE_VERDICT_STATUS}')"
        )

    # Completed iff: no errors above, not a template, verdict status is
    # one of the real verdict values.
    s.completed = (
        not s.is_template
        and not s.errors
        and s.verdict_critic_status in ALLOWED_VERDICT_STATUSES
    )

    return s


def validate_critic_report_file(path: Path) -> CriticReportState:
    """Read `path` and return the parsed Critic report state."""
    s = CriticReportState(path=str(path))
    if not path.exists():
        s.exists = False
        s.parse_error = f"file not found: {path}"
        return s
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as e:
        s.exists = False
        s.parse_error = f"unreadable: {e}"
        return s
    parsed = parse_critic_report(text, path=str(path))
    return parsed


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------


def _print_help() -> None:
    print(
        "usage: scripts/validate_critic_report.py [--require-completed] "
        "<path-to-critic_report.md>",
        file=sys.stderr,
    )


def main(argv: list[str]) -> int:
    require_completed = False
    args = []
    for a in argv[1:]:
        if a in ("-h", "--help"):
            _print_help()
            return 0
        if a == "--require-completed":
            require_completed = True
            continue
        args.append(a)
    if len(args) != 1:
        _print_help()
        return 1
    path = Path(args[0])
    state = validate_critic_report_file(path)
    summary = json.dumps(state.to_dict(), ensure_ascii=False, indent=2,
                         sort_keys=True)
    print(summary)
    if not state.exists:
        return 1
    if require_completed and not state.completed:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
