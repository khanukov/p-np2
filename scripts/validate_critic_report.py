#!/usr/bin/env python3
"""
Critic-report parser/validator — Research Governance v0.1, Autoresearch
MVP-0.1.1 (Critic state hardening).

Reads `pnp3/Candidates/<id>/critic_report.md` (or
`seed_packs/<id>/critic_report.md`) and answers four questions:

  1. is_template       — does the file still carry template markers
                         (`<!-- TEMPLATE_MARKER ... -->` HTML comment, or
                         every section's summary still containing the
                         literal "Template placeholder" string)?
  2. is_well_formed    — does the file contain six attack sections in
                         the fixed order required by
                         `spec/critic_protocol.md` §1, plus a Verdict
                         section?
  3. is_completed      — `is_well_formed AND NOT is_template AND every
                         attack section has a non-empty, non-template
                         evidence body`?
  4. critic_status     — what verdict does the file claim?  Parsed from
                         the `## Verdict` block; one of
                         {"pass", "fail", "not_run", "unknown"}.
                         "not_run" is the canonical sentinel for a
                         template / unfilled report; "unknown" means
                         the verdict line is malformed.

Output is a single-line JSON object on stdout with these fields plus
`errors` (list of strings).  Exit code is 0 iff the file is at least
syntactically parseable (six sections + Verdict block); 1 otherwise.
A template that is well-formed but unfilled is still exit 0 — it is
"valid as a template", just not "completed".

Usage:

  scripts/validate_critic_report.py <path>

The script is stdlib-only.  It is intentionally grep/regex-based; a
proper Markdown parser is overkill for the MVP.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

# spec/critic_protocol.md §1 — six attack sections in fixed order.
ATTACK_TITLES = (
    "Hidden-payload attack",
    "Hardwiring attack",
    "KnownGuards-factorization attack",
    "Natural-proof / relativization / algebrization barrier audit",
    "Collapse-not-contradiction audit",
    "Vacuity / source-theorem rephrasing audit",
)

# Acceptable Critic-status enum values, mirrored from
# `spec/nogolog_schema.json::AttemptLedgerEntry.critic_status`.
CRITIC_STATUS_ENUM = {"pass", "fail", "not_run"}

# Acceptable per-section status values, from spec/critic_protocol.md §2.
ATTACK_STATUS_ENUM = {"no break found", "break found", "attack not applicable"}

# Markers that classify the report as still being a template.  Any
# of these triggers `is_template = true`.
TEMPLATE_MARKER_RE = re.compile(
    r"<!--\s*TEMPLATE_MARKER\s*:\s*do-not-treat-as-completed\s*-->",
    re.IGNORECASE,
)
TEMPLATE_PLACEHOLDER_PHRASES = (
    "Template placeholder",
    "TEMPLATE marker",
    "Template caveat",
)

# Sentinel string the Critic must *remove* from each attack section
# evidence block to claim a real verdict.
EVIDENCE_TEMPLATE_SENTINELS = (
    "Template — fill",
    "Template.",
)

ATTACK_HEADER_RE = re.compile(
    r"^##\s+Attack\s+(?P<num>[1-6])\s*:\s*(?P<title>.+?)\s*$",
)
VERDICT_HEADER_RE = re.compile(r"^##\s+Verdict\s*$")
STATUS_LINE_RE = re.compile(
    r"^\s*-\s*\*\*status:\*\*\s*`(?P<status>[^`]*)`\s*$",
)
SUMMARY_LINE_RE = re.compile(
    r"^\s*-\s*\*\*summary:\*\*\s*(?P<summary>.+?)\s*$",
)
EVIDENCE_LINE_RE = re.compile(r"^\s*-\s*\*\*evidence:\*\*\s*$")
CRITIC_STATUS_LINE_RE = re.compile(
    r"^\s*-\s*\*\*critic_status:\*\*\s*`(?P<value>[^`]*)`\s*$",
)
DOMINANT_BREAK_CLASS_RE = re.compile(
    r"^\s*-\s*\*\*dominant_break_class:\*\*\s*`(?P<value>[^`]*)`\s*$",
)
DOMINANT_BREAK_SECTION_RE = re.compile(
    r"^\s*-\s*\*\*dominant_break_section:\*\*\s*`(?P<value>[^`]*)`\s*$",
)


def _strip_inline_md(s: str) -> str:
    """Strip leading/trailing whitespace and surrounding backticks/quotes
    so that "`pass`" and "pass" parse identically."""
    s = s.strip()
    if s.startswith("`") and s.endswith("`"):
        s = s[1:-1].strip()
    return s


def _section_evidence_is_template(evidence_lines: list[str]) -> bool:
    """A section's evidence is template iff every non-blank evidence
    bullet starts with a template sentinel."""
    cleaned = [ln.strip() for ln in evidence_lines if ln.strip()]
    if not cleaned:
        return True
    for ln in cleaned:
        # Strip leading "- " bullet prefix, leading spaces.
        body = re.sub(r"^[-*]\s*", "", ln).strip()
        if not body:
            continue
        if not any(body.startswith(s) or body == s.rstrip(".")
                   for s in EVIDENCE_TEMPLATE_SENTINELS):
            return False
    return True


def parse_report(text: str) -> dict[str, Any]:
    """Parse a Critic report.  Returns a structured dict; never raises.

    Top-level keys:
        is_well_formed: bool
        is_template:    bool
        is_completed:   bool
        critic_status:  "pass" | "fail" | "not_run" | "unknown"
        dominant_break_class:  string or None
        dominant_break_section: int or None
        sections:       list of {num, title, status, summary, evidence_template}
        errors:         list[str]
    """
    errors: list[str] = []
    has_marker = bool(TEMPLATE_MARKER_RE.search(text))

    # Split into per-section blocks by the "## Attack N:" / "## Verdict"
    # headers.  We keep raw line offsets for evidence parsing.
    lines = text.splitlines()

    sections: list[dict[str, Any]] = []
    verdict_block_lines: list[str] = []
    current: dict[str, Any] | None = None
    in_verdict = False
    in_evidence = False
    for ln in lines:
        atk = ATTACK_HEADER_RE.match(ln)
        vrd = VERDICT_HEADER_RE.match(ln)
        if atk:
            if current is not None:
                sections.append(current)
            current = {
                "num": int(atk.group("num")),
                "title": atk.group("title").strip(),
                "status": None,
                "summary": None,
                "evidence_lines": [],
            }
            in_verdict = False
            in_evidence = False
            continue
        if vrd:
            if current is not None:
                sections.append(current)
                current = None
            in_verdict = True
            in_evidence = False
            continue
        if in_verdict:
            verdict_block_lines.append(ln)
            continue
        if current is None:
            continue
        if in_evidence:
            # An evidence block ends when we hit a blank line followed
            # by a non-indented non-bullet, OR the next section header.
            # The simpler rule: every line that starts with whitespace
            # then `-` or `*` belongs to evidence; blank lines pass
            # through; non-blank non-indented lines end the block.
            if ln.strip() == "":
                current["evidence_lines"].append(ln)
                continue
            stripped = ln.lstrip()
            if stripped.startswith("-") or stripped.startswith("*") \
                    or ln.startswith("    ") or ln.startswith("\t"):
                current["evidence_lines"].append(ln)
                continue
            in_evidence = False
            # fallthrough to status/summary detection
        m = STATUS_LINE_RE.match(ln)
        if m:
            current["status"] = _strip_inline_md(m.group("status"))
            continue
        m = SUMMARY_LINE_RE.match(ln)
        if m:
            current["summary"] = m.group("summary").strip()
            continue
        if EVIDENCE_LINE_RE.match(ln):
            in_evidence = True
            continue

    if current is not None:
        sections.append(current)

    # Structural checks.
    is_well_formed = True
    if len(sections) != 6:
        errors.append(
            f"expected 6 attack sections, found {len(sections)}")
        is_well_formed = False
    for i, sec in enumerate(sections):
        if i + 1 != sec["num"]:
            errors.append(
                f"attack section #{i + 1} has wrong header number "
                f"{sec['num']!r}")
            is_well_formed = False
        if i < len(ATTACK_TITLES) and ATTACK_TITLES[i] not in sec["title"]:
            errors.append(
                f"attack section {sec['num']} title {sec['title']!r} "
                f"does not match expected {ATTACK_TITLES[i]!r}")
            is_well_formed = False
        if sec["status"] is None:
            errors.append(
                f"attack section {sec['num']} is missing the "
                f"`status` field")
            is_well_formed = False
        elif sec["status"] not in ATTACK_STATUS_ENUM:
            errors.append(
                f"attack section {sec['num']} status {sec['status']!r} "
                f"not in enum {sorted(ATTACK_STATUS_ENUM)}")
            is_well_formed = False
        if sec["summary"] is None:
            errors.append(
                f"attack section {sec['num']} is missing the "
                f"`summary` field")
            is_well_formed = False

    # Verdict-block parsing.
    critic_status = "unknown"
    dominant_break_class: str | None = None
    dominant_break_section: int | None = None
    saw_verdict_critic_status = False
    for ln in verdict_block_lines:
        m = CRITIC_STATUS_LINE_RE.match(ln)
        if m:
            saw_verdict_critic_status = True
            value = _strip_inline_md(m.group("value"))
            if value in CRITIC_STATUS_ENUM:
                critic_status = value
            else:
                # Sentinel values like "template_not_filled" mean
                # not_run; everything else means malformed.
                if value.lower() in {
                        "template_not_filled", "template-not-filled",
                        "template", "null", "n/a", ""}:
                    critic_status = "not_run"
                else:
                    critic_status = "unknown"
                    errors.append(
                        f"verdict critic_status {value!r} "
                        f"not in enum {sorted(CRITIC_STATUS_ENUM)}")
            continue
        m = DOMINANT_BREAK_CLASS_RE.match(ln)
        if m:
            v = _strip_inline_md(m.group("value"))
            dominant_break_class = None if v in {"null", "", "n/a"} else v
            continue
        m = DOMINANT_BREAK_SECTION_RE.match(ln)
        if m:
            v = _strip_inline_md(m.group("value"))
            if v in {"null", "", "n/a"}:
                dominant_break_section = None
            else:
                try:
                    dominant_break_section = int(v)
                except ValueError:
                    dominant_break_section = None
                    errors.append(
                        f"verdict dominant_break_section {v!r} "
                        f"is not an integer")
            continue
    if not saw_verdict_critic_status:
        errors.append("Verdict block is missing the critic_status line")
        is_well_formed = False

    # Template detection.  Multiple independent signals:
    is_template = False
    if has_marker:
        is_template = True
    if any(p in text for p in TEMPLATE_PLACEHOLDER_PHRASES):
        # The Template caveat itself is informational; presence of any
        # of the placeholder phrases above (Template placeholder /
        # TEMPLATE marker) anywhere in the file marks it as template.
        is_template = True
    # Section-level evidence sentinel sweep.
    if not is_template and sections:
        all_sections_template_evidence = all(
            _section_evidence_is_template(s.get("evidence_lines", []))
            for s in sections
        )
        if all_sections_template_evidence:
            is_template = True

    # Cross-field verdict consistency.
    is_completed = (
        is_well_formed
        and not is_template
        and critic_status in {"pass", "fail"}
    )
    if critic_status == "fail":
        if dominant_break_class is None:
            errors.append(
                "critic_status=fail requires "
                "dominant_break_class != null")
            is_completed = False
        if dominant_break_section is None:
            errors.append(
                "critic_status=fail requires "
                "dominant_break_section in 1..6")
            is_completed = False
    if critic_status == "pass":
        # Per spec/critic_protocol.md §3: pass requires every section's
        # status ∈ {no break found, attack not applicable}.
        for sec in sections:
            if sec.get("status") == "break found":
                errors.append(
                    f"critic_status=pass contradicts "
                    f"section {sec['num']} status 'break found'")
                is_completed = False

    return {
        "is_well_formed": is_well_formed,
        "is_template": is_template,
        "is_completed": is_completed,
        "critic_status": critic_status,
        "dominant_break_class": dominant_break_class,
        "dominant_break_section": dominant_break_section,
        "sections": [
            {"num": s["num"],
             "title": s["title"],
             "status": s["status"],
             "summary": s["summary"]}
            for s in sections
        ],
        "errors": errors,
    }


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: validate_critic_report.py <path>", file=sys.stderr)
        return 2
    path = Path(argv[1])
    if not path.exists():
        out = {
            "is_well_formed": False,
            "is_template": False,
            "is_completed": False,
            "critic_status": "not_run",
            "dominant_break_class": None,
            "dominant_break_section": None,
            "sections": [],
            "errors": [f"file not found: {path}"],
        }
        print(json.dumps(out, sort_keys=True))
        return 1
    text = path.read_text(encoding="utf-8")
    out = parse_report(text)
    print(json.dumps(out, sort_keys=True))
    return 0 if out["is_well_formed"] else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
