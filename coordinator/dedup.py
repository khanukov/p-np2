"""Content-addressed candidate dedup — Research Governance v0.1, MVP-0.2.

Content-hash policy:
  * For a `gen-*` worker, the hash inputs are
      seed_pack_id +
      sketch.md content +
      manifest.toml content +
      candidate's proof.lean SourceTheorem-statement bytes.
  * For a `crit-*` worker, the hash inputs are
      attempt_id (i.e. the AttemptLedgerEntry being criticised) +
      critic_report.md content (after stripping TEMPLATE markers).

Both shapes hash to a hex sha256 string used as the primary key in
the dedup table.  Two workers that independently propose
identical-content candidates collide and the second receives
`409 Conflict` with `first_assignment_id` from the first.

Phase B intentionally keeps the hashing simple (sha256 over
concatenated bytes with explicit separators).  Phase D will
specialise per-role.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

# Field separator in the hash input.  The choice is arbitrary but
# stable: changing it bumps every cached hash.
_SEPARATOR = b"\x1e"  # ASCII record separator


def hash_gen_candidate(
    seed_pack_id: str,
    sketch_md: str | bytes,
    manifest_toml: str | bytes,
    proof_source: str | bytes,
) -> str:
    """Compute the dedup hash for a Generator-side candidate."""
    h = hashlib.sha256()
    h.update(b"gen")
    h.update(_SEPARATOR)
    h.update(seed_pack_id.encode("utf-8"))
    h.update(_SEPARATOR)
    h.update(_as_bytes(sketch_md))
    h.update(_SEPARATOR)
    h.update(_as_bytes(manifest_toml))
    h.update(_SEPARATOR)
    h.update(_as_bytes(proof_source))
    return h.hexdigest()


def hash_critic_report(
    attempt_id: str,
    critic_report_md: str | bytes,
) -> str:
    """Compute the dedup hash for a Critic-side report.

    The TEMPLATE markers documented in
    `pnp3/Candidates/_template/critic_report.md` are stripped before
    hashing so a never-filled template never produces a non-trivial
    hash collision with a real report.
    """
    text = _as_bytes(critic_report_md)
    text = _strip_template_markers(text)
    h = hashlib.sha256()
    h.update(b"crit")
    h.update(_SEPARATOR)
    h.update(attempt_id.encode("utf-8"))
    h.update(_SEPARATOR)
    h.update(text)
    return h.hexdigest()


def hash_file(path: Path) -> str:
    """Helper: sha256 of the bytes at `path`."""
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Helpers.
# ---------------------------------------------------------------------------


_TEMPLATE_MARKERS_BYTES = (
    b"TEMPLATE FILE",
    b"Template placeholder",
    b"Template caveat",
    b"TEMPLATE marker",
    b"Template - fill",
    b"Template \xe2\x80\x94 fill",  # UTF-8 em-dash variant
    b"Template note.",
    b"DO NOT USE AS A REAL CRITIC OUTPUT",
    b"critic_status:** `TEMPLATE`",
)


def _strip_template_markers(text: bytes) -> bytes:
    """Replace any line containing a TEMPLATE marker with an empty
    line.  Used by `hash_critic_report` so that template-only files
    hash trivially.
    """
    out = []
    for line in text.splitlines():
        if any(m in line for m in _TEMPLATE_MARKERS_BYTES):
            out.append(b"")
        else:
            out.append(line)
    return b"\n".join(out)


def _as_bytes(value: str | bytes) -> bytes:
    if isinstance(value, bytes):
        return value
    return value.encode("utf-8")
