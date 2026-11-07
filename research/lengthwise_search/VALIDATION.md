# Local validation and supplied handoff history — 7 November 2026

## This author's actual local execution

Accepted source base: `ffba57655ac76e31f9e26304b2437139e47d4b08`.
Branch: `infrastructure/lengthwise-search-interface-20261107`.
No commit, push, PR action, merge, core edit or foundation build was performed.

- Native Linux x86_64 Lean 4.22.0-rc2, commit
  `6a60de2ac701d1a3f5dc88894b7822f17c3a980b` (Release).
- The verified installed core and dependency objects were reused read-only.
  No network, Lake build/update/cache or LD_PRELOAD shim was used. Lake emitted
  the existing Mathlib local-changes warning; no pristine/cold foundation claim.
- Fresh attempt `attempt-02`: all SIX modules compiled with
  `-DwarningAsError=true`, actual parsed import order and fresh explicit own-object
  overrides. The attempt's Lake configuration was not executed.
- The audit compared the complete imported addon declaration domain against
  exact names and required **131** direct roots: 19 authored theorem statements,
  19 full-proposition mirrors, 24 definition/structure/constructor/projection
  surfaces, 24 explicit type/arity pins and 45 compiler-generated entries.
  Generated entries include recursors, constructor support, private proof/match
  auxiliaries and one lazily generated imported `thresholdPoly.eq_1`; these are
  listed separately, not silently omitted or advertised as new authored API.
- Direct axiom output and fail-closed transitive checks allow only `propext`,
  `Classical.choice`, `Quot.sound`. Named checking declarations are roots too.
- The original production guard rejected
  `Research.LengthwiseSearch.exact_R_of_lengthwise`: actual compiler OS1 with
  `declaration must have CLOSED exact expected type`, AFTER all positives.
  Every other recorded workbench command in the final run returned OS0.
- The complete installed core source inventory matched before and after:
  `5f833d26620edc0404130be1ac445da0cb9f6a89599af1894fca94faf543c9a3`.
- Resource scope: global SH then lane-a EX, each once per job, CPU 0,1,
  two Lean threads, MALLOC_ARENA_MAX=2, no bytecode, private TMPDIR and >=5 GiB
  MemAvailable checked before/after acquiring locks.

Final actual result status: `PARTIAL_RESEARCH_INTERFACE_CHECKED_NOT_R`.
Run receipt identifier: `3d57a339-5a98-4db8-a41b-19f0ec5c6788`.
Raw source/header snapshots, setups, object pins, launches, stdout/stderr and
OS terminals are retained under the fresh attempt's
`.lake/conditional-check/runs/<id>/`. The integration report independently
pins them and enumerates full declaration sets. Private absolute paths in these
receipts are historical facts; README accepts a caller-selected fresh root.

## Retained local RED history

The missing-interface regression failed before copying. The exact donor then
failed the new surface-coverage regression. The first adapted compilation
successfully elaborated the mathematical sources and type pins, but audit
failed on unclassified generated entries and a misspelled mirror roster name.
Its full failed attempt is retained. The final roster explicitly classifies
all compiler entries and fixes that name; no proof was weakened. A source-only
exact-name regression additionally rejects equal-count substitutions,
duplicates, missing and extra roots. An initial copy precheck encountered four
empty sandbox-protection directory shapes and stopped before copying; those
read-only shapes were preserved, not removed or made writable.

## SUPPLIED donor history — not this execution or current independent review

The immutable donor's VALIDATION.md (SHA256
`13de689b4d05e0e62567910aed9abf0bd290604667cb0889a70e7d229398c0fa`)
reports another branch/environment: five modules, its then-selected 18 roots,
a 62-module project closure with cached external objects, its own static-review
claims and an LD_PRELOAD workaround for an executable-readlink restriction.
Those are supplied handoff assertions, not parent runs, this author's current
compiler receipts, or new independent approvals. The original donor and all
its files remain unchanged. Its selected-root count is historical; the current
complete count is 131. No shim or old host adaptation was introduced here.

## Not claimed

No proof of R, unconditional P≠NP, new lower bound, weaker premise, novelty,
uniform generator or executable bounded-DAG enumeration. Generic empty promise,
empty carrier and zero-width behavior remains; n=0 and n=1 are explicitly
elaborated. Direct R and other research routes are retained. The proposed
solver-to-DAG recognition/polynomial construction is separate and absent.
No new full conditional consumer, full root CI, cold core build, cross-platform
reproduction, independent source approval or release acceptance is claimed.
