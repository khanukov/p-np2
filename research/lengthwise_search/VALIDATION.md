# Local validation and supplied handoff history — 7 November 2026

## Initial source-01 execution — historical checkpoint

Accepted source base: `ffba57655ac76e31f9e26304b2437139e47d4b08`.
Branch: `infrastructure/lengthwise-search-interface-20261107`.
At that source-only checkpoint no commit, push, PR action, merge, core edit or
foundation build was performed. Later publication/review status is separate.

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
The source-01 execution did not run a new full conditional consumer, root CI or
cross-platform replay, and supplied no independent opinion or release acceptance.
No cold core build is claimed.

## Subsequent preceding-head evidence and current verification record

The parent authenticated both completed scoped source and dedicated-docs/effects
APPROVE opinions for preceding head
`bd302d42874454f3486183f136fb0bf04b7b2684`. Those opinions remain at those bytes;
they do not review the later copy-fidelity/owned-module repair. The source-a
procedural metadata overrun and all earlier failed attempts remain recorded.

On 7 November 2026, hosted `./scripts/check.sh` succeeded on that exact head:
[run 42416247912, job 128534861275](https://github.com/khanukov/p-np2/actions/runs/42416247912/job/128534861275),
all 17 main stages and final pass observed. This is actual preceding-head root-CI
evidence, not an author rerun, not compilation of the optional Attempt tree and
not acceptance of future bytes. The separate addon prepare/check execution
covers that tree. See the [PR1824 verification record](https://github.com/khanukov/p-np2/pull/1824)
for the latest published-head review and CI scope; these historical paragraphs
are not an assertion that those gates are perpetually pending or passed.

## Source-02 bounded repair — local execution, 7 November 2026

The copy-fidelity regression first failed on the unchanged preceding prepare
implementation: a corrupted real copy returned normally. Preparation now takes
source names/bytes/hashes before copying and verifies the full copied output
against those rows plus the acquired workbench scaffold before writing its
manifest. Seven finite DATA tests pass: normal bytes, corrupt bytes, missing
file, extra Lean file, extra non-Lean file, existing directory and existing
symlink. Only workbench acquisition is stubbed in those tests; copying is real.
The initial post-fix normal-copy test exposed an ordering mismatch; that failed
run is retained, and the subsequent runs pass without weakening the comparison.

A private negative fixture imports `Attempt.Unclassified` with declaration
`UnclassifiedData.sentinel`. The old audit accepted it, so the regression failed.
The hardened audit discovers all imported owners under Lean's `Attempt` name
prefix, including declarations outside the API namespace, and rejects this
fixture at `unexpected lengthwise declaration UnclassifiedData.sentinel`.
This closes a future-module gap; it does not invalidate the old current-131 audit.

Fresh published prepare/check commands then returned OS0/OS0 on the unchanged
read-only installed core, with fresh own import overrides and warning-as-error.
All six current Lean modules compiled (850 physical lines); the complete
131-name declaration/root set, mirrors, type pins and allowed axiom sets remain
unchanged. Run `d891b74b-e579-4d76-9c4b-1c4bf9711927` recorded 14 OS0 workbench
commands and the expected final production-guard OS1:
`declaration must have CLOSED exact expected type`. No final-R result or assembly
was produced. The addon now has 12 source/tool/doc/test files.

Core/dependency objects were reused, not rebuilt cold; the existing Mathlib
local-changes warning is retained. Compilation used the same pinned native
Linux Lean, global-SH/lane-a-EX order, CPU 0,1 and checked 5 GiB floor as above.
The source-02 report retains exact argv, waits, source/SDK pins and fault fixtures.
This local repair is not its own independent review, new-head root CI, other-platform
reproduction, proof of R or release approval; the current PR record supplies the
scope of subsequent independent checks.
