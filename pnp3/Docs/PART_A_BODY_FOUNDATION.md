# Part A Body foundation: first dependency-closed slice

This is **infrastructure** under `AGENTS.md`. It integrates seven fixed-machine
modules, a focused surface consumer, and direct roots in the existing central audit. It does not reduce
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, prove
`ComplexityInterfaces.NP_not_subset_PpolyDAG`, or prove `P != NP`.

## Contracts

`Body.machine` has exactly nine control states, start `q 0`, accept `q 7`,
and reject `q 8`; `q i` is `i % 9`. Its transition function takes only the
control state and the literal `Option Bool` symbol. Neither width, value,
input length nor the semantic relation is an argument of its transition
table. `Body.rawMachine` is the fixed sequential composition
`FixedRawLengthFence.prefixed.seq Body.machine`, rather than a machine
selected by parsing an input. The underlying `UniformTM.step` makes its
literal accept and reject states absorbing.

`none`, `some false`, and `some true` are distinct tape symbols. Installation
starts at a blank, consumes actual unary `some true` marks into `some false`
digits, and reaches the right blank. A false mark at seed state `q 1` takes
the default reject row. A carry crosses true digits leftwards, flips its
first false digit, and returns to the right blank; reaching the left blank
means overflow. **This work acceptance is counter overflow, never a content
verdict.** Producer work acceptance is a handoff as well. Capacity rejection
alone supplies no semantic rejection theorem.

`Body.Node`, `Edge`, and `Path` describe literal state, natural-number head,
and whole tape. An edge carries both head bounds, the actual machine row,
the destination, and the entire tape update. `Path.execute` transports an
exact-length path to the bounded `Config` run when its bound is strictly
inside the allocated tape. `Path.bounds`, `Path.append`, `hop`, `put_same`,
and `sweep` expose the corresponding bounded execution and frame contracts.

`Body.Target.Span T left bits` requires blank cells at `left` and
`left + bits.length + 1`, and digit `bits[j]!` at
`left + bits.length - j` for every in-range `j`. Exterior tape is arbitrary.
Digits are listed least significant first, with that digit physically at
the right. Leading false digits and zero width are retained.

`Body.round_exact` proves all of `Body.Target.Round`: from ready state `q 2`
at the right blank of a fitting span, the actual run after `roundClock bits`
has state `machine.accept` on overflow and `q 2` otherwise, head `left + 1`
on overflow and the original right blank otherwise, the exact incremented
span, and unchanged tape at every cell `i ≤ left` or `left + length < i`.
`inc_value` includes the overflow contribution `2^bits.length`.
`carry_frame`, `carry_reads`, `carry_path`, `round_path`, `clear_step`,
`seed_path`, and `install_path` state the full intermediate tape/path facts;
the read, length and extension lemmas remain public contracts as well.

`Body.repeated_exact` iterates the same full configuration contract under
`Good bits r` (no overflow in those rounds). `good_of_lt` derives this
premise from `value bits + r < 2^bits.length`. Exact accumulated time is
`iterClock bits r`, bounded by `r * (2 * bits.length + 3)`.
`Body.install_exact` consumes a prepared unary span in exactly `n + 2`
steps, with arbitrary exterior tape. `first_accept_whole` derives first
arrival and equality of the **whole** endpoint configuration using
absorption, rather than merely equating states.

`Body.raw_counter_parsed` assumes the concrete successful content parse,
matching tag, and `3 ≤ pr.2.n`. It identifies `pr.2.n = pr.1` and a gamma
width `z ≥ 2`. Under the separate strict capacity premise, it supplies a
producer first-arrival time `T` at most `countdownDeadline`, an installed
zero span, its exterior frame, and the actual sequential run equality for
**every** later body time `s`. `raw_repeated_parsed` specializes this to
every `r < 2^pr.2.n`, preserving ready state, head, incremented span, and
every literal serialized source cell with `8 + 2*z + 1 ≤ i < a + m` at each
reentry. Consumed gamma-header cells are outside this source preservation
claim. `raw_source_after_header` supplies the underlying literal equality;
`zero_value` supplies the zero seed's numeric value.

`AcceptedBody.exact k` proves precisely `AcceptedBody.AcceptedOrbit k`.
It starts with the **accepted guarded relation premise**
`PartAEndpoint.thresholdContentWitnessRelation k a m x w = true`. It yields
a concrete successful parse and `tableLen pr.2.n ≤ a + m`. If `3 ≤ pr.2.n`,
it additionally yields `z ≥ 2`, a matching gamma parse, strict capacity,
and a producer time `T ≤ countdownDeadline (pairLength a m)` such that, for
every `r < 2^pr.2.n`:

- `T + pr.2.n + 2 + Body.iterClock (replicate pr.2.n false) r` is at most
  `132 * (pairLength a m + 1)^2`;
- the actual raw-origin run at that time, on allocation
  `FixedRawLengthFence.allocation (pairLength a m)`, has the exact composed
  ready state, head `a + m + 2 + z + pr.2.n + 1`, the iterated span, and the
  literal source preservation just described.

`concat_eq_append`, `table_support`, `strict_capacity`, and `clock_bound`
expose each supporting contract. The table bound counts assignment rows;
it does not assert a bound on the last physically present serialized table
cell. `deadline` is a time upper bound and does not change tape allocation.

This capstone does not execute semantic reads, evaluate trees, compare a
result, handle the small-target cases, partition malformed/rejected inputs,
or prove an all-input verifier clock or semantic verifier correctness.
`Body.Target.PartA` separately records the complete `VerifiesRelation`
family obligation for the concrete threshold content relation. No witness
for that obligation is supplied here.

## Public consumers and options

`Tests.PartABodySurfaceTests` imports the capstone and independently writes
named `check_*` propositions for all 36 explicit source theorems and all
five `Edge` proof projections. The `Round` and `AcceptedOrbit` aliases are
expanded in full. Its 35 explicitly annotated expression pins cover all
remaining explicit public definitions, structures, inductive types,
source-declared constructors and data projections. These 76 names exclude
compiler-generated recursors, equation lemmas and internal proof helpers.
The focused surface introduces no private-spec API and no inferred-type or
anonymous proposition mirrors.

`Tests.AxiomsAudit` contains the 117 direct `#print axioms` commands for this
slice: all 76 source/structural names and all 41 named wrappers. Its import
block now imports `Tests.PartABodySurfaceTests`; all previous central-audit
bytes are preserved except this insertion and an explicitly marked EOF append.
The seven source modules and surface consumer are explicitly registered in
`PnP3`, alongside the already registered central audit. The initial standalone
`Tests.PartABodyAxiomsAudit` source was preserved and moved to
`/root/reports/part-a-main-integration-20261020/parent-central-audit/moved-standalone/pnp3/Tests/PartABodyAxiomsAudit.lean`;
its new registration alone was removed. Its old private build outputs are
historical stage-1 artifacts, not the current canonical audit.

The copied source contains these explicit resource options:

| Module | Option | Value |
| --- | --- | ---: |
| `Body.Proof` | `maxRecDepth` | 4000 |
| `Body.Raw` | `maxRecDepth` | 40000 |
| `Body.Raw` | `maxHeartbeats` | 2000000 |
| `AcceptedBody.Closure` | `maxRecDepth` | 12000 |

This adaptation adds no resource or linter options. The initial writer snapshot
reported no compiler run and an unchanged central audit; those were stage-1
pre-build facts, preserved unchanged in `writer-first7/SNAPSHOT_READY.json`.
The subsequent real initial Lake `--wfail` build passed for all seven exact
source modules, the surface consumer, and the then-standalone audit. All 117
printed roots used subsets of `{propext, Classical.choice, Quot.sound}`; the
parent qualification is `FIRST7_CANONICAL_STAGE1_VERIFIED.json`.
After moving the roots into `Tests.AxiomsAudit`, its fresh canonical compiler
was marked Built and emitted every expected root, using standard axioms only.
The aggregate Lake `--wfail` attempt `proc_a4f8c75f0a69` ended at
2026-10-20 09:54 UTC with exit 1: 54 warnings came from eight unchanged base
modules, not from this slice or its central-audit append. That attempt remains
a failed gate; it is not retrospectively relabeled PASS. It used the unchanged
installed lane-A wrapper and no per-module wall timeout. Its real logs,
unchanged source pins and all 117 reconciled root observations are under
`/root/reports/part-a-main-integration-20261020/parent-central-audit/`.
Release verification separately requires a fresh direct audit-consumer compile
with `-DwarningAsError=true`, the unchanged canonical `scripts/check.sh`, final
exact-head alignment and automated release checks. These require their own
completed results, not an inference from a Built marker or an existing object.
Historical
supplementary inventory used diagnostic `maxRecDepth = 10000`,
`maxHeartbeats = 0`; that inventory is not a new compiler receipt.

## Exact source provenance

The scope data is `INTEGRATION_SCOPE.v1.json`, SHA256
`fb8e9d06cbc0780b9ef80c94f31b6269fa880c727e810b38b21fdbd60e4d15af`,
against main `88b17c754e3d9792bcc865080cef806191dccc0e`.
Only its `first_capstone` entries are integrated. Each destination below
has the exact bytes of its authoritative `preferred_a2_copy`, at
`/root/reports/part-a-v1-private-foundation-copied-replay-20261019-a2/sources/`
followed by the module path with `.lean`. Each copy has a distinct inode
from both that donor and the historical original; neither was edited.

| Module | Original physical LOC | SHA256 |
| --- | ---: | --- |
| `Body.Machine` | 55 | `ee7d6ce9c9d742dc84350275f56845658e7f2a910ede30a4ba723b5a242fbde5` |
| `Body.Path` | 105 | `0eeab38a91f74d68d5f469107c37be29a5138f9647324d9afaecbdc6c5c644fc` |
| `Body.Target` | 29 | `fb18765965d5d084db2bba4a1789aa4c61344859bc187a4cef5b4acb6831604c` |
| `Body.Proof` | 316 | `d9e6329cd1d3da7fdca1f3f2d3fdabcc14e1ed6d1296ac90f1eaf3c588fd5dfe` |
| `Body.Raw` | 210 | `c01ae472c8f216276b127d8bec84b4ee2b3a48e1f5f62eebc83ee75389261c8e` |
| `AcceptedBody.Target` | 39 | `550912e0768f77bd82b968b564f05ad45ad053ac6e0b599e1565cac9af91b362` |
| `AcceptedBody.Closure` | 88 | `aaf3a2150adaf006d8f9e0859424712ee7f5616630d7a682b4ec5e8ae2b71844` |

Original `Body/*` provenance is
`/root/reports/part-a-v1-runtime-body-integration-20261016/Body/`;
original `AcceptedBody/*` provenance is
`/root/reports/part-a-v1-accepted-body-clock-closure-20261016/AcceptedBody/`.
Exact paths, byte counts, before/after hashes and file identities are in
the new `writer-first7` report package.

The adapted gross Lean delta is 1243 additions/deletions across 10 paths: 842
copied lines, 272 surface-consumer lines, 121 central-audit additions (one
import, three separator/comment lines, 117 commands), and eight lakefile
registrations. There are no deletions against the original main base. The
initial 1246-line snapshot is preserved in full, not regenerated.
Static import traversal reaches these seven new modules and 154 unchanged,
hash-matching main modules. Its remaining boundary consists of Mathlib
imports. Compilation uses the unchanged installed lane-A wrapper and a private
mount overlay over the read-only canonical dependency-cache lower directory;
the worktree build outputs and dependency upper remain private.
The initial acceptance RED/GREEN and the adaptation registration RED/GREEN are
filesystem/static checks only. Kernel evidence is recorded separately from
those tests. Neither stage-1 nor a targeted central audit is a fullgate,
release, final all-input verifier, or merge verdict.
