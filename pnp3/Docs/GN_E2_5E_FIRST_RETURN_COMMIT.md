# GN-E2-5e: canonical first-return commit

Classification: **Infrastructure**. This change reduces neither pnp4 source
obligation. The original historical base is
`067b9ff6253dfa746dfe34e591d2739344593eb9`; after three `origin/main` integration
merges the release scope is measured at the integration head
`beba9d1b669323e1dd01ae65a853afb1af090537` against its `origin/main` parent
`5deb0abda65479a529111e66fa97bcb409661118` (see
[Ordered content-addressed migration](#ordered-content-addressed-migration)).
Only `GateNFixedDelegateRelocation.lean` changes inside the frozen subtree.

The finite control latches the intercepted Boolean, seeks the unique cursor
backward, seeks the opening bof, writes the first slot as `data res`, marks the
first record spent, and probes the following frame. A bof becomes the next
cursor, with head returned to its first cell. A terminal separator routes to
an actual write of `output res` in the GN final-output frame.

With `N = (encodeGN r).length`, `n = r.inputs.length`,
`m = r.program.gates.length`, `L = gnRecordSize (gnGateFields g)`, and
`B = 4*(gnRecordsStart r + L)`, the endpoint is:

- steps: `N + 8*(L+n) + 4*m + 39`;
- state/head: `firstCommitTerminal`/`B+8` when `m=1`, otherwise
  `firstCommitNext`/`B`;
- complete tape: the bits of `encodeGNAtFrames r [res]` followed by the
  completed `g1OutputFrames (gnFirstRequest r g) res`, with false padding.

`gnCS_firstReturned_commit_exact` executes genuine `TM.runConfig` from the
explicit relocated/intercepted `gnFirstReturnedConfig`. Its explicit parameters
are `(hg : r.program.gates[0]? = some g)` and `(res : Bool)`. The initial-run
composition `gnCS_encodeGN_firstCommit_exact` additionally requires exactly
`(gnFirstRequest r g).spec = some res`. Neither theorem assumes an execution
contract, global well-formedness, room, or second-gate success.

The kernel proves reverse scans from concrete machine rows, a four-read
forward probe that permits a stationary fourth read, three leftward rewind
steps, and the existing four-cell rightward writer instantiated on GNM.
The branch macrostep costs 15 in both cases. No dispatch row or reposition
step is hidden. The generic composition preserves its explicit list lets by
disabling only Lean's optional `cleanup.letToHave` transformation for that
theorem; proof elaboration and kernel checking remain enabled. Record tags are checked by finite modes; undecodable frames,
blank searches, and unspecified decoded frames reject.

The run-derived ABI theorem links the result to `gnCommit? r [] res`. The
scratch-preservation theorem covers every cell at or above N, including the
completed result, finish, blank, and all padding. The two endpoint states
are stable arrivals, not verdicts or installer entries.

Fixtures include the existing canonical `GNTapeStateExamples.capFirstFrames`:
179 steps from the returned cap configuration and 1742 from its encoded
initial configuration. Initial execution is theorem composition, not an
independent kernel evaluation of 1742 steps. Independent kernel probes execute
the new rows from literal returned configurations. The zero-input single
const-true fixture checks terminal head 48 and final-output cell 47 = true;
its retained scratch output is cell 83. The tight const-false case takes 139
steps, and a two-gate false-result fixture exercises data-false plus cursor
advance. Full propositions have named surface pins and direct focused and
aggregate audit roots.

Out of scope: acceptance, first-arrival minimality, arbitrary-stage iteration,
scratch reset/reuse, composed clock adequacy, ContentVerifierBridge, advice
freedom, and N1/N3. In particular retained true scratch is not consumable by
the old values/tail pass without additional work. The one-directional
P-vs-NP extraction chain and all pnp4 Lean are unchanged.

The freeze migration uses two commits. Stage (a) contains the implementation,
proofs, tests, registrations and initial slice record, intentionally leaving the
old manifest stale on exactly the authorized owner. Stage (b) also carries the
required decision-record header/authorization/migration update and current-status
corrections; stage (a) did not contain all final documentation bytes. Its
immediate stage-(b) child changes
no Lean or frozen byte: it repins the checker constants and regenerates the
schema-3 manifest from the committed Git subtree and completes the documentation.
The fresh authorization and requirement-1 rationale are recorded in
[TMVERIFIER_FREEZE.md](TMVERIFIER_FREEZE.md#authorized-gn-e2-5e-local-migration-2026-10-02).
No squash, push, or PR is part of this task. The history through integration
head `beba9d1b` adds the three merges recorded below after stage (b); this
documentation correction is a later child, not a new freeze migration.
Original targeted Lane B validation and pre-correction commit identifiers are
recorded in `/tmp/gn-e25e-writer-report.md`; no full-check run is claimed.

## Ordered content-addressed migration

Stage (a) is `a1bd06ee3639879c1b9e4b8563d7c856185a1d86`, a direct child of
`067b9ff6253dfa746dfe34e591d2739344593eb9`. Its authoritative TMVerifier subtree
is `17eded124b0b76fb02ceca62b8ad82d91d0fe288`. The old checker was run on
committed stage (a) and reported exactly the authorized owner. The corrected
stage-(b) child is `1cefc7a0670c32254491978615b100071bc84a9c`; it changes only
the checker pins, generated manifest, slice and freeze decision records, and
current-status documentation relative to stage (a). No Lean or frozen byte
changes in stage (b). Its amendment from superseded unpushed
`18ac69f15ac7d4d854802f8cfb5c7026673d893d` leaves checker pins and manifest
unchanged. Original post-repin validation is recorded in
`/tmp/gn-e25e-writer-report.md`; stage-(b) amendment checks are recorded in
`/tmp/gn-e25e-docfix-report.md`. The prior documentation correction at
`20945334` is recorded in
`/root/reports/gn-e25e-a708-docfix-writer.md`. This correction's checks and
resulting SHA are recorded in `/root/reports/gn-e25e-beba-docfix-writer.md`.

Release scope is measured at integration head
`beba9d1b669323e1dd01ae65a853afb1af090537` against its main parent
`5deb0abda65479a529111e66fa97bcb409661118`:
**1093 additions + 12 deletions = 1105 changed Lean LOC across nine Lean files**
(eight modules plus `lakefile.lean`). The original stage-(a) parent
`067b9ff6253dfa746dfe34e591d2739344593eb9` is historical, not the release-scope
base. Three `origin/main` integration merges followed stage (b):
`2cda48bd9ed267e4c47c0cd3bb7cd35e36dc75fb` merged
`bedc3d1710d034dc913b862969b7b436a7cc0bcc`, then
`a7086994cebe3dcee10fba463f736fd23e13d3cf` merged
`ea574c53644e19a0f24c0bdf0f356d1c403b60ea`, then
`beba9d1b669323e1dd01ae65a853afb1af090537` merged
`5deb0abda65479a529111e66fa97bcb409661118`. The original-base-to-integration-head
whole-repository diff is 5262 additions + 88 deletions across 32 files,
including main's G3r/G3s/G3t work; it is not the slice's Lean scope.
All three merges preserve the GN-E2-5e owner, extension modules, focused tests,
checker pins and manifest; shared registrations, aggregate audits and status
records incorporate main's changes.

The explicit freeze decision pair is stage (a)
`a1bd06ee3639879c1b9e4b8563d7c856185a1d86` and its immediate corrected
stage-(b) child `1cefc7a0670c32254491978615b100071bc84a9c`.
The latter superseded `18ac69f15ac7d4d854802f8cfb5c7026673d893d` under freeze
rule 3(b) through a documentation-only amendment; that amendment changed no
Lean, checker pin, manifest or frozen byte. This later documentation correction
preserves that pair and all three integration merges in ancestry.

Validation is targeted only. Original implementation and stage-(b) evidence
remains scoped to those snapshots. The existing successful targeted-build log
`/tmp/lane-b-gn-e25e-merge-targeted.log` matches the earlier integration head
`2cda48bd`: 5607 aggregate audit entries, ending at `AxiomsAudit.lean:6858`.
It does not validate the merged `AxiomsAudit.lean` union at `beba9d1b`, which
contains 5659 roots: 52 roots absent from that log (30 G3s roots added at
`a7086994` and 22 G3t roots added at `beba9d1b`). Targeted
validation of that merged union remains outstanding; no successful merged-head
build is claimed. This correction runs only documentation/Git consistency
checks and read-only freeze verification. No Lean build or full check is run,
and no full gate, fresh independent approval, remote CI or owner attestation is
claimed for this correction. No push is performed.

Reproduce the release Lean scope with immutable endpoints (sum the first two
columns and count the rows):

```sh
git diff --numstat 5deb0abda65479a529111e66fa97bcb409661118 beba9d1b669323e1dd01ae65a853afb1af090537 -- '*.lean'
```

The result is 1093 additions, 12 deletions, nine files, satisfying the
1500-changed-Lean-LOC and ten-module caps. The historical whole-repository
comparison is separately reproducible:

```sh
git diff --shortstat 067b9ff6253dfa746dfe34e591d2739344593eb9 beba9d1b669323e1dd01ae65a853afb1af090537
```

The targeted log ends with `Build completed successfully.` Its 5607 aggregate
audit messages match the root names and line numbers at `2cda48bd` (allowing
Lean's qualification of printed names); its last root is
`Pnp3.Tests.UniformV1FixedRawLengthFenceSurfaceTests.check_endpoint_definitions`.
The 30 roots added at `a7086994` and 22 added at `beba9d1b` do not occur in
the log: 52 roots of the current 5659-root union are absent. This identifies
the audit snapshot supported by that log, not a successful build of the later
merged union. Release validation remains with the supervisor.

## Exact public endpoint declarations and hypotheses

These signatures are transcribed from
`pnp3/Complexity/TMVerifierExtensions/GateNFirstCommit.lean`, in namespace
`Pnp3.Internal.PsubsetPpoly.TM`, with proof bodies omitted. `res` is a Boolean
parameter, not a semantic-success premise. Only the encoded-initial theorem
requires `hs`. The physical-configuration lemma explicitly requires `hr`;
the main execution proof derives its needed bound from `gnFirstRequest_room hg`.
The structure theorem takes only `hg` and `res`; scratch preservation also takes
`i` and `hi`. All conclusions are equalities or conjunctions of equalities;
none is an acceptance theorem, an iff, or a first-arrival minimality statement.

```lean
theorem gnFirstReturnedConfig_eq_physical {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hr : 4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1 <
      GNM.tapeLength (encodeGN r).length) :
    gnFirstReturnedConfig r g hg res =
      gnCommitConfig (encodeGN r).length
        (4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1) hr
        (frameListTape ((encodeGNFrames r ++
          g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits)) (gnReturnedState res)
```

```lean
theorem gnCS_firstReturned_commit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res
```

```lean
theorem gnCS_encodeGN_firstCommit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g)+1) +
        gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res
```

```lean
theorem gnFirstCommit_structure {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    let out := TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res) (gnFirstCommitSteps r g)
    out.state = ⟨(0 : Fin 1), if r.program.gates.length = 1 then
      .firstCommitTerminal else .firstCommitNext⟩ ∧
    (out.head : Nat) = gnFirstCommitHead r g ∧
    out.tape = frameListTape ((encodeGNAtFrames r [res] ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) ∧
    gnCommit? r [] res = some ([res], encodeGNAtFrames r [res]) ∧
    gnCurrentValues r [res] = r.inputs ++ [res] ∧
    gnFinalValue r [res] = (if r.program.gates.length = 1 then res else false)
```

```lean
theorem gnFirstCommit_scratch_preserved {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length)) (hi : (encodeGN r).length ≤ i.val) :
    (TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g)).tape i = (gnFirstReturnedConfig r g hg res).tape i
```
