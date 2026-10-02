# GN-E2-5e: canonical first-return commit

Classification: **Infrastructure**. This change reduces neither pnp4 source
obligation. The base is `067b9ff6253dfa746dfe34e591d2739344593eb9`; only
`GateNFixedDelegateRelocation.lean` changes inside the frozen subtree.

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
No squash, push, or PR is part of this task. Original targeted Lane B validation
and pre-correction commit identifiers are recorded in
`/tmp/gn-e25e-writer-report.md`; no full-check run is claimed.

## Ordered content-addressed migration

Stage (a) is `a1bd06ee3639879c1b9e4b8563d7c856185a1d86`, a direct child of the requested base. Its
authoritative TMVerifier subtree is `17eded124b0b76fb02ceca62b8ad82d91d0fe288`. The old checker was run on
the committed stage (a) and reported exactly the authorized owner. This
stage-(b) child changes only the checker pins, generated manifest, slice and
freeze decision records, and current-status documentation; no Lean or frozen
byte changes. Its original unpushed SHA `18ac69f15ac7d4d854802f8cfb5c7026673d893d`
is superseded by the documentation-only amendment, preserving stage (a) as the
immediate parent. The amendment leaves the checker pins and manifest unchanged.
Original post-repin validation is recorded in `/tmp/gn-e25e-writer-report.md`;
corrected-head non-Lean checks and the resulting SHA are recorded in
`/tmp/gn-e25e-docfix-report.md`. No full gate, independent approval, remote CI
or owner attestation is claimed for the corrected head. No Lean build or full
check is run during this correction while the globally exclusive full gate is
active; release validation remains with the supervisor.

Scope against `067b9ff6253dfa746dfe34e591d2739344593eb9` is exactly
**1093 additions + 12 deletions = 1105 changed Lean LOC across nine Lean files**
(eight modules plus `lakefile.lean`). Validation is targeted only.

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
