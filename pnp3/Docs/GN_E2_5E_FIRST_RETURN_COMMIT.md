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
explicit relocated/intercepted `gnFirstReturnedConfig`. Its only assumptions
are first-gate selection `hg` and the supplied Boolean. The initial-run
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

The freeze migration uses two commits. Stage (a) contains all implementation,
proof, test, and documentation bytes, intentionally leaving the old manifest
stale on exactly the authorized owner. Its immediate stage-(b) child changes
no Lean or frozen byte: it repins the checker constants and regenerates the
schema-3 manifest from the committed Git subtree. No squash, push, or PR is
part of this task. Targeted Lane B validation and final commit identifiers are
recorded in `/tmp/gn-e25e-writer-report.md`; no full-check run is claimed.
