# Project Status (current)

**GN-E2-5d / PR #1810 (2026-10-01, Infrastructure only):** the finite
`requestReady` launch executes the installed request back to its opening `bof`
and enters the fixed G1 start. `gnCS_encodeGN_firstLaunch_exact` assumes only
`hg`; output-done and first return additionally require `spec = some res`.
The full-tape real-input fixtures launch at **1333**, reach output-done at
**1562**, and intercept at **1563/head107**. Scratch cell111=true and GN
reserved cell11=false. Canonical first `notGate 0` on `[true]` still launches
with undefined specification; a first returned bit is not the program verdict.

At exact integration head `58c334417d29086245c488bf980d2154194f1b8f`,
the targeted Lane B implementation/surface/axiom build passed, Codex and
Fable 5.1 both returned **APPROVE**, and the globally exclusive
`pnp2-full-check /root/pnp2-lane-b-gn-e25d` completed all **17 steps**.
Freeze checker, negative controls and policy tests passed there too.
[PR #1810](https://github.com/khanukov/p-np2/pull/1810) records that release;
the exact-head reports and full-gate log are linked in the
[GN-E2-5d evidence record](pnp3/Docs/GN_E2_5D_FIRST_REQUEST_LAUNCH.md).

The Qodo correction fixes three findings: launch now rejects blank frames,
the two stale writer comments describe the active launch, and these records
include the completed integration-head validation. The generic scan requires
no internal `bof` **or blank**; concrete request bodies discharge both premises.
`gnCS_requestReady_allBlank_reject_exact` proves genuine rejection after
`5+k` steps from every legal head on a no-bof all-blank tape, at head `h-4`
with the entire tape unchanged, including clamping at zero. An independent
kernel fixture checks heads zero and four plus a nine-step persistence instance;
the generic theorem proves stable rejection for every extra step. The new
endpoint and fixture have named full-proposition surfaces and direct roots in
both audits (40 focused roots total). The canonical launch/return propositions
retain their existing premises. The current PR scope against `origin/main`
is **893 additions + 17 deletions = 910 changed Lean LOC**, across **eight
modules plus lakefile.lean**, below both caps.

This correction uses a new ordered stage-(a) implementation commit and an
immediate stage-(b) content-addressed repin, preserving the original
`f07c4439` → `2644c724` migration, docs child `80a2680b`, and integration head
in ancestry. Only the authorized control owner and writer change in the
120-object frozen subtree. Stage (b) changes no Lean or frozen byte.
Corrected-head validation is targeted Lane B plus freeze/negative/policy tests;
the earlier APPROVE verdicts and 17-step gate apply only to `58c33441`.
Fresh full-gate/review results, remote CI and owner attestation at a future
release head are not claimed. This correction is committed locally, with no push.

Returned-bit commit, cursor/spent advance, repeated gates, verdict, GN
acceptance, first-arrival minimality, composed runtime adequacy,
`ContentVerifierBridge`, and Lane B N1/N3 remain open. No pnp4 bridge,
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` is supplied;
no P-vs-NP mainline progress is claimed.

**Historical GN-E2-5c values induction and first-request tail (2026-10-01,
Infrastructure only):** on base `b71eb6ca3ff4101d6d1596dfb4fc06ce63f845c7`,
`GateNValuesInduction` executes every actual input value through the live
classifier using the landed one-value theorem, then executes the existing
output-false tail writer to the exact `gnFirstRequestReadyConfig` endpoint.
The initial theorem assumes only the selected first-gate equation. Its clock
is `gnValuesEntrySteps + (k*(8*d+38) + (4*d+20))`, with `k = r.inputs.length`
and `d = gnValuesTailDistance r g`. The full nonempty request now fits within
**529 added Lean lines, six Lean files including lakefile.lean (five modules)**.
The 136-step two-value and 1300-step encoded nonempty fixtures pass, as do the
targeted Lane B builds and all 22 direct new audit roots. The exact frozen
premises, surfaces, evidence and limits are in the
[GN-E2-5c record](pnp3/Docs/GN_E2_5C_VALUES_INDUCTION.md).

Stage (a), `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8`, committed the validated frozen
bytes and registrations/surfaces/audits. Stage (b),
`4ffd71f356e13babde80397186ee176e5455ccc5`, repinned the checker and manifest to
stage (a)'s subtree `b2762b378800f81e6adaaa3ecbe6b277ddd59482` (120 objects), with no
frozen-byte change. The freeze checker, negative controls and local policy
unit tests passed. Both stages preserve the exact base in ancestry. The docs-only
child `6c21021a1ca9685bd7fa563c7cc005bc87fd08b8` and its docs-only follow-up
`e984d32d16fe172307127fa8c58ceaf2009e6173` corrected the GN-E2-5b/5c records
without changing Lean, pins or frozen bytes. The integration head
`85a8c61b6c926b4a54594a84504c28ac4e11f269` subsequently
passed the globally exclusive 17-step full gate; exact-head Codex and Fable 5.1
reviews both reported **APPROVE**. PR #1808 carries the `Infrastructure` and
`tmverifier-unfreeze` labels, the owner's full-SHA attestation, and successful
CodeQL and freeze-policy runs. The final raw CI rollup and a fresh agentic review
of this release-record correction remain merge gates. Exact evidence and scope
limits are recorded in the GN-E2-5c record linked above.
Request launch, delegation, returned-bit commit, repeated gates, verdict,
acceptance, first arrival and new-clock/runtime adequacy remain open, together
with Lane B's N1/N3 carry-forward items. No P-vs-NP source obligation is reduced.

The following GN-E2-5b and earlier records describe their dated snapshots;
their then-open values-list/tail work is discharged only by GN-E2-5c above.
Their reviews and gates do not transfer to this new slice.

**Historical GN-E2-5b one-value Infrastructure slice (2026-10-01):** on merged base
`b83de46cc67ecfbf52093807b66b9cd7acf04010`, the live classifier and installer
copy one value in `8*d+37` rows through the data exit; the stationary dispatch
returns to `valuesEntry` after `8*d+38`. The real initial capstone returns at
head 8 with one copied `data` frame and the request tail pending (1184 rows in
the literal example). The implementation at reviewed head
`df7699642bf22673cfee7f3ebe6c37e36128360a` measured **903 changed Lean lines
across seven Lean files including `lakefile.lean`**, with no transition-row
changes. Its targeted Lane B builds, 44 focused audit roots, freeze checker
and negative controls passed as recorded in the
[implementation and review record](pnp3/Docs/GN_E2_5B_VALUES_COPY.md).
Stage (a), `b16d816e011560e86ea81ffa1a08da20e18cd2d2`, committed the frozen
bytes; stage (b), `df7699642bf22673cfee7f3ebe6c37e36128360a`, repinned tree
`e4fa8f333a055e8bbce4c258af7f84719426416a` with 119 manifest objects and
changed no frozen byte. Fable 5.1 and Codex both approved that exact stage-(b)
head; Fable listed seven documentation notes. Neither review covers this later
correction.
The documentation-only follow-up preserved both stages, frozen bytes and pins.
At integration release head `e65231fc1be4c12d9338b39dd67e8d8e9a6b8571`,
the targeted Lane B build passed, exact-head remote CI completed `scripts/check.sh`,
and exact-head Codex and Fable 5.1 reviews approved. PR #1806 carries the `Infrastructure` and
`tmverifier-unfreeze` labels, the owner's full-SHA attestation, and a successful
freeze-policy run. Qodo's later documentation finding is corrected by this dated
release record; fresh checks and reviews of that correction remain required before
merge. At that GN-E2-5b snapshot full-list execution and nonempty request
completion remained open; GN-E2-5c now discharges those execution targets.
**Lane B owns the deferred N1/N3 follow-up**, explicitly still open in the
[carry-forward register](pnp3/Docs/GN_E2_5B_VALUES_COPY.md#carry-forward-ownership).
Historical GN-E2-5a records below retain their dated scope.

**GN-E2-5a current-main record before G3n integration
(2026-09-29, Infrastructure only):** Qodo's
finding at PR #1804 exact head
`1b5aa3e219d30d2292c8cd13bbc8e68acbbb1d90`, as supplied by the owner,
is addressed by the two-stage migration recorded in `TMVERIFIER_FREEZE.md`.
Stage (a) is `1e7fe40592001142378ff3620c888045d8c10594`; stage (b)
repins tree `145252565dc2538c6c01c19fc2f6814abc1c3a8d` and updates these
records. At main `b83de46cc67ecfbf52093807b66b9cd7acf04010`, the GN-E2-5a
dependency-closed delta is **1499 changed Lean lines (1468 added, 31 deleted)
across 8 files**, including `lakefile.lean`, against merge base
`2f8a3d5e6f90fe41a2cd7bc240d3c9fad407b68e`. The 1497-line counts below
are historical measurements before this correction. The owner-label deferral
was closed; GN-E2-5b implementation was paused at that date. No review of
either owner-docstring correction head was claimed in that record. The sole
repository category remains
`Infrastructure`; the existing `tmverifier-unfreeze` labeling intent remains.
No remote label or attestation is issued by this local correction.

Updated: 2026-10-01

**Historical Lane B integration update (2026-09-29, Infrastructure):**
the GN-E2-5a branch's third
integration merge brings `main` at `2f8a3d5e6f90fe41a2cd7bc240d3c9fad407b68e`
into `03b8184402fb7bf092d3bcd72ca7c936fab9862b`, preserving both histories.
G3m and GN-E2-5a remain intact; the frozen subtree and pins are unchanged.
Against that new base, GN-E2-5a still changes **1497 Lean lines across 8 files**
(including `lakefile.lean`). References below to two integration merges and
`9445a93e` as the current base describe the preceding snapshot. This integration
did not establish a full-check or review gate result. GN-E2-5b was still paused
at that integration; the authorized one-value result is recorded above.

**Part A G3p — Infrastructure: executed cursor → unchanged G3o handoff H2.**
`FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown` composes the
unchanged five-state `FixedPairSeparatorCursor` with G3o using `UniformTM.seq`:
**201 states, 603 rows**, start 0, accept 199, reject 200, tail entry 5.
**Sixteen of seventeen handoffs are executed; only H1 remains proof-level.**
The phase-local entry has head zero and the complete sentinelized pair tape;
it is not raw `initialConfig`. At strict first entry `T = 2*a+2`, H2 writes
back the nonblank lookahead bit unchanged and moves left to head `2*a`,
retaining the full `sentinelTape`. Both Boolean lookahead rows are live.
H3 follows one step later, erases the separator, and stays. H2 is clamp-free
on valid pairs, including empty pairs and `B=0`; the inherited removal origin
clamp remains at `T+(1+(Removal.clock a-2))`. The H3/H4/H5/H6/H7 controls are
8/17/24/50/54 at their inherited times plus T; H6 retains head zero and the
whole `alignedTape`. Every later G3o full configuration is transported.

`separator_cursor_countdown_drained` preserves exactly the eight inherited
premises: matching tag, gamma width, dispatcher strict first terminal,
width at least two, fence bound, allocation room, register-bit identification,
and zero high bits. The theorem-derived finite witness uses
`a=8, m=9, B=22, zeros=4, C=18, q=qHasOne, borrow=0, v=F=24` and reaches
**2991 = 18+2973 steps, accept 199, head 23**, with the complete
`loopTape 22 tag physWord 4 0 24` and persistence thereafter. Its 49-cell
layout has drained register cells 18–22, blank 23, marks 24–47, blank 48.
This witnesses the eight execution premises, not `ContentAccepts` nonvacuity,
runtime decoding of 24, or first arrival of composed accept. In particular,
2991 exceeds B=22: B allocates tape, not time.

Three blank source rows reject with unchanged head/tape. Malformed
sentinelized raw-word rejection requires **positive padding B>0**; that
restriction is not imposed on valid-pair or inherited rejection theorems.
Independent finite probes expose the B=0 malformed counterexample and the
valid empty pair's raw-entry rejection versus successful phase-local H2.
Both inherited rejection branches preserve their full endpoints and all
later persistence at the original deadlines, without a converse or
first-rejection claim.

H1, raw-input front-chain execution, runtime fence/cap and budget domination,
full parser/GN bridge, runtime selection of C/q/v, advice freedom, language
acceptance, `TM.runConfig` conversion, and `ContentVerifierBridge` remain open.
No pnp4 bridge advances: the accepted-content composite bridge still starts
at G3e. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. This is not P-vs-NP mainline progress.

The following G3o record is historical (fifteen executed, two remaining).

**Part A G3o — Infrastructure: executed separator-hole → unchanged G3n handoff H3.**
`Complexity.Uniform.V1.FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown`
sequences the unchanged three-state hole machine into unchanged G3n with
`UniformTM.seq`: **196 states, 588 rows**, start 0, accept 194, reject 195,
tail start 3. **Fifteen of seventeen handoffs are executed; H1–H2 remain
proof-level connections.** H3's sole live accepting row reads `some true` at
state 0, writes blank, stays, and enters state 3 in exactly one transition.
The two bad scanned symbols route to reject; dead left verdict copies also
have cross-block rows. Neither dead copy (1 or 2) is a target or the start.

The unconditional strict handoff starts from the phase-local encoded-pair
configuration: head `2*a`, full `sentinelTape`, scanned `some true`. At time 1
it has head `2*a` and complete `holeTape`. It proves left-block confinement
before that time, no composed verdict through that time, routed-left equality
through time 1, and whole-configuration transport of every G3n suffix. H3 is
stationary even at `a=0` or `B=0`; the inherited removal origin clamp still
occurs at `1 + (Removal.clock a - 2)`. H4 arrives separately at
`1 + Removal.clock a`, control 12, head 0, full `compactTape`; H5/H6/H7 are
19/45/49 at G3n's times plus one, preserving H6's head 0 and `alignedTape`.

`separator_hole_countdown_drained` retains exactly G3n's eight premises:
matching tag, gamma width, dispatcher `StrictFirstTerminalAt`, width at least
two, `v ≤ F`, allocation room, register-bit identification, and zero high bits.
Strict dispatcher arrival excludes every earlier terminal. The endpoint at
`holeChainClock = 1 + removalChainClock` is accept 194, head
`a+m+2+zeros`, whole `loopTape B x w zeros 0 v`, with persistence thereafter.
This is not first arrival of composed accept. Both inherited rejection
branches are forward guarantees with complete head/tape endpoints; mismatch
retains its deadline guarantee, not a first-rejection claim. Source rejection
is only a scanned-symbol guarantee on arbitrary configurations.

Independent `decide` probes cover empty and singleton pairs, both bit values,
empty/nonempty witnesses, budgets 0/1, H3 and H4, and both bad scanned symbols.
The large witness discharges all eight premises and is theorem-derived:
`a=8, m=9, B=22, zeros=4, C=18, q=qHasOne, borrow=0, v=F=24`;
**2973 = 1 + 2972 steps**, accept 194, head 23, full
`loopTape 22 tag physWord 4 0 24`, persistent thereafter. Its 49-cell allocation
has zero register bits at 18–22, blank 23, marks 24–47, blank 48. The whole tape
equality is authoritative. This witnesses satisfiable execution premises,
not `ContentAccepts` nonvacuity or runtime decoding of 24; the full run is not
kernel-reduced. `B` allocates tape and does not bound the runtime.

G3o executes only H3. No H1/H2 execution, raw-input composition, later parser
fields, `TM.runConfig` simulation, runtime fence or budget domination, runtime
selection of `C/q/v`, composed-accept minimality, rejection equivalence,
language acceptance, advice-freedom claim, or verifier bridge is supplied.
**No pnp4 bridge advances**: the accepted-content composite bridge still starts
at G3e. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced; this is not P-vs-NP mainline progress.

The following G3n and G3m records describe their historical fourteen/three and
thirteen/four boundaries; G3p above is the current sixteen/one boundary.

**Historical Part A G3n — Infrastructure: executed tag-removal → unchanged G3m handoff H4.**
`Complexity.Uniform.V1.FixedPairTagRemovalShiftAlignmentCountdown` composes the existing
nine-state tag-removal machine with G3m using unchanged `UniformTM.seq`: 193 states,
579 rows, start 0, accept 191, reject 192. Fourteen of seventeen handoffs were
executed at that stage; H1–H3 remained proof-level connections. The single live
H4 row is state 1 on blank, routed to state 9, writing blank and staying, at
`a * (a + 5) + 2` steps. The origin clamp occurs separately at `clock a - 2`.
Exactly seven live rows target the removal reject once both verdict source states
are excluded.

Relative to main `b83de46cc67ecfbf52093807b66b9cd7acf04010`, that integration added
**528 Lean lines across 4 registered Lean files** (528 added, 0 deleted).
`handoff_exact` has no proposition premises and proves actual `UniformTM.run`
execution: strict left-block confinement before H4, no composed verdict through
H4, whole-configuration handoff at head 0 over `compactTape`, and every later G3m
configuration under the right embedding. The inherited H5/H6/H7 controls are
16/42/46. `tag_removal_countdown_drained` retains exactly eight G3m premises:
matching tag, gamma width, dispatcher `StrictFirstTerminalAt`, width at least two,
`v ≤ F`, allocation room, register-bit identification, and zero high bits. It
reaches accept at `removalChainClock`, head `a + m + 2 + zeros`, tape
`loopTape B x w zeros 0 v`, and persists. This is not first arrival of composed
accept. Tiny independent reduction probes cover empty inputs at budgets 0/1 and
both singleton query bits with empty/nonempty witnesses. The large fixture is
theorem-derived: hand-supplied `v = 24`, 2972 = 106 + 2866 steps, accept 191,
head 23, `loopTape 22 tag physWord 4 0 24`. This is execution nonvacuity, not
`ContentAccepts` nonvacuity; the full large run is not kernel-reduced.

The start is the encoded-pair tag-removal phase configuration, not raw input.
G3m already executes origin alignment; G3n adds only H4. No later parser field,
`TM.runConfig` conversion, runtime fence, budget-domination theorem, language
acceptance, advice-freedom claim, verifier bridge, or P-vs-NP mainline progress is
supplied. `C`, `q`, and `v` remain theorem parameters, never selected runtime data.
Rejection transport remains forward-only, with the mismatched branch guaranteed
only from the inherited deadline. No pnp4 bridge advances: the accepted-content
composite bridge still starts at G3e. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced.

**Part A G3m, the executed origin-shift → origin-alignment handoff H5: the same sequential
composition applied a thirteenth time, one block further left, with no new table row and no new
combinator (infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown`, with its surface test. **No new table
row and no landed module's code edited**; the landed generic `UniformTM.seq` is reused unchanged and no
`mergeAccept` is needed. The machine is the fixed 7-state, 21-row structural one-cell origin shift on
the left block `[0, 7)` followed by the whole landed G3l 177-state composite on `[7, 184)`, as one
closed 184-state, 552-row table, `FixedPairOriginShiftBootstrap.machine.seq
FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `182` and reject `183`. Write `N = a+m` and `d = borrow x w zeros`. **Thirteen** of the
seventeen handoffs are now performed by a finite table and **four** remain proof-level retags.

* **H5 is executed by one live routed row, and it is a `.stay`.** Over all seven bootstrap states and
  all three symbols, with the accept's own absorbing three excluded, a target of the phase's accept
  forces the fetch state `4` on `none` — the probe that finds the block exhausted
  (`accept_rows_unique`) — and `seq` retargets that one row to the right block's start `tailStart` at
  index `7`, keeping its written `none` and its `.stay`, in that same transition and at no cost. One
  row is as narrow as a live accept list can be; nine of the twelve landed handoffs route one row too,
  and only H6, with three, H15, with four, and H11, with six, are plural. The endpoint head is
  `pairLength a m + min B 1`, which is what `seq_handoff` transports: it uses the post-move head, and
  the routed row itself does not move. The **boundary distinction** matters here: the bootstrap's own
  last right move, at source time `switchTime a m - 2`, clamps exactly when `B = 0` — the landed
  `clamps` proves that equivalence — whereas H5 is a `.stay` and so clamps on neither budget, which
  `check_h5_boundary_probes` exhibits at both `B = 0` and `B = 1`. On the reject side, once **both**
  verdicts' own absorbing rows are excluded, every row of the bootstrap table targeting its reject is
  one of **six** — the two Boolean rows of each of the states `1`, `2`, `3`, the carry and hole probes
  that find a cell occupied where the shift invariant requires it blank — and `reject_rows_unique`
  proves that list exhaustive **in both directions**, over all `7` states and all three symbols, while
  `reject_rows_routed` sends each to the composed reject `183` with the symbol written and the move
  unchanged. None is *taken* out of this slice's `startConfig`:
  `bootstrap_first_arrival` proves the left block is never in its reject at any time whatever, so the
  composed reject is reachable only through the right block. The six rows of the two left verdict
  copies are dead, no left-block row targeting either verdict copy, and the composed start is neither.
  The injective, disjoint block maps cover all `184` states because their domain sizes are `7` and
  `177`; together with the two block row equations in `table_and_resource_pins`, this accounts for
  every composed row and excludes right-block targets from the dead left copies. H6 (three rows, `17`,
  `18` and `19`, all into `33`), H7 (`34 → 37`), H8 (`49 → 52`), H9 (`52 → 55`), H10 (`58 → 61`) and H11
  (six rows inside `[61, 89)`, all into `89`) to H17 (`170 → 173`) are inherited from G3l, its indices
  shifted by seven, located by `(inTail q).val = 7 + q.val` and the universal right-block row equation.
* **The strict arrival H5 needs was already exported, and takes no hypothesis.** The bootstrap phase
  has exactly two absorbing states, `qAccept` and `qReject` — its raw states `5` and `6`, three rows
  each — so the landed `seq` routes both, as for H6 to H10 and unlike H11. Its strict first arrival was
  landed in the shape `seq_handoff` consumes: the landed `noEarlyTerminal` excludes **both** verdicts
  strictly before the clock and takes **no hypothesis at all** — no tag, no width, no room, no positive
  budget — and `run_exact` gives the exact endpoint there. `bootstrap_first_arrival` therefore only
  repackages the two at `switchTime a m = clock a m` and adds, from the landed `run_after`, the
  never-rejects consequence. `run_exact` alone would **not** suffice: it is one endpoint identity, and
  an absorbing phase satisfies it at every later time too, while `seq_handoff` starts the right machine
  inside the accepting transition and so needs the absence of any earlier acceptance.
* **The switch time is linear, but it still reads the split lengths apart.**
  `switchTime a m = 4 * a + 3 * m + 5`: one `a + 1`-cell scan to the top of the blank prefix, then
  three steps — fetch, carry, hole — for each of the `N + 1` cells of the block, then the closing
  accepting step. `clock_pins` identifies it with the phase's own landed `clock a m`, records both
  closed forms, and exhibits `11`, `12` and `13` at `N = 2`, so no reformulation of this chain's clock
  on `N` alone is possible and `switchTime` keeps **two** arguments, as G3l's does. It is far below
  G3l's quadratic switch time — `12` against `54` at `a = m = 1`, `64` against `1590` at the surface
  test's `a = 8`, `m = 9` — but it is *not* the smallest switch time in the chain: the length-only
  `N + 3` and `3 * N + 7` are `20` and `58` at that fixture. The composed clock therefore stays
  quadratic in `a`, and whether the cubic budget still dominates it is **not** proved. This clock is
  also the first in the chain that counts the bootstrap phase's own steps, which no landed clock in
  this chain did.
* **What the switch hands over is exactly what the origin alignment reads.**
  `alignment_start_at_first_arrival` records the semantic dependency and executes nothing, and it needs
  **no hypothesis**: the origin-alignment `startConfig` is built field for field out of the bootstrap
  `finalConfig`, which the landed `run_exact` shows *is* the phase's run at `switchTime a m` for every
  input. `handoff_exact` therefore takes **no hypothesis at all** — no tag, no width, no room, no
  positive budget, no budget-dominates-clock premise — and concludes: the control is strictly inside
  the left block `[0, 7)` at every time strictly before `switchTime a m`; no composed verdict at any
  time up to and **including** it (at the switch time itself the control is `tailStart`, so that bound
  is `≤`); the composed run is the bootstrap phase's own run routed at every such time, as
  whole-`Config` equality; at exactly `switchTime a m` it **is** G3l's landed `startConfig B x w`
  re-embedded; and every later step is a G3l step. `handoff_endpoint_pins` reads that configuration
  back as both G3l's and the origin-alignment phase's own `startConfig` projections, with the source
  head `pairLength a m + min B 1`, the tape the `shiftedTape` — blank below `a`, the content block on
  cells `a … a + N - 1` reading as `Fin.append x w`, the trailing marker `some true` on cell
  `a + N = 2 * a + m`, blanks from `pairLength a m` on — and, for a nonempty query block, that this tape
  is **not** the `alignedTape`: the origin alignment still has to run, and G3l's own
  `(10 * a + 7) * (N + 1) + 3 * a` steps are what move the block down to the origin.
* **The inherited switches and the composed run.** `inherited_alignment_switch` locates the inherited
  H6 at `switchTime a m + tailSwitchTime a m` at composed index `33`, on exactly the head and tape
  G3k's own `startConfig` carries, with the trailing marker still present, and the inherited H7 `N + 3`
  steps later at index `37`, the marker erased by that routed row itself. The deeper inherited locators
  (H8, H9, H10, H11 and below) are **not** re-wrapped here: `handoff_exact`'s last conjunct is a
  universal suffix equality, so G3l's own locators, and through them G3k's four deeper ones, transport
  into this machine by composing that one equation with
  `UniformTM.seqEmbedRight_state/_head/_tape` and `(inTail q).val = 7 + q.val`, exactly as
  `inherited_alignment_switch` does; no fact is lost and none is claimed that is not proved. The
  drained theorem takes G3l's **eight** hypotheses unchanged and lands the composed accept `182` at
  exactly `shiftChainClock C a m zeros d v = switchTime a m + alignmentChainClock C a m zeros d v` on
  the separator blank `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally
  quantified and unsupplied, and persistence is not first arrival.
* **Two inherited rejecting branches, both forward direction only.** On a matching tag whose physical
  suffix holds no gamma terminator the whole prefix hands over and `malformed_reject_handoff` lands the
  composed reject `183` from
  `switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7 + (N - 7))))` on, on the blank boundary
  cell `N` over the erased content tape, the anchor never running. On a **mismatched** tag
  `mismatched_tag_reject_handoff` lands the composed reject from
  `switchTime a m + (tailSwitchTime a m + (N + 3 + (3 * N + 7)))` on, on the gate's own `finalConfig`
  head over that same tape, the gamma blocks never running. Neither is a converse, and the mismatched
  one is deliberately **not** timed exactly, for the reason G3j to G3l record: on a nonempty content
  the gate's own first rejection is at `3 * N + j` for its mismatch *cell* `j`, which this chain does
  not derive from `tagMatches (Fin.append x w) = false`, the value of
  `FixedContentTagGate.finalConfig`'s head being the only public trace of the `badIndex` that defines
  it. So the composed run may already be in the composed reject strictly before the time stated, and
  nothing here says when.
* **Probes.** Kernel reduction of `machine.run` is quadratic in the step count and the tagged fixtures
  all have `a = 8`, so reducing to G3l's own switch at `64 + 1590` overflows the kernel stack. The
  independent `check_*_probe` theorems — which use **no** slice theorem — therefore run on tiny
  tag-free fixtures, which is sound because the bootstrap phase scans those cells but does not test
  their tag, gamma or bit meaning; it only shifts the block one cell left: empty inputs
  (`switchTime 0 0 = 5`) at **both** budgets and `![true]`/`![false]` (`switchTime 1 1 = 12`) at both
  budgets exhibit the whole allocated tape at and before the switch, the single live routed row firing
  `4 → 7` on a blank cell with a stationary head, both carry states on the way — each over a blank
  cell, so each takes its shifting `none` row and neither its rejecting Boolean one — the two budgets
  moving the source head from `1` to `2` and from `4` to `5`, the inherited H6 and H7 at `33` and `37`,
  and the composed reject `183` entered through the **right** block when the inherited tag gate rejects
  the short content. The tagged fixtures are kept for the `check_*_literal*` theorems, which are
  **derived** from the slice's own theorems and so cost no `run` reduction: `tag`/`physWord` switches at
  `64`, reaches the inherited H6 at `1654` and H7 at `1674` and drains at `2866 = 64 + 2802` with the
  register value `24` supplied **by hand** (an execution fixture, not an accepted-content one), the
  malformed fixture rejects from `1172` on and the mismatched one from `1168` on.

Deferred and deliberately not claimed. **Four of the seventeen handoffs remain proof-level**: the
composed `startConfig` is the bootstrap phase's own routed into the composed control, so it still
retags the actual tag-removal `finalConfig` and embeds every earlier phase, no raw-input
`initialConfig` is executed, and no clock counts a step of any phase *before* the origin shift;
`handoff_pins` records H4 as a hypothesis-free identification and pins no earlier phase's table row.
**No pnp4 bridge**: the standalone phases' pnp4 semantics are unchanged and no `ContentVerifierBridge`,
raw-input acceptance, `AcceptsAt`, `DecidesWithin` or `UniformP` runtime theorem appears; whether the
cubic budget still dominates the quadratic-in-`a` composed clock is not proved here, and no
advice-freedom or wrapper-level claim is made. **No first arrival of the composed accept**: the
arrivals proved are the bootstrap phase's and, as a hypothesis, the dispatcher's, each inside its own
block. **No exact time on the mismatched branch**, as above. The **fence** is unchanged — all fourteen
tables are uncapped, so an oversized register still times out; no **footprint** theorem, the bootstrap
phase's own bounding its head only through its own clock and saying nothing about the right block; no
**converse**, so neither composed reject implies anything about the input. The endpoints reached are
internal states out of a retagged actual prior endpoint, neither halting on a raw input nor language
acceptance. The **model connection** remains open (caveat 6 of `VERIFIER_RETARGET_PLAN.md`). Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. This is infrastructure, not
P-vs-NP mainline progress, and it makes no `P ≠ NP` claim.

**Part A G3l, the executed origin-alignment → marker-erase handoff H6: the same sequential
composition applied a twelfth time, one block further left, with no new table row and no new
combinator (infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
with its surface test. **No new table row and no landed module's code edited**; the landed generic
`UniformTM.seq` is reused unchanged and no `mergeAccept` is needed. The machine is the fixed
26-state, 78-row pair origin alignment on the left block `[0, 26)` followed by the whole landed G3k
151-state composite on `[26, 177)`, as one closed 177-state, 531-row table,
`FixedPairOriginAlignment.machine.seq
FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `175` and reject `176`. Write `N = a+m` and `d = borrow x w zeros`. **Twelve** of the
seventeen handoffs were performed by a finite table when this slice landed and **five** remained
proof-level retags; G3m above executed H5, taking the counts to thirteen and four;
G3n subsequently executed H4, taking them to fourteen and three; G3o then executed
H3, taking them to fifteen and two; G3p above now executes H2, taking them to sixteen
and one.

* **H6 is executed by three live routed rows, not one.** Over all twenty-six alignment states and
  all three symbols, with the accept's own absorbing three excluded, a target of the phase's accept
  forces one of the classification states `10`, `11`, `12` on `none` (`accept_rows_unique`), and
  `seq` retargets all three to the right block's start `tailStart` at index `26`, each keeping its
  own written symbol — `none`, `some false`, `some true`, the three restoration writes — and its
  **left** move, in that same transition and at no cost. In **forward execution order** this is the
  first handoff of the chain whose live accept list is plural — the already-executed H11, further
  right, routes six — and the three rows write three different symbols. **Which** of them fires on a
  given input is *not* claimed: those states are `private` in the landed phase and no landed theorem
  identifies the control one step before the clock; the surface test exhibits each of the three by
  kernel reduction at a fixture. The endpoint head is `0`, which is what `seq_handoff` transports: it
  uses the post-move head and `run_exact` pins that to `0`. That routed `.left` move is a genuine
  step onto the origin, **not** a clamp: the landed `boundary_clamps` puts the phase's sole left
  clamp two steps earlier, at source time `clock - 3`, and `check_h6_literal_probe` exhibits the
  switch carrying the head from cell `1` to `0`. On the reject side every row of the alignment table
  targeting its reject is one of **21** — the five `none` rows of states `4, 5, 6, 16, 18` and the
  sixteen Boolean rows of states `0, 13, 14, 15, 19, 20, 21, 23` — and `reject_rows_unique` proves
  that list exhaustive over all `26` states and all three symbols once both verdicts' own absorbing
  rows are excluded, in that one direction only, while `reject_rows_routed` sends each to the
  composed reject `176` with the symbol written and the move unchanged. None is
  *taken* out of this slice's `startConfig`: `alignment_first_arrival` proves the left block is never
  in its reject at any time whatever, so the composed reject is reachable only through the right
  block. The six rows of the two left verdict copies are dead, no left-block row targeting either
  verdict, and the composed start is neither. The injective, disjoint block maps cover all `177`
  states because their domain sizes are `26` and `151`; together with the two block row equations in
  `table_and_resource_pins`, this accounts for every composed row and excludes right-block targets
  from the dead left copies. H7 (`27 → 30`), H8 (`42 → 45`), H9 (`45 → 48`), H10 (`51 → 54`) and H11
  (six rows inside `[54, 82)`, all into `82`) to H17 (`163 → 166`) are inherited from G3k, its
  indices shifted by twenty-six, located by `(inTail q).val = 26 + q.val` and the universal
  right-block row equation.
* **The strict arrival H6 needs was already exported, and takes no hypothesis.** The alignment phase
  has exactly two absorbing states, `qAccept` and `qReject` — its raw states `24` and `25`, three
  rows each — so the landed `seq` routes both, as for H7 to H10 and unlike H11. Its strict first
  arrival was landed in the shape `seq_handoff` consumes: the landed `strict_first_terminal` gives
  both halves against the phase's `qAccept` and `qReject`, which its own landed `resource_pins`
  identifies with `machine.accept` and `machine.reject`, and it takes **no hypothesis at all**.
  `alignment_first_arrival` therefore only repackages it at `switchTime a m = clock a m` and adds,
  from the landed `accepting_absorption`, the never-rejects consequence. `run_exact` alone would
  **not** suffice: it is one endpoint identity, and an absorbing phase satisfies it at every later
  time too, while `seq_handoff` starts the right machine inside the accepting transition and so needs
  the absence of any earlier acceptance.
* **The switch time is the first in this chain to depend on the split lengths `a` and `m`
  separately.** The landed switch times are of three kinds, none of them a function of the split:
  length-only in `N = a + m` (H7's `N + 3`, H8's `3 * N + 7`), width-only in the decoded `zeros`
  (H9's `zeros + 1`, H10's `successTime zeros = 2 * zeros + 5`) and input-dependent (H11's `C`, for
  which no length formula exists). The alignment clock `(10 * a + 7) * (a + m + 1) + 3 * a` is
  quadratic in `a` and reads the two lengths apart, so `switchTime` here takes **two** arguments and
  so does `alignmentChainClock`. `clock_pins` records that break explicitly and exhibits three
  different values at one `N` — `switchTime 0 2 =
  21`, `switchTime 1 1 = 54`, `switchTime 2 0 = 87` — so no reformulation of this chain's clock on
  `N` alone is possible. The composed clock is therefore quadratic in `a`, and whether the cubic
  budget still dominates it is **not** proved. This clock is also the first in the chain that counts
  the alignment phase's own steps, which no landed clock in this chain did.
* **What the switch hands over is exactly what the marker-erase scan reads.**
  `marker_erase_start_at_first_arrival` records the semantic dependency and executes nothing, and it
  needs **no hypothesis**: the marker-erase `startConfig` is built field for field out of the
  alignment `finalConfig`, which the landed `run_exact` shows *is* the phase's run at
  `switchTime a m` for every input. `handoff_exact` therefore takes **no hypothesis at all** — no
  tag, no width, no room, no positive budget, no budget-dominates-clock premise — and concludes: the
  control is strictly inside the left block `[0, 26)` at every time strictly before `switchTime a m`;
  no composed verdict at any time up to and **including** it (at the switch time itself the control
  is `tailStart`, so that bound is `≤`); the composed run is the alignment phase's own run routed at
  every such time, as whole-`Config` equality; at exactly `switchTime a m` it **is** G3k's landed
  `startConfig B x w` re-embedded; and every later step is a G3k step. `handoff_endpoint_pins` reads
  that configuration back as both G3k's and the marker-erase phase's own `startConfig` projections,
  with the head on the origin cell `0`, the tape the `alignedTape`, the trailing content marker
  **still** `some true` on cell `N` — the inherited H7 row erases it `N + 3` steps later — and every
  allocated cell above `N` blank.
* **The inherited switches and the composed run.** `inherited_marker_erase_switch` locates the
  inherited H7 at `switchTime a m + (N + 3)` at composed index `30`, on exactly the head and tape
  G1's own `startConfig` carries, with the trailing marker gone. The four deeper inherited locators —
  H8 at `45`, H9 at `48`, H10 at `54`, H11 at `82` — are **not** re-wrapped here: `handoff_exact`'s
  last conjunct is a universal suffix equality, so G3k's own four transport into this machine by
  composing that one equation with `UniformTM.seqEmbedRight_state/_head/_tape` and
  `(inTail q).val = 26 + q.val`, exactly as `inherited_marker_erase_switch` does for H7; no fact is
  lost and none is claimed that is not proved. The drained theorem takes G3k's **eight** hypotheses
  unchanged and lands the composed accept `175` at exactly
  `alignmentChainClock C a m zeros d v = switchTime a m + eraseChainClock C N zeros d v` on the
  separator blank `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally
  quantified and unsupplied, and persistence is not first arrival.
* **Two inherited rejecting branches, both forward direction only.** On a matching tag whose physical
  suffix holds no gamma terminator the whole prefix hands over and `malformed_reject_handoff` lands
  the composed reject `176` from `switchTime a m + (N + 3 + (3 * N + 7 + (N - 7)))` on, on the blank
  boundary cell `N` over the erased content tape, the anchor never running. On a **mismatched** tag
  `mismatched_tag_reject_handoff` lands the composed reject `176` from
  `switchTime a m + (N + 3 + (3 * N + 7))` on, on the gate's own `finalConfig` head over that same
  tape, the gamma blocks never running. Neither is a converse, and the mismatched one is deliberately
  **not** timed exactly, for the reason G3j and G3k record: on a nonempty content the gate's own
  first rejection is at `3 * N + j` for its mismatch *cell* `j`, which this chain does not derive
  from `tagMatches (Fin.append x w) = false`, the value of `FixedContentTagGate.finalConfig`'s head
  being the only public trace of the `badIndex` that defines it. So the composed run may already be
  in the composed reject strictly before the time stated, and nothing here says when.
* **Probes.** Kernel reduction of `machine.run` is quadratic in the step count and the tagged
  fixtures all have `a = 8`, so `switchTime 8 m` is already `981` or more and reducing to the switch
  overflows the kernel stack. The independent `check_*_probe` theorems — which use **no** slice
  theorem — therefore run on new tiny tag-free fixtures, which is sound because the alignment phase
  scans those cells but does not test their tag, gamma, or bit meaning; it only shifts the block to
  the origin: empty inputs (`switchTime 0 0 = 7`) exercise the routed row of state `10`,
  `![true]`/`![false]`
  (`switchTime 1 1 = 54`) that of state `11`, and `![true]`/`![true]` that of state `12`, so all
  three live H6 rows are exhibited, together with `B = 1`, the inherited H7 firing `N + 3` later, and
  the composed reject `176` entered through the **right** block when the inherited tag gate rejects
  the two-cell content. The tagged fixtures are kept for the `check_*_literal*` theorems, which are
  **derived** from the slice's own theorems and so cost no reduction: `tag`/`physWord` switches at
  `1590` and drains at `1590 + 1212 = 2802` with the register value `24 > N` supplied **by hand** (an
  execution fixture, not an accepted-content one), the malformed fixture rejects from `1126` on and
  the mismatched one from `1122` on.

Deferred and deliberately not claimed. **Five of the seventeen handoffs remain proof-level**: the
composed `startConfig` is the alignment phase's own routed into the composed control, so it still
retags the actual origin-shift-bootstrap `finalConfig` and embeds every earlier phase, no raw-input
`initialConfig` is executed, and no clock counts a step of any phase *before* origin alignment;
`handoff_pins` records H5 as a hypothesis-free identification and pins no earlier phase's table row.
**No pnp4 bridge**: the standalone phases' pnp4 semantics are unchanged and no
`ContentVerifierBridge`, raw-input acceptance, `AcceptsAt`, `DecidesWithin` or `UniformP` runtime
theorem appears; whether the cubic budget still dominates the now quadratic-in-`a` composed clock is
not proved here, and no advice-freedom or wrapper-level claim is made. **No first arrival of the
composed accept**: the arrivals proved are the alignment phase's and, as a hypothesis, the
dispatcher's, each inside its own block. **No exact time on the mismatched branch**, as above. The
**fence** is unchanged — all thirteen tables are uncapped, so an oversized register still times out;
no **footprint** theorem, the alignment phase's own bounding its head only through its own clock and
saying nothing about the right block; no **converse**, so neither composed reject implies anything
about the input. The endpoints reached are internal states out of a retagged actual prior endpoint,
neither halting on a raw input nor language acceptance. The **model connection** remains open (caveat
6 of `VERIFIER_RETARGET_PLAN.md`). Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. This is infrastructure, not P-vs-NP mainline progress,
and it makes no `P ≠ NP` claim.

**Part A G3k, the executed marker-erase → tag-gate handoff H7: the same sequential composition
applied an eleventh time, one block further left, with no new table row and no new combinator
(infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
with its surface test. **No new table row and no landed module's code edited**; the landed generic
`UniformTM.seq` is reused unchanged and no `mergeAccept` is needed. The machine is the fixed 4-state,
12-row trailing-content-marker erasure on the left block `[0, 4)` followed by the whole landed G3j
147-state composite on `[4, 151)`, as one closed 151-state, 453-row table,
`FixedPairContentMarkerErase.machine.seq
FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `149` and reject `150`. Write `N = a+m` and `d = borrow x w zeros`. **Eleven** of the
seventeen handoffs were performed by a finite table when this slice landed and **six** remained
proof-level retags; G3l above has since executed H6 as well, taking the counts to twelve and five.

* **H7 is executed by one live routed row, which performs the erasure itself.** Over all four
  marker-erase states and all three symbols, with the accept's own absorbing three excluded, a target
  of the phase's accept forces `qErase` on `some true` (`accept_row_unique`), and `seq` retargets that
  row to the right block's start `tailStart` at index `4`, writing `none` and **staying**, in that
  same transition and at no cost. That written `none` *is* the erasure of the trailing content
  marker: this routed row does not rewrite the symbol it read but blanks it, so the composed table
  performs the mutation itself, in the very transition that hands over. On the reject side this slice
  is the first of the chain whose live list is both **complete** and **plural**: the marker-erase
  reject is the target of exactly **two** live rows, `qErase` on `some false` and on `none`, the
  malformed-candidate exits, and `reject_rows_unique` proves those two the only ones over all four
  states and all three symbols once both verdicts' own absorbing rows are excluded, while
  `reject_rows_routed` sends each to the composed reject `150` with the symbol written and the move
  unchanged. Neither is *taken* out of this slice's `startConfig`: `erase_first_arrival` proves the
  left block is never in its reject at any time whatever, so the composed reject is reachable only
  through the right block. The six rows of the two left verdict copies are dead, no left-block row
  targeting either verdict. The injective, disjoint block maps cover all `151` states because their
  domain sizes are `4` and `147`; together with the two block row equations in
  `table_and_resource_pins`, this accounts for every composed row and excludes right-block targets
  from the dead left copies. H8 (`16 → 19`), H9 (`19 → 22`), H10 (`25 → 28`) and H11 (six rows inside
  `[28, 56)`, all into `56`) to H17 (`137 → 140`) are inherited from G3j, its indices shifted by four,
  located by `(inTail q).val = 4 + q.val` and the universal right-block row equation.
* **The strict arrival H7 needs was already exported, and takes no hypothesis.** The marker-erase
  phase has exactly two absorbing states, `qAccept` and `qReject` — its raw states `2` and `3`, three
  rows each — so the landed `seq` routes both, as for H8, H9 and H10 and unlike H11. Unlike the
  gate's, its strict first arrival was landed in the shape `seq_handoff` consumes: the landed
  `strict_first_terminal` gives both halves against the phase's `qAccept` and `qReject`, which its own
  landed `table_and_resource_pins` identifies with `machine.accept` and `machine.reject`, and it takes
  **no hypothesis at all**. `erase_first_arrival` therefore only repackages it at
  `switchTime N = N + 3`, adds that this time **is** the phase's own landed `clock`, and adds from the
  landed `post_clock_absorption` the never-rejects consequence. The arrival is length-only, neither
  width- nor path-dependent: `N + 1` rightward steps walk the content and its trailing marker and stop
  on the first physical blank, one step left returns to the marker, and one more reads it, erases it
  and accepts.
* **What the switch hands over is exactly what G1 reads.** `gate_start_at_first_arrival` records the
  semantic dependency and executes nothing, and it needs **no hypothesis**: G1's `startConfig` is
  built field for field out of the marker-erase `finalConfig`, which the landed `run_exact` shows *is*
  the phase's run at `switchTime N` for every input. `handoff_exact` therefore takes **no hypothesis
  at all** — the first executed handoff of this chain that takes none, no tag, no width, no room, no
  budget — and concludes: no composed verdict at any time up to and **including** `N + 3` (at the
  switch time itself the control is `tailStart`, so the bound is `≤`); the composed run is the
  marker-erase phase's own run routed at every such time, as whole-`Config` equality; at exactly
  `N + 3` it **is** G3j's landed `startConfig B x w` re-embedded; and every later step is a G3j step.
  `handoff_endpoint_pins` reads that configuration back as both G3j's and G1's own `startConfig`
  projections, with the head on the boundary cell `N`, the tape the erased `contentTape`, and every
  allocated cell from `N` on blank there, the trailing marker included.
* **The inherited switches and the composed run.** `tagged_inherited_switch` locates the inherited H8
  at `N + 3 + (3 * N + 7)` at composed index `19`, `tagged_inherited_terminator_switch` the inherited
  H9 at `N + 3 + (3 * N + 7 + (zeros + 1))` at index `22`, `tagged_inherited_anchor_switch` the
  inherited H10 at `N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5)))` at index `28`, and
  `tagged_inherited_dispatcher_switch` the inherited H11 at
  `N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + C)))` at index `56`, each on exactly the head
  and tape the landed `startConfig` of that phase carries and with `C` produced existentially at or
  below G2m's deadline rather than chosen. The drained theorem takes G3j's **eight** hypotheses
  unchanged and lands the composed accept `149` at exactly
  `eraseChainClock C N zeros d v = N + 3 + gateChainClock C N zeros d v` on the separator blank
  `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally quantified and
  unsupplied, and persistence is not first arrival.
* **Two inherited rejecting branches, both forward direction only.** On a matching tag whose physical
  suffix holds no gamma terminator the whole prefix hands over and `malformed_reject_handoff` lands
  the composed reject `150` from `N + 3 + (3 * N + 7 + (N - 7))` on, on the blank boundary cell `N`
  over the erased content tape, the anchor never running. On a **mismatched** tag
  `mismatched_tag_reject_handoff` lands the composed reject `150` from `N + 3 + (3 * N + 7)` on, on
  the gate's own `finalConfig` head over that same tape, the gamma blocks never running. Neither is a
  converse, and the mismatched one is deliberately **not** timed exactly, for the reason G3j records:
  on a nonempty content the gate's own first rejection is at `3 * N + j` for its mismatch *cell* `j`,
  which this chain does not derive from `tagMatches (Fin.append x w) = false`, the value of
  `FixedContentTagGate.finalConfig`'s head being the only public trace of the `badIndex` that defines
  it. So the composed run may already be in the composed reject strictly before the time stated, and
  nothing here says when.
* **Probes.** The surface test reuses G3j's nine words. Because the marker-erase switch is
  length-only the seven well-formed words switch at `20`, `16`, `15`, `15`, `14`, `14` and `13` —
  always on the boundary cell `N`, whatever the width, and whatever the tag: `badTag` and
  `malformedWord` switch on time too: the left block scans those cells but does not test their tag,
  gamma, or bit meanings. It
  derives H7 at the widest and the narrowest fixture, both routed reject rows and the absence of any
  `qScan` row into the reject, the drain at `B = 22` after `1212` steps — `20` for the marker erasure,
  `58` for the gate, `5` for the terminator, `13` for the anchor, `18` for the dispatcher, `1098` for
  G3e — with the register value `24 > N` supplied **by hand** (an execution fixture, not an
  accepted-content one), the malformed reject at `58` and the mismatched reject at `54`; and it
  independently reduces the composed machine by kernel computation, with no slice theorem used,
  through the marker-erase walk and the erasing switch (cell `17` still `some true` at step `19` and
  `none` at step `20`), all nine H7 switches, the inherited H8, H9, H10 and H11, the inherited H12 at
  steps `132`/`133`, and the composed reject `150` at `58` on the malformed fixture and at rejection
  time `47` on `badTag`, at mismatch cell `0` — one step after a control in neither composed verdict,
  and seven steps before the `54` the theorem states.

Deferred and deliberately not claimed. **Six of the seventeen handoffs remain proof-level**: the
composed `startConfig` is the marker-erase phase's own routed into the composed control, so it still
retags the actual origin-alignment `finalConfig` and embeds every earlier phase, no raw-input
`initialConfig` is executed, and no clock counts a step of any earlier phase; `handoff_pins` records
H6 as a hypothesis-free identification and pins no earlier phase's table row. **No pnp4 bridge**: the
standalone phases' pnp4 semantics are unchanged and no `ContentVerifierBridge`, raw-input acceptance,
`AcceptsAt`, `DecidesWithin` or `UniformP` runtime theorem appears; whether the cubic budget still
dominates the composed clock is not proved here, and no advice-freedom or wrapper-level claim is made.
**No first arrival of the composed accept**: the arrivals proved are the marker-erase phase's and, as
a hypothesis, the dispatcher's, each inside its own block. **No exact time on the mismatched branch**,
as above. The **fence** is unchanged — all twelve tables are uncapped, so an oversized register still
times out; no **footprint** theorem; no **converse**, so neither composed reject implies anything
about the input. The endpoints reached are internal states out of a retagged actual prior endpoint,
neither halting on a raw input nor language acceptance. The **model connection** remains open (caveat
6 of `VERIFIER_RETARGET_PLAN.md`). Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. This is infrastructure, not P-vs-NP mainline progress,
and it makes no `P ≠ NP` claim.

**Part A G3j, the executed tag-gate → gamma-terminator handoff H8: the same sequential composition
applied a tenth time, one block further left, with no new table row and no new combinator
(infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
with its surface test. **No new table row and no landed module's code edited**; the landed generic
`UniformTM.seq` is reused unchanged and no `mergeAccept` is needed. The machine is G1's fixed
15-state, 45-row content tag gate on the left block `[0, 15)` followed by the whole landed G3i
132-state composite on `[15, 147)`, as one closed 147-state, 441-row table,
`FixedContentTagGate.machine.seq
FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `145` and reject `146`. Write `N = a+m` and `d = borrow x w zeros`. **Ten** of the
seventeen handoffs were performed by a finite table when this slice landed and **seven** remained
proof-level retags; G3k above has since executed H7 as well, taking the counts to eleven and six.

* **H8 is executed by one live routed row; the reject side is routed but not unique.** Over all
  fifteen gate states and all three symbols, with the accept's own absorbing three excluded, a
  target of the gate's accept forces the last tag state `12` on `some false` (`accept_row_unique`),
  and `seq` retargets that row to the right block's start `tailStart` at index `15`, writing
  `some false` and moving **right**, in that same transition and at no cost. The reject side differs
  from block to block: the terminator's reject took **one** live row, proved unique
  (`verdict_rows_unique`); the anchor's took **six**, each pinned individually and no uniqueness
  claimed; the gate's is the target of *many* live rows — the mismatch exits of the eight tag
  positions and the rewind's defensive rows — so no reject-row uniqueness holds, and neither it nor a
  count is claimed; rather than enumerate them, `reject_rows_routed` proves that `seq` sends every
  live row targeting the gate's reject to the composed reject `146`, symbol written and move
  unchanged.
  The six rows of the two left verdict copies are dead, no left-block row targeting either verdict.
  The injective, disjoint block maps cover all `147` states because their domain sizes are `15` and
  `132`; together with the two block row equations in `table_and_resource_pins`, this accounts for
  every composed row and excludes right-block targets from the dead left copies. H9 (`15 → 18`), H10
  (`21 → 24`) and H11 (six rows inside `[24, 52)`, all into `52`) to H17 (`133 → 136`) are inherited
  from G3i, its indices shifted by fifteen, located by `(inTail q).val = 15 + q.val` and the
  universal right-block row equation.
* **The strict arrival H8 needs was not exported, and is derived here.** The gate has exactly two
  absorbing states, `qAccept` and `qReject` — its raw states `13` and `14`, three rows each — so the
  landed `seq` routes both, as for H9 and H10 and unlike H11. Its landed `exact_terminal_contract`
  gives the strictness but lands in a private endpoint configuration, so `gate_first_arrival`
  assembles the `state = accept` form `seq_handoff` consumes from that contract and the landed
  `run_deadline`, with no room premise: on a matching tag the gate is in neither verdict before
  `switchTime N = 3 * N + 7` and in `finalConfig` at it, that time **is** its own length-only
  deadline — `gate_first_arrival` pins that identity, so nothing is lost by a running machine's
  inability to wait for a deadline — and the matching tag forces `8 ≤ N`.
* **What the switch hands over is exactly what G2 reads.**
  `terminator_start_at_first_arrival` records the semantic dependency and executes nothing, and it
  needs **no hypothesis**: G2's `startConfig` retags the gate's `finalConfig`, which the landed
  `run_deadline` shows *is* the gate's run at `switchTime N` for every input, matching tag or not.
  `handoff_exact` therefore takes the matching tag and nothing else — **one** hypothesis, one fewer
  than G3i's, no width, no room, no budget — and concludes: no composed verdict at any time up to and
  **including** `3 * N + 7` (at the switch time itself the control is `tailStart`, so the bound is
  `≤`); the composed run is G1's own run routed at every such time, as whole-`Config` equality; at
  exactly `3 * N + 7` it **is** G3i's landed `startConfig B x w` re-embedded; and every later step is
  a G3i step. `handoff_endpoint_pins` reads that configuration back as G2's own `startConfig`
  projections, with the head on the gamma cell `8`, the tape the unchanged `contentTape`, and cell
  `7` carrying the tag's own last bit `some false`.
* **The inherited switches and the composed run.** `tagged_inherited_switch` locates the inherited
  H9 at `3 * N + 7 + (zeros + 1)` at composed index `18`, `tagged_inherited_anchor_switch` the
  inherited H10 at `3 * N + 7 + (zeros + 1 + (2 * zeros + 5))` at index `24`, and
  `tagged_inherited_dispatcher_switch` the inherited H11 at
  `3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + C))` at index `52`, each on exactly the head and tape
  the landed `startConfig` of that phase carries and with `C` produced existentially at or below
  G2m's deadline rather than chosen. The drained theorem takes G3i's **eight** hypotheses unchanged
  and lands the composed accept `145` at exactly
  `gateChainClock C N zeros d v = 3 * N + 7 + terminatorChainClock C N zeros d v` on the separator
  blank `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally quantified
  and unsupplied, and persistence is not first arrival.
* **Two rejecting branches, the second new to the chain.** On a matching tag whose physical suffix
  holds no gamma terminator the gate hands over, the terminator rejects at exactly its own deadline
  `N - 7` and not before, the anchor never runs, and `malformed_reject_handoff` lands the composed
  reject `146` from `3 * N + 7 + (N - 7)` on. On a **mismatched** tag —
  `mismatched_tag_reject_handoff`, the first statement of this chain that assumes the tag does *not*
  match — the right block never runs at all and the composed reject `146` holds from the gate's
  length-only deadline `3 * N + 7` on, on the gate's own `finalConfig` head over the unchanged
  content tape. Both are forward direction only, and the mismatched one is deliberately **not**
  timed exactly. On a nonempty content the gate's own rejection *time* is `3 * N + j` for its
  mismatch *cell* `j` — with `j` the blank cell `N` itself, so `4 * N`, exactly when the word is too
  short to carry the whole tag *and* every bit it does carry already agrees with the tag prefix, a
  word with an earlier mismatch keeping that mismatch's own `3 * N + j` — and its landed
  `exact_terminal_contract` proves exactly that, strictness
  included, for a `j` characterised by the public `physicalSymbol` and `expectedTagBit`; this slice
  derives no such `j` from its single hypothesis `tagMatches (Fin.append x w) = false`, the
  `badIndex` defining it being private and its only public trace the value of `finalConfig.head`.
* **Probes.** The surface test reuses G3f's, G3g's, G3h's and G3i's eight words and adds `badTag`,
  that tag with its first bit flipped. Because the gate's switch is length-only the seven well-formed
  words switch at `58`, `43`, `40`, `40`, `37`, `46` and `43` — always on the gamma cell `8`,
  whatever the width. It derives H8 at the widest and the narrowest fixture, the drain at `B = 22`
  after `1192` steps — `58` for the gate, `5` for the terminator, `13` for the anchor, `18` for the
  dispatcher, `1098` for G3e — with the register value `24 > N` supplied **by hand** (an execution
  fixture, not an accepted-content one), the malformed reject at `44` and the mismatched reject at
  `40`; and it independently reduces the composed machine by kernel computation, with no slice
  theorem used, through the gate's rewind and tag scan, all seven H8 switches, the inherited H9, H10
  and H11, the inherited H12 at steps `112`/`113`, and the composed reject `146` at `44` on the
  malformed fixture and at rejection time `33` on `badTag`, at mismatch cell `0` — one step after a
  control in neither composed verdict, and seven steps before the length-only deadline `40` the
  theorem states.

Deferred and deliberately not claimed. **Seven of the seventeen handoffs remained proof-level** as
of this slice (G3k above has since taken H7, leaving six): the composed `startConfig` is G1's own
routed into the composed control, so it still retags the actual marker-erase `finalConfig` and
embeds every earlier phase, no raw-input `initialConfig` is executed, and no clock counts a step of
any earlier phase; `handoff_pins` records H7 as a hypothesis-free identification and pins no earlier
phase's table row. **No pnp4 bridge**: the standalone phases' pnp4 semantics are unchanged and no
`ContentVerifierBridge`, raw-input acceptance, `AcceptsAt`, `DecidesWithin` or `UniformP` runtime
theorem appears; whether the cubic budget still dominates the composed clock is not proved here, and
no advice-freedom or wrapper-level claim is made. **No first arrival of the composed accept**: the
arrivals proved are the gate's and, as a hypothesis, the dispatcher's, each inside its own block.
**No exact time on the mismatched branch**, as above. The **fence** is unchanged — all eleven tables
are uncapped, so an oversized register still times out; no **footprint** theorem; no **converse**,
so neither composed reject implies anything about the input. The endpoints reached are internal
states out of a retagged actual prior endpoint, neither halting on a raw input nor language
acceptance. The **model connection** remains open (caveat 6 of `VERIFIER_RETARGET_PLAN.md`). Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. This is infrastructure,
not P-vs-NP mainline progress, and it makes no `P ≠ NP` claim.

**Part A G3i, the executed gamma-terminator → gamma-anchor handoff H9: the same sequential
composition applied a ninth time, one block further left, with no new table row and no new
combinator (infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
with its surface test. **No new table row and no landed module's code edited**; the landed generic
`UniformTM.seq` is reused unchanged and no `mergeAccept` is needed. The machine is G2's fixed
3-state, 9-row gamma-terminator scan on the left block `[0, 3)` followed by the whole landed G3h
129-state composite on `[3, 132)`, as one closed 132-state, 396-row table,
`FixedContentGammaTerminator.machine.seq
FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `130` and reject `131`. Write `N = a+m` and `d = borrow x w zeros`. **Nine** of the
seventeen handoffs were performed by a finite table when this slice landed and **eight** remained
proof-level retags; G3j and G3k above have since executed H8 and H7 as well, taking the counts to
eleven and six.

* **H9 is executed by one live routed row, and both routed rows are proved unique.** Over all three
  terminator states and all three symbols, with the accept's own absorbing row excluded, a target of
  the terminator's accept forces `qScan` on `some true`; with the reject's own absorbing row
  excluded, a target of its reject forces `qScan` on the blank (`verdict_rows_unique`). `seq`
  retargets the first to the right block's start `tailStart` at index `3`, writing `some true` and
  staying, in that same transition and at no cost, and the second to the composed reject `131`; the
  one remaining working row, `qScan` on `some false`, stays inside the left block; and the six rows
  of the two left verdict copies are dead, no left-block row targeting either verdict. Together
  with the right-block row equation and the block disjointness `inTerminator p ≠ inTail q` — both in
  the same theorem — this accounts for every composed row. `table_and_resource_pins` pins all nine
  terminator rows in the composed control alongside the counts, the injections with their offsets,
  and the routing cases. H10 (`6 → 9`) and H11 (six rows inside `[9, 37)`, all into `37`) to H17
  (`118 → 121`) are inherited from G3h, its indices shifted by three, located by
  `(inTail q).val = 3 + q.val` and the universal right-block row equation.
* **The strict arrivals H9 needs were not exported, and are derived here.** The terminator has
  exactly two absorbing states, `qAccept` and `qReject` — its raw states `1` and `2`, three rows
  each — so the landed `seq` routes both, as for H10 and unlike H11. Its landed
  `exact_terminal_contract` gives the run at the arrival but not the `state = accept` form
  `seq_handoff` consumes, so `terminator_first_arrival` and `terminator_reject_arrival` derive both
  halves, with no room premise: on a matching tag with a decoded width the terminator is in neither
  verdict before `switchTime zeros = zeros + 1` and in `finalConfig` at it, at most its length-only
  deadline `N - 7`; with no decoded width it is in neither verdict before that deadline and in
  `finalConfig` — its `qReject` — at it.
* **What the switch hands over is exactly what G2a reads.**
  `anchor_start_at_first_arrival` records the semantic dependency and executes nothing: G2a's
  `startConfig` retags the terminator's `finalConfig`, which *is* its run at `switchTime zeros`.
  `handoff_exact` therefore takes a matching tag and a decoded width — two hypotheses, no room, no
  budget — and concludes: no composed verdict at any time up to and **including** `zeros + 1` (at
  the switch time itself the control is `tailStart`, so the bound is `≤`); the composed run is G2's
  own run routed at every such time, as whole-`Config` equality; at exactly `zeros + 1` it **is**
  G3h's landed `startConfig B x w` re-embedded; and every later step is a G3h step.
  `handoff_endpoint_pins` reads that configuration back as G2a's own `startConfig` projections, with
  the head on the gamma terminator cell `8 + zeros`, the tape the **unmarked** `contentTape`, and
  cell `7` not yet blank — the anchor's recoverable marker is written later, inside the right block.
* **The inherited switches and the composed run.** `tagged_inherited_switch` locates the inherited
  H10 at `zeros + 1 + (2 * zeros + 5)` at composed index `9`, on exactly the head and tape G2k's
  landed `startConfig` carries; `tagged_inherited_dispatcher_switch` locates the inherited H11 at
  `zeros + 1 + (2 * zeros + 5) + C` at index `37`, with `C` produced existentially at or below
  G2m's deadline rather than chosen. The drained theorem takes G3h's **eight** hypotheses unchanged
  and lands the composed accept `130` at exactly
  `terminatorChainClock C N zeros d v = zeros + 1 + anchorChainClock C N zeros d v` on the separator
  blank `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally quantified
  and unsupplied, and persistence is not first arrival. On a matching tag whose physical suffix holds
  no gamma terminator the terminator rejects at exactly its deadline `N - 7` and not before, the
  anchor never runs, and `malformed_reject_handoff` lands the composed reject `131` from that
  deadline on — forward direction only. Unlike G3h's routed reject this one **does** carry the tag
  premise: every run theorem of the terminator phase is tag-gated, because a mismatched tag leaves
  G2's `startConfig` retagging the tag gate's *rejecting* endpoint, whose head the phase does not
  characterise.
* **Probes.** The surface test reuses G3f's, G3g's and G3h's eight words. The seven well-formed ones
  switch at `1`, `2`, `3`, `3`, `3`, `3`, `5`, the inherited H10 then fires at `6`, `9`, `12`, `12`,
  `12`, `12`, `18`, and the inherited H11 at `8`, `25`, `24`, `24`, `35`, `35`, `36`. It derives H9
  at the widest and the narrowest fixture, the drain at `B = 22` after `1134` steps — `5` for the
  terminator, `13` for the anchor, `18` for the dispatcher, `1098` for G3e — with the register value
  `24 > N` supplied **by hand** (an execution fixture, not an accepted-content one), and the
  malformed reject; and it independently reduces the composed machine by kernel computation, with no
  slice theorem used, through the terminator's rightward scan, all seven H9 switches with the
  unerased cell `7` pinned at the widest of them, the inherited H10 and H11, the inherited H12 at
  steps `54`/`55`, and the composed reject `131` at the terminator's deadline `4`.

Deferred and deliberately not claimed. **Eight of the seventeen handoffs remained proof-level** at
this slice (G3j and G3k above have since taken H8 and H7, leaving six): the composed `startConfig`
is G2's own
routed into the composed control, so it still retags the actual tag-gate `finalConfig` and embeds
every earlier phase, no raw-input `initialConfig` is executed, and no clock counts a step of any
earlier phase. **No pnp4 bridge**: the standalone phases' pnp4
semantics are unchanged and no `ContentVerifierBridge`, raw-input acceptance, `AcceptsAt`,
`DecidesWithin` or `UniformP` runtime theorem appears; whether the cubic budget still dominates the
composed clock is not proved here, and no advice-freedom or wrapper-level claim is made. **No first
arrival of the composed accept**: the arrivals proved are the terminator's and, as a hypothesis, the
dispatcher's, each inside its own block. The **fence** is unchanged — all ten tables are uncapped, so
an oversized register still times out; no **footprint** theorem; no **converse**, so the composed
reject implies nothing about the input. The endpoints reached are internal states out of a retagged
actual prior endpoint, neither halting on a raw input nor language acceptance. The **model
connection** remains open (caveat 6 of `VERIFIER_RETARGET_PLAN.md`). Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. This is infrastructure,
not P-vs-NP mainline progress, and it makes no `P ≠ NP` claim.

**Part A G3h, the executed gamma-anchor → dispatcher handoff H10: the same sequential composition
applied an eighth time, one block further left, with no new table row and no new combinator
(infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
with its surface test. **No new table row and no landed module's code edited**; the landed generic
`UniformTM.seq` is reused unchanged and no `mergeAccept` is needed. The machine is G2a's fixed
6-state, 18-row gamma-anchor shuttle on the left block `[0, 6)` followed by the whole landed G3g
123-state composite on `[6, 129)`, as one closed 129-state, 387-row table,
`FixedContentGammaAnchor.machine.seq
FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`,
with accept `127` and reject `128`. Write `N = a+m` and `d = borrow x w zeros`. **Eight** of the
seventeen handoffs were then performed by a finite table and **nine** remained proof-level retags.

* **H10 is executed by one live routed row, and that row is proved unique.** Over all six anchor
  states and all three symbols, with the accept's own absorbing row excluded, a target of the
  anchor's accept forces `qReturn` on `some true` (`accept_row_unique`). `seq` retargets that row
  to the right block's start `tailStart` at index `6`, writing `some true` and staying, in that same
  transition and at no cost. Six further anchor rows route to the composed reject `128`; the marker-
  erase row and four other working rows stay inside the left block; and the six rows of the two left
  verdict copies are dead: no left-block row targets either verdict. Together with the right-block
  row equation and the block disjointness `inAnchor p ≠ inTail q` — both in the same theorem — this
  accounts for every composed row.
  `table_and_resource_pins` pins all eighteen anchor rows in the composed control alongside the
  counts, the injections with their offsets, and the routing cases. H11 (six rows inside `[6, 34)`,
  all into `34`) and H12 (`40 → 43`) to H17 (`115 → 118`) are inherited from G3g, its indices
  shifted by six, located by `(inTail q).val = 6 + q.val` and the universal right-block row
  equation.
* **The switch time is width-dependent but not path-dependent.** Unlike H11, H10 needed no new
  machinery: the anchor has exactly two absorbing states, `qAccept` and `qReject` — its raw states
  `4` and `5`, three rows each — so the landed `seq` routes both. H10 fires at the anchor's own
  strict first arrival `successTime zeros = 2 * zeros + 5`, public before this slice and carrying no
  room premise: G2a's `exact_terminal_contract` puts the anchor in neither verdict before it and in
  `finalConfig` at it, and its landed `successTime_le_deadline` bounds it by the length-only `2N`,
  so the switch adds a linear prefix to the composed clock and no new premise.
* **What the switch hands over is exactly what G2k reads.**
  `dispatcher_start_at_first_arrival` records the semantic dependency and executes nothing: G2k's
  `startConfig` retags the anchor's run at the length-only deadline `2N`, and G2a's `run_deadline`
  makes that the same run as at `successTime zeros`. `handoff_exact` therefore takes a matching tag
  and a decoded width — two hypotheses, no room, no budget — and concludes: no composed verdict at
  any time up to and **including** `2 * zeros + 5` (at the switch time itself the control is
  `tailStart`, so the bound is `≤`); the composed run is G2a's own run routed at every such time, as
  whole-`Config` equality; at exactly `2 * zeros + 5` it **is** G3g's landed `startConfig B x w`
  re-embedded; and every later step is a G3g step. `handoff_endpoint_pins` reads that configuration
  back as G2k's own `startConfig` projections, as the anchor's `markedTape`, as `none` on cell `7`
  and as the unchanged `contentTape` off it, with the head on the gamma terminator cell `8 + zeros`.
* **The inherited switch and the composed run.** `tagged_inherited_switch` locates the inherited
  H11 at `2 * zeros + 5 + C` at composed index `34`, on exactly the head and tape G2p-a's landed
  `startConfig` carries, with `C` produced existentially at or below G2m's deadline rather than
  chosen. The drained theorem takes G3g's **eight** hypotheses unchanged and lands the composed
  accept `127` at exactly
  `anchorChainClock C N zeros d v = 2 * zeros + 5 + dispatcherChainClock C N zeros d v` on the
  separator blank `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting; `v` is universally
  quantified and unsupplied, and persistence is not first arrival. On a malformed gamma the anchor
  rejects at step `1`, the dispatcher never runs, and `malformed_reject_handoff` lands the composed
  reject `128` from step one on — forward direction only, from the malformed-gamma premise alone,
  with **no** tag premise.
* **Probes.** The surface test reuses G3f's and G3g's eight words. The seven well-formed ones switch
  at `5`, `7`, `9`, `9`, `9`, `9`, `13`, and the inherited H11 then fires at `7`, `23`, `21`, `21`,
  `32`, `32`, `31`. It derives H10 at the widest and the narrowest fixture, the drain at `B = 22`
  after `1129` steps — `13` for the anchor, `18` for the dispatcher, `1098` for G3e — with the
  register value `24 > N` supplied **by hand** (an execution fixture, not an accepted-content one),
  and the malformed reject; and it independently reduces the composed machine by kernel computation,
  with no slice theorem used, through the anchor's leftward walk and its marker erase into cell `7`,
  one step before and at the switch on all seven well-formed words, the inherited H12 at steps
  `49`/`50`, and the composed reject `128` at step `1`.

Deferred and deliberately not claimed. **Nine of the seventeen handoffs remained proof-level** as of
this slice (G3i, G3j and G3k above have since taken H9, H8 and H7, leaving six): the
composed `startConfig` is G2a's own routed into the composed control, so it still retags the actual
gamma-terminator `finalConfig` and embeds every earlier phase, no raw-input `initialConfig` is
executed, and no clock counts a step of any earlier phase. **No pnp4 bridge**: the standalone
phases' pnp4 semantics are unchanged and no `ContentVerifierBridge`, raw-input acceptance,
`AcceptsAt`, `DecidesWithin` or `UniformP` runtime theorem appears; whether the cubic budget still
dominates the composed clock is not proved here, and no advice-freedom or wrapper-level claim is
made. **No first arrival of the composed accept**: the arrivals proved are the anchor's and, as a
hypothesis, the dispatcher's, each inside its own block. The **fence** is unchanged — all nine
tables are uncapped, so an oversized register still times out; no **footprint** theorem; no
**converse**, so the composed reject implies nothing about the input. The endpoints reached are
internal states out of a retagged actual prior endpoint, neither halting on a raw input nor language
acceptance. The **model connection** remains open (caveat 6 of `VERIFIER_RETARGET_PLAN.md`).
Neither `SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. This is
infrastructure, not P-vs-NP mainline progress, and it makes no `P ≠ NP` claim.

**Part A G3g, the executed dispatcher → G3e handoff H11 by accept merging: a generic table
transformation and the same sequential composition applied a seventh time, one block further left
(infrastructure only).** Two new pnp3 modules,
`Complexity.Uniform.V1.AcceptMerge` (generic) and
`Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`
(concrete), with their surface tests. **No new table row and no landed module's code edited**; one
stale sentence in G3f's module docstring and one in its surface-test docstring are corrected. The
concrete machine is G2k's fixed 28-state, 84-row payload dispatcher with its second successful
absorbing endpoint `qHasOne` merged into its `accept` `qAllZero`, followed by the whole G3e
95-state composite, as one closed 123-state, 369-row table,
`(FixedGammaPayloadDispatcher.machine.mergeAccept qHasOne).seq
FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`.
Write `N = a+m` and `d = borrow x w zeros`.

When G3f landed, H11 — G2m's payload dispatcher into G2p-a — had one blocker left: the dispatcher
has *two* non-reject absorbing outcomes, and `UniformTM.seq` routes a left `accept` and `reject`
only. G3g removes it without touching `seq` or G2k's table, and executes H11, so **seven** of the
seventeen handoffs were then performed by a finite table and **ten** remained proof-level retags.
(G3h, G3i, G3j and G3k above have since executed H10, H9, H8 and H7 as well, taking the count to
eleven and
the remainder to six; the seven-and-ten counts in this entry are the ones this slice left.)

* **The generic half is a table transformation, not a machine.** `M.mergeAccept e` keeps `M`'s
  states, `accept` and `reject`; its start and every raw row have a target `e` retargeted to
  `M.accept` (`mergeState`), with every written symbol and move untouched. With `e` neither verdict
  of `M`, `e` becomes a dead index: no merged row targets it and no merged run out of a merged
  configuration is ever in it (`mergeAccept_step_ne`, `mergeAccept_run_ne`). `mergeAccept_run`
  simulates: as long as `M` has not been in `e` before `T`, the merged run is `M`'s run re-embedded
  up to and including `T`, and at `T` both `e` and `M.accept` read back as the merged accept
  (`mergeAccept_run_accept`). `mergeAccept_seq_handoff` is then `seq_handoff` against both
  endpoints at once, with every landed `seq` lemma reused unchanged: row for row,
  `(M.mergeAccept e).seq M₂` is the table a bespoke two-success-source combinator would produce.
  Its surface test reduces a four-state literal with two success endpoints, its merge, the routed
  composition, and the unmerged composition as a negative control, which sticks in the dead left
  state.
* **H11 is executed by six live routed rows.** After the merge exactly two working-state rows of
  G2k change target — `qCursorFillOne` on the blank and `qPendingFillOne` on `true`, which aimed at
  `qHasOne` — and `seq` routes them, together with the four rows that already aimed at `qAllZero`
  (`qCursorBackFirst` and `qCursorFillVirtual` on the blank, `qZeroFillCounter` and
  `qPendingFillVirtual` on `true`), into G3e's start at composed index `28`, in that same
  transition, at no cost. `table_and_resource_pins` pins every merged row as G2k's row with its
  target merged, the two retargeted rows, `qHasOne` as no row's target, and the six routed rows. H12 (`34 → 37`), H13 (`52 → 55`), H14 (`66 → 69`), H15 (`78`/`79 → 83`),
  H16 (`102 → 105`) and H17 (`109 → 112`) are inherited from G3e by the block-offset equations and
  the universal right-block row equation.
* **The switch time is input-dependent.** Unlike every earlier handoff, H11 fires at the
  dispatcher's strict first terminal time `C` of G3f's `StrictFirstTerminalAt B x w C q`, one of
  seven path cases selected by the payload, sharing five closed forms (`1`, `2`, `3*zeros+6`,
  `pendingEndClock zeros k`, `zeroEndClock zeros`); there is no length-only formula.
  `handoff_of_first_terminal` takes that
  first arrival, `q ≠ qReject` and `C ≤ deadline N` as hypotheses and concludes: no composed
  verdict before `C`; the composed run is G2k's own run merged and routed up to and including `C`,
  with the same head and whole tape at every such time; at exactly `C` it **is** G3e's landed
  `startConfig B x w` re-embedded; and every later step is a G3e step.
  `strictFirstTerminalAt_unique` pins the arrival unique, `side_premises_of_strictFirstTerminalAt`
  derives the two side premises from a matching tag and a decoded width, and `tagged_handoff`
  packages the switch existentially from those two hypotheses alone.
* **Both outcomes route, the reject stays rejecting, and the verdict is merged exactly where the
  chain already discards it.** With `q = qAllZero` or `q = qHasOne` the merged control at `C` is
  `qAllZero` and the same row the standalone dispatcher takes is routed on the same head and tape;
  `handoff_endpoint_pins` reads
  the switch configuration back as G2p-a's own `startConfig` projections — the unchanged
  `contentTape` and the cleaned head, `7` at width zero and `6` otherwise. The composed control
  after the switch does not record which of the two the dispatcher reached; G2p-a's landed
  `retagDispatcher` keeps only head and tape, so nothing downstream ever read that verdict, and
  G2m's `qHasOne_iff`/`qAllZero_iff` remain statements about the standalone dispatcher, untouched.
  On a malformed gamma the dispatcher rejects at step `1`, the merge keeps `qReject` fixed, and
  `malformed_reject_handoff` lands the composed reject `122` from step one on, forward direction
  only.
* **The composed run.** The drained theorem takes G3e's **seven** hypotheses plus the dispatcher's
  first arrival — eight, none redundant — and lands the composed accept `121` at exactly
  `dispatcherChainClock C N zeros d v = C + bootChainClock N zeros d v` on the separator blank
  `N+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting.
* **Probes.** The surface test reuses G3f's eight words. The seven well-formed ones switch at `2`,
  `16`, `12`, `18`, `12`, `23`, `23`, three of them through the retargeted rows; the malformed word
  has no switch time at all — its first terminal is the reject at step `1`. It derives H11
  through both success endpoints (`physWord` via `qHasOne`, `oneWord` via `qAllZero`) from
  `handoff_of_first_terminal` and G3f's path theorems, the handed-over head and tape from
  `handoff_endpoint_pins`, the drain at the physical fixture at `B = 22` after `1116` steps, and the
  malformed reject; and it independently reduces the composed machine by kernel computation one
  step before and at the switch on all seven well-formed words, the inherited H12 and H13 at steps
  `36`/`37` and `68`/`69`, and the composed reject `122` at step `1`, out of configurations
  identified only through G2a's landed `run_deadline`.

Deferred and deliberately not claimed. **Ten of the seventeen handoffs remained proof-level** as of
this slice (G3h, G3i, G3j and G3k above have since taken H10, H9, H8 and H7, leaving six): this
module's
composed `startConfig` still retags the actual G2a anchor endpoint and embeds every earlier phase,
no raw-input `initialConfig` is executed, and no clock counts a step of any earlier phase. **No pnp4
bridge**: the standalone dispatcher's pnp4 semantics are unchanged and no `ContentVerifierBridge`,
raw-input acceptance, `AcceptsAt`, `DecidesWithin` or `UniformP` runtime theorem appears; whether
the cubic budget still dominates `2N² + bootChainClock` is not proved here. **No first arrival of
the composed accept**: the first arrival proved is the dispatcher's, inside the left block. The
**fence** is unchanged, so an oversized register still times out; no **footprint** theorem; no
**converse**, so the composed reject implies nothing about the input. The endpoints reached are
internal states out of a retagged actual prior endpoint, neither halting on a raw input nor
language acceptance. The **model connection** remains open (caveat 6 of
`VERIFIER_RETARGET_PLAN.md`). Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G3f, the strict first terminal arrival of the gamma-payload dispatcher: the first of the
two blockers on H11, and only that one (infrastructure only).** One new pnp3 module,
`Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival`, and its surface test. **No new
table row and no new machine**: G2k's fixed 28-state, 84-row dispatcher table is untouched, and the
only edit to a landed implementation module is one added theorem,
`FixedGammaPayloadDispatcher.first_read_exact`, which lives there because the embedding it
transports is private to that module. Write
`N = a+m`.

When G3e landed, H11 — G2m's payload dispatcher into G2p-a — had two blockers: missing
first arrival for the dispatcher's own terminal, and *two* non-reject absorbing outcomes.
G3f removes the first blocker and **nothing else**; the second stands, so the handoff count is
still **six of seventeen** and no H11 composite table exists. (Those are the count and the open
blocker this G3f slice left; G3g above has since removed the second blocker and executed H11.)

* **The terminal set is derived from the table, not chosen.** `IsTerminal q` is
  `q = qAllZero ∨ q = qHasOne ∨ q = qReject`, and `isTerminal_iff_absorbing` proves it equivalent,
  in both directions over all 28 states, to `∀ s, machine.step q s = (q, s, .stay)` — so it is
  exactly the absorbing part of the fixed table. `terminals_distinct` pins the three apart, pins
  `machine.accept = qAllZero` and `machine.reject = qReject`, and pins that `qHasOne` is neither.
  It also pins `¬ IsTerminal qCursorStart` and `¬ IsTerminal qCursorRead`, the two working
  checkpoints used in the strictness proofs.
* **Strictness is against *any* endpoint, not the path's own.** `StrictFirstTerminalAt B x w C q`
  asserts the state at `C` is `q`, that `q` is terminal, and that **no** terminal of any of the
  three occurs at any `s < C`, all on the actual `startConfig B x w` — the retagged G2a deadline
  run — and at the actual path-dependent clock. Nothing is generic in a machine, and there is no
  `Source`, `Contract` or `Provider` wrapper and no structure field.
* **Seven outcome theorems, no room premise anywhere.** Malformed gamma: `qReject` at `1`, head
  `N`, 2 hypotheses. Width zero: `qAllZero` at `2`, on its own historical head `7`, 2 hypotheses.
  First payload cell physically `true`: `qHasOne` at `3*zeros + 6`, head `6`, 5 hypotheses; the
  same cell virtual: `qAllZero` at the *same* clock, head `6`, 4 hypotheses. A `true` cell at a
  positive `k < zeros`: `qHasOne` at `pendingEndClock zeros k`, 6 hypotheses; virtual there:
  `qAllZero` at the same clock, 6 hypotheses. A payload `false` in all `zeros` cells: `qAllZero` at
  `zeroEndClock zeros`, 4 hypotheses. Here `pendingEndClock zeros k =
  2*zeros*k + 3*zeros + 5*k + 8` for `1 ≤ k`, and `zeroEndClock zeros =
  2*zeros*zeros + 8*zeros + 6` for `0 < zeros`. Each also carries the head and the tape at its
  clock. Unlike G3b, no statement needs a room premise or an additional width cutoff.
* **Four of the seven are new content; three are a repackaging, and the module says so.**
  `malformed_exact`, `zero_width_exact`, `first_true_exact` and `first_virtual_exact` carried no
  exclusion conjunct at all. G2l's `TrueExecution`/`VirtualExecution`/`ZeroExecution` bundles
  already excluded their own endpoint before the clock and the other two at every time, so for the
  two pending paths and the exhausted one the work is assembling the three into the single form.
* **The reusable step is absorption.** `run_frozen_of_terminal` freezes the whole
  configuration from a terminal onward; `no_terminal_of_le` contraposes it, so one terminal-free
  checkpoint clears every earlier time. The two `k = 0` cleanups had no intermediate checkpoint, so
  the slice adds one — the cursor read, `qCursorRead` at cell `9+zeros` at time `2*zeros + 3` — and
  closes the remaining window on a leftward head bound: the endpoint is at cell `6` at
  `3*zeros + 6`, and `zeros + 3` transitions is exactly that distance, so no terminal fits in
  between.
* **One existential over every tagged input, one direction only.** `tagged_strict_first_terminal`
  produces, from `tagMatches = true` alone, some `C ≤ deadline N = 2*N*N` and some `q` with
  `StrictFirstTerminalAt B x w C q` and `machine.run (deadline N) (startConfig B x w) =
  machine.run C (startConfig B x w)` — so G2m's deadline classification reads back verbatim at the
  first arrival and the dispatcher needs no deadline padding to be stopped. It produces a `C`; it
  states no parsed-target characterisation or converse of its tagged-input existence implication.
* **Eight probes execute the table.** `check_probe_reductions` identifies the actual
  `startConfig 0 tag ·` with G2a's landed `finalConfig` using `probe_start` and the proved
  `run_deadline` equality, which execute nothing there, and then reduces the dispatcher by kernel
  computation at eight fixtures across five content lengths (`N = 10, 11, 12, 13, 17`), reading back
  the working state one step before each clock at seven distinct states and the endpoint index
  and head at it. It appeals to none
  of the slice's theorems, so the clocks
  are cross-checked against the table and not only against the proofs; the `check_*_probe`
  wrappers separately derive the same arrivals from the theorems.

Deferred and deliberately not claimed by G3f itself. At its landing, **the second H11 blocker
stood**: `qHasOne` was still a second non-reject absorbing outcome, and `UniformTM.seq` routes the
left machine's `accept` and `reject` only, so the generic combinator did not apply to this dispatcher
unchanged. **G3g above later closes that blocker and composes H11**; no composition is built in G3f
itself. At the G3f head, **six of the seventeen** handoffs were performed by a finite table and the
eleven earlier ones remained proof-level identifications. **No new converse theorem is
stated here**: the seven path theorems run from the parsed shape to the endpoint only. G2m's
imported `qHasOne_iff` and `qReject_iff` already give endpoint converses under their respective
hypotheses; `run_deadline_eq_of_strictFirstTerminalAt` transports that classification to a strict
first-arrival clock at or below the deadline. The **fence** is unchanged — the dispatcher table
is uncapped, and this slice adds no cap. The three endpoints are internal states
reached out of a retagged actual prior endpoint: that is neither halting on a raw input nor
language acceptance, and no statement in the slice mentions `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP` membership or `ContentVerifierBridge`; no
bridge instance is constructed. The **model connection** remains open: this is a V1 `UniformTM`
on `Option Bool` cells laid out against `pairLength a m`, while `ContentVerifierBridge` asks for
the legacy `TM` with a `runTime` field on `concatBitstring x w`; caveat 6 of
`VERIFIER_RETARGET_PLAN.md` is untouched. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G3e, the executed scratch-bootstrap → G3c handoff: the same generic sequential composition
applied a sixth time, one block further left, at the same cubic budget (infrastructure only).**
One new pnp3 module,
`Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`,
and one new pnp4 module,
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`.
**No new table row**: the concrete machine is G2p-a's fixed 9-state, 27-row scratch-bootstrap table
followed by the whole G3c 86-state composite as one closed 95-state, 285-row table,
`FixedGammaTerminatorScratchBootstrap.machine.seq
FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`. Write `N = a+m`,
`zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`. (The G3d slice label is skipped here; the
preceding composite is G3c.)

Of the seventeen phase handoffs of the Part A chain, G3c executed five. G3e executes the one before
them, **H12**, so **six** of the seventeen are now performed by a finite table and **eleven** remain
proof-level retags. G3e adds **no new first-arrival theorem**: G2p-a already landed arrival,
minimality and the deadline cover in the bootstrap module — `strict_first_terminal` puts the control in
neither `qTerm` nor `qReject` at every time strictly before `exactClock N zeros = 2N - 11 - zeros`
and in `qTerm` exactly there, and `exactClock_le_deadline` holds for all `N` and `zeros` with no
premise at all — and `UniformTM.run_accept_of_le` identifies the run at the first arrival with the
run at the length-only deadline `2 * N` that G2p-b's `startConfig`, and through it G3c's, retags.
Those are exactly the landed facts the G3c entry below required; the composition itself was owed here.

* **H12 is executed by a single live routed row.** `qScanLeft` on the blank is G2p-a's *only* row
  out of a working state into its own absorbing `qTerm`, and `seq` routes it — writing `some true`,
  which is the gamma terminator the bootstrap had blanked as its return marker, and staying — to
  G3c's start at composed index `9`, in that same transition, at no cost. The three `qTerm`
  self-rows are routed too, but that state stays dead. H13 (`24 → 27`), H14 (`38 → 41`), H15 (four
  routed rows into `55`, of which `2 ≤ zeros` reaches only `50` and `51`), H16 (`74 → 77`) and H17
  (`81 → 84`) are inherited from G3c, located here by the four block-offset equations and carried
  by the universal right-block row equation, which transports every G3c row verbatim.
* **Every decoded width, in one statement, with no room premise.** Unlike every earlier handoff in
  this chain, H12 needs no width case and no room: G2p-a's first arrival is `2N - 11 - zeros` at
  *every* decoded width — the degenerate width zero differs only in the incoming G2m dispatcher
  head, `7` against `6`, which G2p-a's own trace absorbs — and `tapeLength` allocates G2p-a's
  scratch cell `N+1` for every budget including `B = 0`. So `handoff_exact` has exactly two
  hypotheses, a matching tag and a decoded width, and there is no separate width-zero theorem to
  state. An accepted parsed target (`3 ≤ pr.2.n`, hence `2 ≤ zeros`) is a sub-case.
* **The switch hands over exactly what the next phase reads.** `handoff_endpoint_pins` reads the
  configuration at the switch back semantically: its head is the restored terminator cell
  `8 + zeros` and its whole tape is G2p-a's `scratchTape B x w` — `contentTape` with `true` at the
  scratch cell `N+1` and nothing else changed — and those are *the same two projections* that
  G2p-b's own `startConfig` carries. No reinterpretation, no re-derived width, no second decoding
  crosses the block boundary.
* **The composed run, at the same three pnp4 hypotheses.** The pnp4 wrapper
  `scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock`
  takes exactly G3c's parse, acceptance and `3 ≤ pr.2.n`, at `B := polyClock 3 (pairLength a m)`,
  and derives the cap `pr.2.n ≤ N`, `11 ≤ N`, the target identity `pr.2.n = pr.1`, the tag, the
  header, `zeros = gammaZeros pr.2.n`, the width bound `2 ≤ zeros`, the switch time
  `S = 2N - 11 - zeros`, neither composed verdict before `S`, the head and tape handed over at `S`,
  the clock `C = S + firstChainClock N zeros d pr.2.n ≤ B`, the handoff itself, and the composed
  accept at `C`, at `B` and at every later time, on the separator blank `N+2+zeros` with tape
  `loopTape B x w zeros 0 pr.2.n`.
* **Probes execute the composed table, they do not restate it.** Six `*_start` lemmas identify the
  actual composed `startConfig B tag ·` with an explicit configuration using only G2m's landed
  dispatcher endpoint classification, which executes nothing; kernel reduction then reads H12 back
  in five fixtures across four widths (`N = 17` clock `19`, `N = 12` clock `11`, `N = 11` clocks
  `10` and `9`, and width zero at `N = 10`, clock `9`), reads the five inherited handoffs at steps `50`/`51`,
  `77`/`78`, `88`/`89`, `152`/`153` and `170`/`171` — G3c's steps shifted by nine states and by the
  `19` steps G2p-a takes — and reduces the routed reject. The register value `24 > N = 17` is
  supplied by hand, so the pnp3 fixture is an execution fixture and not evidence for the pnp4 cap.

Deferred and deliberately not claimed. **Six handoffs of seventeen**: the composed `startConfig`
still embeds every earlier phase — the eleven handoffs from the sentinel through G2m's dispatcher
deadline remain proof-level identifications, no `initialConfig` on a raw pair input is executed, and
no clock here counts a step of any earlier phase. Composing the next handoff down, **H11** — G2m's
dispatcher into G2p-a — is **not** in the same position, and was blocked twice over when this slice
landed: `FixedGammaPayloadDispatcherDeadline` exported the deadline-indexed endpoint classification
but no first-arrival theorem for its own terminal, so that composition needed a new first-arrival
slice first, the way G3b had to precede G3c; and the dispatcher has *two non-reject* absorbing
outcomes, `qAllZero` (its `machine.accept`) and `qHasOne`, of which `UniformTM.seq` routes only the
first, so the generic combinator does not apply to it unchanged. Part A G3f above later closed the
first blocker, and G3g now closes the second by accept merging and composes H11. The six-of-seventeen
count in this historical G3e entry is the count at G3e's landing. **First arrival of the composed
accept**: `S` is the first time H12 fires, but
nothing says `C` is the first time the composed accept is entered, since G2s-a and G2u prove no
first arrival for `qDone`; the first arrival proved here is G2p-a's, inside the left block. **The
fence**: all seven tables are unfenced, hence so is the composition; an oversized register still
runs off the end of the tape and sticks, a timeout and neither verdict. The routed reject is
exercised on a malformed gamma only: **no** rejection converse, no `RejectsAt`, and no
parsed-target rejection characterisation. **Small targets** `0`, `1`, `2` stay excluded by
`3 <= pr.2.n`. **Every converse**, a **footprint** theorem for the composite — so every room
premise of the tail is sufficient and used, never shown necessary — every witness-check phase, and
the **model connection**: this is a V1 `UniformTM` on `Option Bool` cells laid out against
`pairLength a m`, while `ContentVerifierBridge` asks for the legacy `TM` with a `runTime` field on
`concatBitstring x w`, and caveat 6 of `VERIFIER_RETARGET_PLAN.md` is untouched. The composed
accept is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior endpoint
is neither halting on a raw input nor language acceptance, and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP` membership or `ContentVerifierBridge` fact is
stated. Neither `SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced.
Infrastructure only.

**Part A G3c, the executed first-payload → G3a handoff: the same generic sequential composition
applied a fifth time, one block further left, at the same cubic budget (infrastructure only).**
One new pnp3 module,
`Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`, and
one new pnp4 module,
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`.
**No new table row**: the concrete machine is G2p-b's fixed 18-state, 54-row first-payload table
followed by the whole G3a 68-state composite as one closed 86-state, 258-row table,
`FixedGammaTargetFirstPayload.machine.seq
FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine`. Write `N = a+m`,
`zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

Of the seventeen phase handoffs of the Part A chain, G3a executed four. G3c executes the one before
them, **H13**, so **five** of the seventeen were then performed by a finite table and **twelve**
remained proof-level retags. G3c adds **no new first-arrival theorem**: Part A G3b landed G2p-b's
arrival (`first_payload_exact`, `zero_width_exact`), its minimality (`first_payload_strict`,
`zero_width_strict`) and its deadline cover (`exactClock_le_deadline`) at every decoded width, and
`UniformTM.run_accept_of_le` identifies the run at the first arrival with the run at the length-only
deadline `3 * N` that G2p-c's `startConfig`, and through it G3a's, retags. That is exactly the
premise G3a and G3b recorded as blocking this composition.

* **H13 is executed by a single live routed row.** `qSeekAnchor` on the blank is G2p-b's *only* row
  out of a working state into its own absorbing `qDone`, and `seq` routes it — writing `some false`
  and staying — to G3a's start at composed index `18`, in that same transition, at no cost. The
  three `qDone` self-rows are routed too, but that state stays dead. H14 (`29 → 32`), H15 (four
  routed rows into `46`, of which `2 ≤ zeros` reaches only `41` and `42`), H16 (`65 → 68`) and H17
  (`72 → 75`) are inherited from G3a, located here by the two block-offset equations and carried by
  the universal right-block row equation, which transports every G3a row verbatim.
* **Every decoded width, and only truthful ones.** `handoff_exact` covers the whole positive branch
  `0 < zeros`, whose first arrival is `2N + zeros - 6`; G2p-b splits its widths as `0` against
  `0 < zeros`, so no separate width-one statement exists or is needed, and an accepted parsed target
  (`3 ≤ pr.2.n`, hence `2 ≤ zeros`) is a sub-case of that branch. Inside it G2p-b's endpoint is
  extensional in its two source shapes — a physical payload cell, and a payload cell that *is* the
  boundary blank and copies the virtual zero — so both hand the same configuration over.
  `zero_width_handoff` states the same switch at width zero (first arrival `6`, no room premise);
  that width is outside every accepted target and **nothing downstream is claimed for it**.
* **The composed run, at the same three pnp4 hypotheses.** The pnp4 wrapper
  `first_payload_second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock`
  takes exactly G3a's parse, acceptance and `3 ≤ pr.2.n`, at `B := polyClock 3 (pairLength a m)`,
  and derives the cap `pr.2.n ≤ N`, `11 ≤ N`, the target identity `pr.2.n = pr.1`, the tag, the
  header, `zeros = gammaZeros pr.2.n`, the width bound `2 ≤ zeros`, the switch time
  `S = 2N + zeros - 6`, neither composed verdict before `S`, the clock
  `C = S + secondChainClock N zeros d pr.2.n ≤ B`, the handoff itself, and the composed accept at
  `C`, at `B` and at every later time, on the separator blank
  `N+2+zeros` with tape `loopTape B x w zeros 0 pr.2.n`.
* **Probes execute the composed table, they do not restate it.** Six `*_start` lemmas identify the
  actual composed `startConfig B tag ·` with an explicit configuration using only G2p-a's landed
  bootstrap endpoint theorems, which execute nothing; kernel reduction then reads H13 back in four
  positive-width fixtures across three widths and at width zero (`N = 17` clock `32`, `N = 12` clock `20`, `N = 11` clock `18`
  on the virtual source, `N = 11` clock `17`, and the length-free `6`), reads the four inherited
  handoffs at steps `58`/`59`, `69`/`70`, `133`/`134` and `151`/`152` — G3a's `26`/`27`, `37`/`38`,
  `101`/`102` and `119`/`120` shifted by the `32` steps G2p-b takes — and reduces the routed reject.
  The register value `24 > N = 17` is supplied by hand, so the pnp3 fixture is an execution fixture
  and not evidence for the pnp4 cap.

Deferred and deliberately not claimed. **Five handoffs of seventeen**: the composed `startConfig`
still embeds every earlier phase — the twelve handoffs from the sentinel through G2p-a's bootstrap
remain proof-level identifications, no `initialConfig` on a raw pair input is executed, and no clock
here counts a step of any earlier phase. Composing the next handoff down — G2p-a's bootstrap into
G2p-b — needs no new first-arrival theorem either: G2p-a's `strict_first_terminal` and
`exactClock_le_deadline` are landed, so what is owed there is that composition itself; Part A G3e
above has since built it, taking the count to six, so the counts in this G3c entry are the ones
this slice left. **First arrival of the composed accept**: `S` is the first time H13 fires, but nothing says `C` is the first
time the composed accept is entered, since G2s-a and G2u prove no first arrival for `qDone`; the
first arrival proved here is G2p-b's, inside the left block. **The fence**: all six tables are
unfenced, hence so is the composition; an oversized register still runs off the end of the tape and
sticks, a timeout and neither verdict. The routed reject is exercised on a malformed gamma only:
**no** rejection converse, no `RejectsAt`, and no parsed-target rejection characterisation. **Small
targets** `0`, `1`, `2` stay excluded by `3 <= pr.2.n`, and width zero gets the switch and nothing
else. **Every converse**, a **footprint** theorem — so every room premise is sufficient and used,
never shown necessary — every witness-check phase, and the **model connection**: this is a V1
`UniformTM` on `Option Bool` cells laid out against `pairLength a m`, while `ContentVerifierBridge`
asks for the legacy `TM` with a `runTime` field on `concatBitstring x w`, and caveat 6 of
`VERIFIER_RETARGET_PLAN.md` is untouched. The composed accept is the countdown's phase-local
`qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw input nor
language acceptance, and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation`,
`NP` membership or `ContentVerifierBridge` fact is stated. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G3b, the exact first arrival of the first-payload phase: the prerequisite the next
sequential composition was missing (infrastructure only).** No new module, no new machine and no new
table row. The fixed 18-state, 54-row `FixedGammaTargetFirstPayload` table is untouched and every
signature it already exported is unchanged; the slice adds theorems to that module, its surface test
and the pnp3 axiom audit. Write `N = a+m`.

G3a recorded that composing G2p-b's first payload digit into G2p-c was blocked because G2p-b
exported only its length-only deadline `3*N` and no first-arrival theorem, so
`UniformTM.seq_handoff`'s minimality premise could not be discharged. G3b supplies exactly that
premise for this concrete machine, and nothing else.

* **The clock is derived from the fixed table, not chosen.** `exactClock N zeros` is `6` at width
  zero — the run blanks the terminator, walks back to tag cell `6`, blanks the anchor at `7`, finds
  the marker directly after it, restores both and halts, at every length — and `2*N + zeros - 6` at
  a positive width, where the head additionally walks out to the target cell `N+2` and back to the
  anchor. `malformedExactClock` is `1`. `exactClock_le_deadline`, under the width bound
  `9+zeros <= N` that the gamma contract already supplies for a decoded width, places every decoded
  width at or below the landed deadline, and the five `*_at_deadline` endpoints are now derived from
  the exact ones rather than proved a second time.
* **Both directions, at every reachable shape.** `first_payload_exact` holds from
  `exactClock N zeros` on, under the same room premise `a+m+2 < tapeLength (pairLength a m) B` the
  landed endpoint already used, and `first_payload_strict` puts the control in neither `qDone` nor
  `qReject` at every strictly earlier time — read off the fixed schedule, not off absorption — so
  the clock is a *first* arrival and not merely a time by which the run has halted.
  `first_physical_exact` and `first_virtual_exact` name the two positive-width source shapes at that
  time, and `zero_width_exact`/`zero_width_strict` and `malformed_exact`/`malformed_strict` do the
  same for width zero and for a malformed gamma, which has no decoded width at all.
* **The premise shape a sequential composition consumes.** `strict_first_terminal` bundles, on any
  decoded width and assuming room only when that width is positive: neither verdict before
  `exactClock N zeros`, `machine.accept` exactly there, `exactClock N zeros <= deadline N`, and the
  identification of the configuration there with the configuration at the deadline — the one
  G2p-c's `startConfig` retags. The last conjunct is absorption, not a second run.
* **Five reduction probes execute the machine.** Each identifies the *actual* `startConfig B tag ·`
  with an explicit configuration for every budget, using only G2p-a's landed endpoint theorems,
  which execute nothing; it then reduces this phase's own run at `B = 0` by kernel computation, at
  the exact clock and one step before it. The shapes are: a physical payload cell with bit `1` and
  with bit `0` (`zeros = 1`, `N = 11`, clock `17`); a physical payload cell at `zeros = 3`
  (`N = 13`, clock `23`), which moves both the length and the width term; the virtual source
  `9+zeros = N` (`zeros = 2`, `N = 11`, clock `18`), the largest width that length can decode; width
  zero at its own extreme `9 = N` (clock `6`), where the target cell is left blank; and a malformed
  gamma (clock `1`). No probe appeals to the theorem it checks.

Deferred and deliberately not claimed. **No composition is built here**: G3b states no `seq`, no
composed machine, no composed clock and no new handoff, so **four of the seventeen** handoffs were
still the ones performed by a finite table when this slice landed and the thirteen earlier ones
remained proof-level identifications. What blocked that composition was then the composition itself,
not a missing premise; Part A G3c above has since built it, and Part A G3e above has since taken
H12 as well, so the count is now six and the counts in this G3b entry are the ones this slice left.
**No converse**: nothing says that `qDone` at the exact clock implies a positive width, nor that
`qReject` implies a malformed gamma, and no theorem covers a positive width without room. The
**fence** is unchanged — the table is uncapped, and this slice adds no cap. `qDone` is an internal
endpoint reached out of a retagged actual prior endpoint: that is neither halting on a raw input nor
language acceptance, and the module states no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`,
`VerifiesRelation`, `NP` membership or `ContentVerifierBridge` fact. Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G3a, the executed second-payload → G2z handoff: the same generic sequential composition
applied a fourth time, one block further left, at the same cubic budget (infrastructure only).**
One new pnp3 module,
`Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown`, and one new
pnp4 module,
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownBridge`.
**No new table row**: the concrete machine is G2p-c's fixed 14-state, 42-row second-payload table
followed by the whole G2z 54-state composite as one closed 68-state, 204-row table,
`FixedGammaTargetSecondPayload.machine.seq FixedGammaTargetMarkersLoopDecrementCountdown.machine`.
Write `N = a+m`, `zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

Of the seventeen phase handoffs of the Part A chain, G2z executed three. G3a executes the one
before them, **H14**, so **four** of the seventeen were then performed by a finite table and
**thirteen** remained proof-level retags. G3a adds **no new first-arrival theorem**: G2p-c's arrival
(`second_payload_exact`, `zero_width_exact`, `width_one_exact`), its minimality
(`second_payload_strict`, `zero_width_strict`, `width_one_strict`) and its deadline cover
(`exactClock_le_deadline`) are landed at every decoded width, and `UniformTM.run_accept_of_le`
identifies the run at the first arrival with the run at the length-only deadline `2 * N` that
G2p-d's marker `startConfig`, and through it G2z's, retags.

* **H14 is executed by a single live routed row.** `qScanLeft` on the blank is G2p-c's *only* row
  out of a working state into its own absorbing `qDone`, and `seq` routes it — together with the
  three dead `qDone` self-rows — to G2z's start at composed index `14`, writing `some false` and
  staying, at no cost. The routed row restores the blanked anchor at cell `7` in the very
  transition that crosses the block boundary. H15 (`23 -> 28` through `qClearB`, `24 -> 28` through
  `qBackB`), H16 (`47 -> 50`) and H17 (`54 -> 57`) are inherited from G2z, pinned here by composed
  index; their rows are transported verbatim by the universal right-block row equation from G2z's
  own audited pins rather than restated. `check_inherited_handoff_probe` reduces concretely the
  `qClearB` row `23 -> 28`, H16 and H17; the `qBackB` row `24 -> 28` is carried by that universal
  row equation and G2z's own probes, and no fixture here reaches it.
* `FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.handoff_exact` (four: matching tag,
  decoded width, `2 <= zeros`, and G2p-c's own room `N + 3 < tapeLength (pairLength a m) B`, which
  is `room_iff`'s `2 <= a + B` on both sides of the switch): out of the composed `startConfig` —
  G2p-c's own `startConfig`, the retagged *actual* G2p-b first-payload endpoint, routed — the
  composed run is G2p-c's run up to `S = FixedGammaTargetSecondPayload.exactClock N zeros
  = 2 * N - 7`, is in neither composed verdict before `S`, at exactly `S` **is** G2z's landed
  `startConfig B x w` re-embedded, and every later step is a G2z step. The switch fires at G2p-c's
  **first arrival**, not at its length-only deadline `deadline N = 2 * N`, at which G2p-d's marker
  `startConfig` retags. Unlike G2z's, this switch time is **length-dependent**. The conclusion is
  extensional in G2p-c's three source shapes — a physical source `10 + zeros < N`, the source
  address on the boundary blank `10 + zeros = N`, and the first payload cell already on the
  boundary `9 + zeros = N`, which bypasses `qRead` — so all three hand over the same configuration
  and no shape premise appears.
* `zero_width_handoff` (two: matching tag, decoded width zero; **no** room premise) and
  `width_one_handoff` (three: matching tag, decoded width one, G2p-b's weaker room
  `N + 2 < tapeLength (pairLength a m) B`) state the same switch at the two degenerate decoded
  widths, whose first arrivals are the length-free `3` and `5`. Both are **outside** every accepted
  parsed target, since `3 <= pr.2.n` forces `2 <= gammaZeros pr.2.n`; nothing downstream is claimed
  for them, and neither width leaves a net write — the tag cell `7` is blanked and restored, and
  what G2p-c exports at these widths is a tape equality with the incoming tape, not a footprint — so
  G2z starts on the tape it was handed.
* `FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.second_payload_markers_loop_decrement_countdown_drained`
  (G2u's, G2y's and G2z's **seven** hypotheses, unchanged; `v` universally quantified): at exactly
  `secondChainClock N zeros d v = FixedGammaTargetSecondPayload.exactClock N zeros
  + markersChainClock N zeros d v` the composed machine is in its accept — the countdown's `qDone` —
  on the separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`, persisting. There is
  **no** eighth room premise: G2p-c's room is `room_iff`'s `2 <= a + B`, read off the drain's own
  room premise `zeros + 2 + F <= a + B` together with `2 <= zeros`, and derived inside the proof.
* `FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.malformed_reject_handoff` (two:
  matching tag, no decoded width): from step one on, the composed machine is in the **composed**
  reject (index `67`, not G2p-c's own `qReject` at `13` nor G2z's at `53`) at the boundary head `N`
  on the unchanged content tape. It transports G2p-c's landed `malformed_exact` forward only; it is
  no converse — nothing says the composed reject implies a malformed gamma — and characterises no
  parsed target.
* `second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock` (exactly
  G2z's **three**: the parse, the acceptance, `3 <= pr.2.n`; no tag, cap, room, budget, clock,
  width, digit, initial-state, correctness or runtime premise): at the same
  `B := polyClock 3 (pairLength a m)` the chained clock
  `C = FixedGammaTargetSecondPayload.exactClock N zeros + markersChainClock N zeros d pr.2.n` is at
  most `B`, the handoff facts are re-exported — `S = 2 * N - 7`, no composed verdict before `S`, and
  at exactly `S` G2z's landed `startConfig B x w` re-embedded — and at exactly `C`, at exactly `B`
  and at every later time the composed machine is in its accept with tape
  `loopTape B x w zeros 0 pr.2.n`, with `pr.2.n = pr.1` and `11 <= N` exported. The target tracked
  throughout is the parsed `pr.2.n`, the field `ContentAccepts` reads, never a header or index
  substitute. The new arithmetic is
  `C <= (2N - 7) + (zeros + 7) + 3N² + (3N² + 12N + 7) <= (N+1)³ + 3`, whose proof uses `11 <= N`;
  G2z's own domination lemma is private and supplies no slack for the extra `2N - 7`, so the public
  clock formulas are expanded rather than reused.
* Non-vacuity:
  `probe_second_payload_markers_loop_decrement_countdown_polyClock_accepted_target_three` reuses
  G2w-b's accepted word at the pinned target `3`, whose canonical width `gammaZeros 3 = 2` selects
  the positive-width branch, and reads back no composed verdict before `2 * N - 7`, G2z's
  `startConfig` at `2 * N - 7`, and the composed accept at `B`. Unlike G2z's literal `9`, that
  switch time is **length-dependent**, so the probe pins it by the closed formula together with the
  exported `11 <= N` rather than by a numeral. On the pnp3 side `check_second_handoff_instance`
  inhabits the four hypotheses at all three positive source shapes (`zeros = 4`, `2`, `2` at
  `N = 17`, `12`, `11`), `check_degenerate_handoff_instance` the premises of the two degenerate
  widths (`zeros = 0` at `N = 10`, `zeros = 1` at `N = 11`) and `check_second_drained_instance` the
  seven at `B = 22`; `check_h14_probe_physical`, `check_h14_probe_middle`, `check_h14_probe_tight`
  and `check_h14_probe_degenerate` reduce the composed run out of the identified actual
  `startConfig 0 tag ·` through that one routed row at steps `26`/`27`, `16`/`17`, `14`/`15`,
  `2`/`3` and `4`/`5`, `check_inherited_handoff_probe` reads H15 at steps `37`/`38`, H16 at
  `101`/`102` and H17 at `119`/`120` — G2z's `10`/`11`, `74`/`75` and `92`/`93` shifted by the `27`
  steps G2p-c takes — and `check_malformed_probe` reduces the routed reject. The register value
  `24 > N = 17` is supplied by hand, so the pnp3 fixture is an execution fixture and not evidence
  for the pnp4 cap.

Deferred and deliberately not claimed. **Four handoffs of seventeen**: the composed `startConfig`
still embeds every earlier phase — the thirteen handoffs from the sentinel through G2p-b's first
payload remain proof-level identifications, no `initialConfig` on a raw pair input is executed, and
no clock here counts a step of any earlier phase. Composing the next handoff down — G2p-b's first
payload into G2p-c — was **blocked on a missing first-arrival theorem** when this slice landed:
G2p-b exported its endpoint at its deadline but no `first_payload_strict`, as recorded under G2x
below. Part A G3b above has since supplied that premise and Part A G3c above has since executed that
handoff as H13, and Part A G3e above has since executed H12 as well, taking the count to six, so
the counts in this G3a entry are the ones this slice left. **First arrival of the
composed accept**: `S` is the first time H14 fires, but nothing says `C` is the first time the
composed accept is entered, since G2s-a and G2u prove no first arrival for `qDone`; the first
arrival proved here is G2p-c's, inside the left block. **The fence**: all five tables are unfenced,
hence so is the composition; an oversized register still runs off the end of the tape and sticks, a
timeout and neither verdict. The routed reject is exercised on a malformed gamma only: **no**
rejection converse, no `RejectsAt`, and no parsed-target rejection characterisation. **Small
targets** `0`, `1`, `2` stay excluded by `3 <= pr.2.n`, and the two degenerate widths get the switch
and nothing else. **Every converse**, a **footprint** theorem — so every room premise is sufficient
and used, never shown necessary — every witness-check phase, and the **model connection**: this is a
V1 `UniformTM` on `Option Bool` cells laid out against `pairLength a m`, while
`ContentVerifierBridge` asks for the legacy `TM` with a `runTime` field on `concatBitstring x w`,
and caveat 6 of `VERIFIER_RETARGET_PLAN.md` is untouched. The composed accept is the countdown's
phase-local `qDone`; reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance, and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`,
`VerifiesRelation`, `NP` membership, advice-freedom claim or `ContentVerifierBridge` is stated.
Neither `SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure
only.

**Part A G2z, the executed marker-preamble → G2y handoff: the same generic sequential composition
applied a third time, one block further left, at the same cubic budget (infrastructure only).**
One new pnp3 module, `Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown`, and one
new pnp4 module,
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetMarkersLoopDecrementCountdownBridge`.
**No new table row**: the concrete machine is G2p-d's fixed 14-state, 42-row marker-preamble table
followed by the whole G2y 40-state composite as one closed 54-state, 162-row table,
`FixedGammaTargetPayloadLoopFoundation.machine.seq FixedGammaTargetLoopDecrementCountdown.machine`.
Write `N = a+m`, `zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

Of the seventeen phase handoffs of the Part A chain, G2y executed two. G2z executes the one before
them, **H15**, so **three** of the seventeen are performed by a finite table as of this slice and
**fourteen** remain proof-level retags; H14, H13 and H12 have since been taken by G3a, G3c and G3e
above, so the current counts are six and eleven. G2z adds **no new first-arrival theorem**: the preamble's arrival with
persistence (`markers_installed`), its minimality (`markers_strict`) and its deadline cover
(`exactClock_le_deadline`) are all landed, and `UniformTM.run_accept_of_le` identifies the run at
the first arrival with the run at the length-only deadline `N` that G2p-d's round `startConfig`,
and through it G2y's, retags.

* `FixedGammaTargetMarkersLoopDecrementCountdown.handoff_exact` (four: matching tag, decoded width,
  `2 <= zeros`, and the **foundation's** weaker room `N + 3 < tapeLength (pairLength a m) B`, not
  G2y's loop room): out of the composed `startConfig` — the marker preamble's own `startConfig`, the
  retagged *actual* G2p-c second-payload endpoint, routed — the composed run is the preamble's run
  up to `S = exactClock zeros = zeros + 7`, is in neither composed verdict before `S`, at exactly
  `S` **is** G2y's landed `startConfig B x w` re-embedded, and every later step is a G2y step. The
  switch fires at the preamble's **first arrival**, not at its length-only deadline `deadline N = N`,
  at which G2p-d's round `startConfig` retags. Because the room premise is the preamble's, the
  simulation holds even where the tail would later lack room.
* **H15 is executed by four routed rows.** All four working-state preamble rows targeting `qDone` —
  `qZeroA`/`some true`, `qClearB`/`some true`, `qBackB`/`some true`, `qFin`/`some false` — are
  routed to G2y's `qLoop` at composed index `14`, and so are the three dead `qDone` self-rows. The
  table reaches `qZeroA`'s exit only on a terminator already at cell `8` (width zero) and `qFin`'s
  only on one at cell `9` (width one), both excluded by `2 <= zeros`; the remaining two are the ones
  `qSrcB` selects by reading the second payload source, a content symbol taking `qClearB` (index
  `9`, write blank and move right) and the boundary blank taking `qBackB` (index `10`, preserve
  `true` and stay). No theorem here says which row a given word takes. H16 (`33 -> 36`) and H17
  (`40 -> 43`) are inherited from G2y and re-derived through the right-block row equation.
* `FixedGammaTargetMarkersLoopDecrementCountdown.markers_loop_decrement_countdown_drained` (G2u's
  and G2y's **seven** hypotheses, unchanged; `v` universally quantified): at exactly
  `markersChainClock N zeros d v = exactClock zeros + chainClock N zeros d v` the composed machine
  is in its accept — the countdown's `qDone` — on the separator blank `N + 2 + zeros` with tape
  `loopTape B x w zeros 0 v`, persisting. There is **no** eighth room premise: the preamble's room
  is `room_iff`'s `2 <= a + B`, read off the drain's own room premise `zeros + 2 + F <= a + B`
  together with `2 <= zeros`, and derived inside the proof.
* `FixedGammaTargetMarkersLoopDecrementCountdown.malformed_reject_handoff` (two: matching tag, no
  decoded width): from step one on, the composed machine is in the **composed** reject (index `53`,
  not the preamble's own `qReject` at `13`) at the boundary head `N` on the unchanged content tape.
  This is the first **routed reject** the chain composition exercises. It is no converse — nothing
  says the composed reject implies a malformed gamma — and characterises no parsed target.
* `markers_loop_decrement_countdown_drained_accepted_content_at_polyClock` (exactly G2y's **three**:
  the parse, the acceptance, `3 <= pr.2.n`; no tag, cap, room, budget, clock, width, digit,
  initial-state, correctness or runtime premise): at the same `B := polyClock 3 (pairLength a m)`
  the chained clock `C = exactClock zeros + chainClock N zeros d pr.2.n` is at most `B`, the handoff
  facts are re-exported — no composed verdict before `S`, and at exactly `S` G2y's landed
  `startConfig B x w` re-embedded — and at exactly `C`, at exactly `B` and at every later time the
  composed machine is in its accept with tape `loopTape B x w zeros 0 pr.2.n`, with `pr.2.n = pr.1`
  and `11 <= N` exported. The new arithmetic is
  `C <= (zeros + 7) + 3N² + (3N² + 12N + 7) <= (N+1)³ + 3`, whose proof uses `11 <= N`; G2y's own
  domination lemma is private and supplies no slack for the extra `zeros + 7`, so the public clock
  formulas are expanded rather than reused.
* Non-vacuity: `probe_markers_loop_decrement_countdown_polyClock_accepted_target_three` reuses
  G2w-b's accepted word at the pinned target `3`, whose canonical width `gammaZeros 3 = 2` pins the
  switch at the literal `9` rather than an existential time, and reads back no composed verdict
  before `9`, G2y's `startConfig` at `9`, and the composed accept at `B`. On the pnp3 side
  `check_markers_handoff_instance` inhabits the four hypotheses at all three source shapes
  (`zeros = 4`, `2`, `2` at `N = 17`, `12`, `11`) and `check_markers_drained_instance` the seven at
  `B = 22`; `check_h15_probe_physical`, `check_h15_probe_middle` and `check_h15_probe_tight` reduce
  the composed run out of the identified actual `startConfig 0 tag ·` through those two H15 rows by
  kernel computation, `check_inherited_handoff_probe` reads H16 at steps `74`/`75` and H17 at
  `92`/`93` — G2y's `63`/`64` and `81`/`82` shifted by the preamble's `11` steps — and
  `check_malformed_probe` reduces the routed reject. The register value `24 > N = 17` is supplied by
  hand, so the pnp3 fixture is an execution fixture and not evidence for the pnp4 cap.

Deferred and deliberately not claimed. **Three handoffs of seventeen** as of this slice: the
composed `startConfig` still embeds every earlier phase — the fourteen handoffs from the sentinel
through G2p-c's second payload remain proof-level identifications, no `initialConfig` on a raw pair
input is executed, and no clock here counts a step of any earlier phase. Composing the next handoff
down — G2p-c's second payload into the preamble — needs no new first-arrival theorem either, since
`second_payload_strict` is landed; that handoff, H14, has since been taken by G3a above, so the
counts in this G2z entry are the ones this slice left. Below that, G2p-b's first arrival was still
missing when this slice landed, as recorded under G2x below; Part A G3b above has since supplied
it. **First arrival of the composed accept**: `S` is the first time H15 fires, but
nothing says `C` is the first time the composed accept is entered; the first arrival proved here is
the marker preamble's, inside the left block. **The fence**: all four tables are unfenced, hence so
is the composition; an oversized register still runs off the end of the tape and sticks, a timeout
and neither verdict. The routed reject is exercised on a malformed gamma only: **no** rejection
converse, no `RejectsAt`, and no parsed-target rejection characterisation. **Small targets** `0`,
`1`, `2` stay excluded by `3 <= pr.2.n`. **Every converse**, a **footprint** theorem — so every room
premise is sufficient and used, never shown necessary — every witness-check phase, and the **model
connection**: this is a V1 `UniformTM` on `Option Bool` cells laid out against `pairLength a m`,
while `ContentVerifierBridge` asks for the legacy `TM` with a `runTime` field on
`concatBitstring x w`, and caveat 6 of `VERIFIER_RETARGET_PLAN.md` is untouched. The composed accept
is the countdown's phase-local `qDone`; reaching it out of a retagged actual prior endpoint is
neither halting on a raw input nor language acceptance, and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP` membership, advice-freedom claim or
`ContentVerifierBridge` is stated. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G2y, the executed payload-loop → G2x handoff: the same generic sequential composition
applied a second time, one block further left, at the same cubic budget (infrastructure only).**
One new pnp3 module, `Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown`, and one new
pnp4 module, `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetLoopDecrementCountdownBridge`.
**No new table row**: the concrete machine is G2p-d's fixed 22-state, 66-row payload-round table
followed by the whole G2x 18-state composite as one closed 40-state, 120-row table,
`FixedGammaTargetPayloadRound.machine.seq FixedGammaTargetDecrementCountdown.machine`. Write
`N = a+m`, `zeros = gammaZeros pr.2.n` and `d = borrow x w zeros`.

Of the seventeen phase handoffs of the Part A chain, G2x executed the last one. G2y executes the
one before it, **H16**, and inherits G2x's as **H17**, so **two** of the seventeen were then performed
by a finite table and fifteen remained proof-level retags.

* `FixedGammaTargetLoopDecrementCountdown.loop_strict` (four: matching tag, decoded width,
  `2 <= zeros`, G2p-e's room): the payload-round machine, out of its own `startConfig`, is not in
  `qDone` at any time strictly before `totalClock N zeros`. This is the first-arrival fact G2x
  recorded as missing, and it needs no new trace: at `loopClock N zeros` G2p-e's `register_complete`
  puts the machine in the non-absorbing `qLoop`, `no_terminal_of_le` turns that single non-verdict
  into "neither verdict at any earlier time", and above that time `run_add` reduces to the finish,
  where G2p-f's `exhaust_strict` already excludes `qDone` before `exhaustClock N zeros`. Arrival
  itself is G2p-f's `payload_exhausted`; only minimality is new.
* `FixedGammaTargetLoopDecrementCountdown.handoff_exact` (the same four): out of the composed
  `startConfig` — the payload round's own `startConfig`, the retagged *actual* G2p-d foundation
  endpoint, routed — the composed run is that machine's run up to `T = totalClock N zeros`, is in
  neither composed verdict before `T`, at exactly `T` **is** G2x's landed `startConfig B x w`
  re-embedded, and every later step is a G2x step. The switch fires at the loop's **first arrival**,
  not at G2q's length-only deadline `priorDeadline N = 3N²`, at which G2q's `startConfig` retags;
  the head and whole tape are identified through the round machine's persistence between the two
  times, via `prior_covers`.
* `FixedGammaTargetLoopDecrementCountdown.loop_decrement_countdown_drained` (G2u's **seven**
  hypotheses, unchanged; `v` universally quantified): at exactly
  `chainClock N zeros d v = totalClock N zeros + composedClock N zeros d v` the composed machine is
  in its accept — the countdown's `qDone` — on the separator blank `N + 2 + zeros` with tape
  `loopTape B x w zeros 0 v` — one tape equality, which already fixes the cleared register and the
  `v` marks — persisting. There is **no**
  eighth room premise: the decrement's room is G2u's `lane_room` at `r = k = 0` and the loop's
  weaker room is `room_iff`'s second conjunct on it, both derived inside the proof.
* `loop_decrement_countdown_drained_accepted_content_at_polyClock` (exactly G2x's **three**: the
  parse, the acceptance, `3 <= pr.2.n`; no tag, cap, room, budget, clock, width, digit,
  initial-state, correctness or runtime premise): at the same `B := polyClock 3 (pairLength a m)`
  the chained clock `C = totalClock N zeros + composedClock N zeros d pr.2.n` is at most `B`, the
  same two handoff facts are re-exported — no composed verdict before `T = totalClock N zeros`, and
  at exactly `T` G2x's landed `startConfig B x w` re-embedded — and at exactly `C`, at exactly `B`
  and at every later time the composed machine is in its accept with tape
  `loopTape B x w zeros 0 pr.2.n`, with `pr.2.n = pr.1` and `11 <= N` exported. The new arithmetic
  is `C <= 3N² + (3N² + 12N + 7) <= (N+1)³ + 3`, whose proof uses `11 <= N`; G2x's own domination lemma
  is private, so the public clock formulas are expanded rather than reused.
* Non-vacuity: `probe_loop_decrement_countdown_polyClock_accepted_target_three` reuses G2w-b's
  accepted word at the pinned target `3` and reads back a switch time `T <= B`, no composed verdict
  before it, G2x's `startConfig` at it, and the composed accept at `B`; on the pnp3 side
  `check_loop_handoff_instance` and `check_loop_drained_instance` inhabit the four and the seven
  hypotheses at their own budgets (`B = 0` and `B = 22`), and `check_handoff_probe` reduces the
  composed run out of the identified actual `startConfig 0 tag physWord` by kernel computation
  through **both** cross-block edges: the loop's `qFin` (index `19`) on the tag cell `7` at step
  `63`, G2q's `qStart` (index `22`) on that cell at step `64`, G2q's `qBorrow` (index `26`) on the
  digit `22` at step `81`, and the countdown's `qStart` (index `29`) on it at step `82`.

Deferred and deliberately not claimed. **Two handoffs of seventeen**: the composed `startConfig`
still embeds every earlier phase — the fifteen handoffs from the sentinel through the payload loop
foundation remain proof-level identifications, no `initialConfig` on a raw pair input is executed,
and no clock here counts a step of any earlier phase. Composing the next handoff down — G2p-d's
marker foundation into the payload round — needs no new first-arrival theorem: the foundation's
`markers_strict`, `markers_installed` and `exactClock_le_deadline` are the same three ingredients
`loop_strict`, `payload_exhausted` and `prior_covers` supply here; that handoff, H15, has since been
taken by G2z above, so the count of proof-level retags below is the one this slice left. Further
down, G2p-b's first arrival was still missing when this slice landed, as recorded under G2x below;
Part A G3b above has since supplied it. **First arrival
of the composed accept**: `T` is the first time H16 fires, but nothing says `C` is the first time
the composed accept is entered, since G2s-a and G2u prove no first arrival for `qDone`; the first
arrival proved here is the payload loop's, inside the left block. **The fence**: all three tables
are unfenced, hence so is the composition; an oversized register still runs off the end of the tape
and sticks, a timeout and neither verdict, and the rows routed to the composed reject are pinned but
not exercised here: no rejecting run or malformed-gamma rejection is composed in this slice, though
the round machine's `malformed_rejects` with `seq_reject_handoff` would give one. **Small targets**
`0`, `1`, `2` stay excluded by `3 <= pr.2.n`. **Every converse**,
a **footprint** theorem — so every room premise is sufficient and used, never shown necessary —
every witness-check phase, and the **model connection**: this is a V1 `UniformTM` on `Option Bool`
cells laid out against `pairLength a m`, while `ContentVerifierBridge` asks for the legacy `TM` with
a `runTime` field on `concatBitstring x w`. The composed accept is the countdown's phase-local
`qDone`; reaching it out of a retagged actual prior endpoint is neither halting on a raw input nor
language acceptance, and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation`,
`NP` membership, advice-freedom claim or `ContentVerifierBridge` is stated. Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G2x, the executed G2q → G2s-a handoff: a generic sequential composition of two fixed
`UniformTM`s, applied once, at G2w-b's cubic budget (infrastructure only).**
Two new pnp3 modules, `Complexity.Uniform.V1.SequentialComposition` and
`Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown`, and one new pnp4 module,
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetDecrementCountdownBridge`. **No new table
row**: the concrete machine is G2q's fixed 7-state, 21-row table followed by G2s-a's fixed 11-state,
33-row table as one closed 18-state, 54-row table, `FixedGammaTargetRegisterDecrement.machine.seq
FixedGammaTargetUnaryCountdown.machine`. Write `N = a+m`, `zeros = gammaZeros pr.2.n` and
`d = borrow x w zeros`.

Until now every one of the seventeen phase handoffs of the Part A chain was a proof-level retag:
each phase's `startConfig` replaces the control of the previous phase's run at a length-only
deadline, and no finite table performs a control switch. G2x builds the switch for one of them.

* `UniformTM.seq M₁ M₂` (generic, imports only `Machine`): `M₁`'s states at their own indices,
  `M₂`'s shifted past them, the raw table the disjoint union of the two public step functions with
  every `M₁` row **routed** — a target `M₁.accept` becomes `M₂.start` *in that same transition*, a
  target `M₁.reject` the composed reject. This is the routed-edge handoff of the P2-3cB2
  parser/verifier constructor with the left component made generic; it costs **zero** steps, and
  routing inspects a row's target state and nothing else. `seq_run_right` (no hypothesis) runs `M₂`
  out of any right-embedded configuration; `seq_run_left` runs `M₁` up to `T` provided `M₁` does not
  accept strictly before `T`, an `M₁` rejection needing no hypothesis; `seq_handoff` composes them
  under **first arrival** of `M₁.accept` at `T`, which is load-bearing — an earlier acceptance would
  have fired the routed edge earlier; `seq_reject_handoff` needs no first-arrival premise.
  The composed start is routed too: `seq_initialConfig` identifies its initial configuration with
  `M₁`'s routed one, so a terminal `M₁.start` hands over at time zero. `seqLeft M₁.accept` and
  `seqLeft M₁.reject` are dead states no row or start targets.
* `FixedGammaTargetDecrementCountdown.handoff_exact` (four: matching tag, decoded width,
  `2 <= zeros`, G2q's room): out of the composed `startConfig` — G2q's own `startConfig`, the
  retagged *actual* G2p-f endpoint, routed — the composed run is G2q's run up to
  `T = decClock N zeros d`, is in neither composed verdict before `T`, at exactly `T` **is** the
  countdown's landed `startConfig B x w` re-embedded, and every later step is a countdown step. The
  switch fires at G2q's **first arrival**, supplied by G2q's `decrement_strict`, not at G2q's
  deadline `3N`: a switch described at the deadline would credit the countdown with steps it had
  already taken.
* `FixedGammaTargetDecrementCountdown.decrement_countdown_drained` (G2u's seven hypotheses,
  unchanged; `v` universally quantified): at exactly
  `composedClock N zeros d v = decClock N zeros d + fullClock zeros d v` the composed machine is in
  its accept — the countdown's `qDone` — on the separator blank with the register cleared, `v` marks
  laid and blanks beyond, persisting.
* `decrement_countdown_drained_accepted_content_at_polyClock` (exactly G2w-b's **three**: the
  parse, the acceptance, `3 <= pr.2.n`; no tag, cap, room, budget, clock, width, digit, initial-state,
  correctness or runtime premise): at `B := polyClock 3 (pairLength a m)` the composed clock
  `C = decClock N zeros d + fullClock zeros d pr.2.n` is at most `B`, exactly **two** of the handoff
  facts above are re-exported — no composed verdict before `T = decClock N zeros d`, and at exactly
  `T` the countdown's landed `startConfig B x w` re-embedded; the routed run up to `T` and the
  countdown suffix after it stay inside the pnp3 proof — and at exactly `C`, at exactly `B` and at
  every later time the composed machine is in its
  accept with tape `loopTape B x w zeros 0 pr.2.n` — the register cleared, exactly `pr.2.n` marks —
  with `pr.2.n = pr.1` exported and the target tracked as `pr.2.n` throughout. The register value is
  the G2r digit fact on the decoded header; the new arithmetic is `C <= 3N² + 12N + 4 <= (N+1)³ + 3`.
* Non-vacuity: `probe_decrement_countdown_polyClock_accepted_target_three` reuses G2w-b's accepted
  word at the pinned target `3` and reads back a switch time `T <= B`, no composed verdict before it,
  the countdown's `startConfig` at it, and the composed accept at `B`; on the pnp3 side
  `check_handoff_probe` reduces the composed run out of the identified actual `startConfig 0 tag
  physWord` by kernel computation and sees G2q's `qBorrow` at step `17` and the countdown's `qStart`
  on the same cell, now `some false`, at step `18`; `check_seq_literal_probe` reduces a six-state
  toy through both row handoffs and two terminal-start toys through their time-zero accept/reject
  routes.

Deferred and deliberately not claimed. **One handoff of seventeen**: the composed `startConfig`
still embeds every earlier phase — the sixteen handoffs from the sentinel through payload
exhaustion remain proof-level identifications in G2x's machine (Part A G2y above has since executed
the last of them, H16), no `initialConfig` on a raw pair input is executed,
and no clock here counts a step of any earlier phase; composing further handoffs needs first-arrival
theorems from their own start configurations — the G2p-d/e/f loop's is what Part A G2y above later
supplied, and G2p-b's is what Part A G3b above later supplied. **First arrival of the composed
accept**: `T` is the first time the handoff
fires, but nothing says `C` is the first time the composed accept is entered, since G2s-a and G2u
prove no first arrival for `qDone`. **The fence**: both tables are unfenced, hence so is the
composition; accepted words never overflow the lane, since `pr.2.n <= N` is derived, but an
overshooting word still runs off the end of the tape and sticks, a timeout and neither verdict, and
no rejected or malformed input is characterised — the rows routed to the composed reject are pinned
and never exercised. A future fence phase would be a middle component of `seq`, and
`seq_reject_handoff` would propagate its rejection at no extra cost; nothing here builds it. **Small
targets** `0`, `1`, `2` stay excluded by `3 <= pr.2.n`. **Every converse**, every witness-check
phase (index and table locating, witness window, circuit decode and evaluation, size check), and the
**model connection**: this is a V1 `UniformTM` on `Option Bool` cells laid out against
`pairLength a m`, while `ContentVerifierBridge` asks for the legacy `TM` with a `runTime` field on
`concatBitstring x w`; no V1 statement of the advice-free target is frozen, and the legacy `runTime`
advice channel of caveat 6 is untouched. The composed accept is the countdown's phase-local `qDone`;
reaching it out of a retagged actual prior endpoint is neither halting on a raw input nor language
acceptance, and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation`, `NP`
membership, advice-freedom claim or `ContentVerifierBridge` is stated. Neither
`SearchMCSPWeakLowerBound` nor `VerifiedNPDAGLowerBoundSource` is reduced. Infrastructure only.

**Part A G2v + G2w-a + G2w-b, the countdown drains on the parsed target, under a semantic linear
cap, at a fixed cubic budget (infrastructure only).**
Two new pnp4 modules, `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge`
and `Pnp4.Frontier.ContractExpansion.ContentCountdownLinearCap`. There is **no new machine, no new
state, no new table row and no new pnp3 module**: every step is G2s-a's fixed 11-state, 33-row table,
run for longer by G2u. Write `N = a+m` and `d = borrow x w zeros`. Ten public theorems: the G2v
surface includes room equivalences and one-way execution results; G2w adds one-way semantic and
execution results plus one plain equation between two spellings of a split word.

G2v is to G2u exactly what G2t was to G2s-a: the *value*. G2u's `register_drained` is stated for a
universally quantified `v` and supplies none — its own probes use the hand-picked literals `24` and
`3` — and on a decoded header the G2r bridge already proves both digit facts for the decoded target
`n`, so `v := n` is the whole content of the slice.

* `countdown_width_eq_gammaZeros` (two hypotheses, a decoded header and a decoded width): the
  **physical** width `FixedContentGammaTerminator.gammaZeros?` reads off the word equals the
  **canonical** `gammaZeros n = bitLength (n+1) - 1` the pnp4 layout computes from the decoded
  target, and the adjacent-power bounds hold at that common value. The proof is exponent uniqueness
  on `2^zeros <= n+1 < 2^(zeros+1)`; both widths are already functions of data, so this is an
  equation between two computed quantities and **not** extraction of a value from a proof.
* `countdown_drain_cap_iff_machine_room` (the same two): the explicit lane cap `n <= F` together
  with `gammaZeros n + 2 + F <= a+B` is G2u's `lane_room` premise once the width is recovered — the
  same condition as the physical `zeros+2+F <= a+B` and as the tape form
  `a+m+3+zeros+F < tapeLength (pairLength a m) B` — and cap plus room **imply** G2t's first-round
  room `2*(n+1) < 2^(a+B)`. The converse is **not** stated and is false in general;
  `probe_countdown_drain_room_strictly_stronger` exhibits a literal split where G2t's room holds and
  this one fails at *every* `F` the cap admits.
* `countdown_drained_header_value` (five: matching tag, decoded header, `3 <= n`, the cap, the
  room): out of the landed `startConfig` the machine *enters* `qLoop` on the separator blank
  `N+2+zeros` after exactly `d+2` steps with the register holding `n` cell by cell, and after
  exactly `fullClock zeros d n` steps is in the absorbing `qDone` there with tape
  `loopTape B x w zeros 0 n` — every register cell `some false`, exactly `n` marks filling
  `[N+3+zeros, N+3+zeros+n)`, blanks from `N+3+zeros+n` on — and that endpoint persists. `3 <= n`
  reaches `2 <= zeros`; G2u's drain needs no positivity, so unlike G2t nothing here uses `1 <= n`.
* `countdown_drained_parsed_target` (five, with the header replaced by a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec, no monotonicity and no
  injectivity premise): `pr.2.n = pr.1`, the decoded header and width, and the same endpoint at the
  actual parsed target.

G2w-a supplies a *value* for `F`, as semantics rather than as parsing. No theorem bounds the target
from parser success alone, and none is claimed: the source is virtually zero-padded, so the strict
parser's returned target is tied to no bound on the physical length. Content *acceptance* does bound
it, at the concrete `treeCircuitWitnessCodec (thresholdPoly k)`.

* `contentSemanticAccepts_parsed_target_le_length` (two: the successful parse and the Boolean
  acceptance; the exponent `k` is data): `pr.2.n <= N` for `z : PrefixBitVec N`. Two branches. If
  `treeMCSPPrefixM codec pr.2.n <= N`, the layout bound `instanceSize_lt_treeMCSPPrefixM` already
  places `pr.2.n` below it. Otherwise FEAS-0's
  `contentAccepts_parsed_tableLen_le_of_header_target_wide` turns acceptance into
  `tableLen pr.2.n = 2^pr.2.n <= N`, and `pr.2.n < 2^pr.2.n` finishes;
  `contentInput?_target_eq_contentHeader` is what lets the wide case be read at the parsed target
  rather than the header's. Neither branch needs `0 < N`.
* `contentSemanticAccepts_eq_false_of_length_lt_parsed_target` is the contrapositive in the form a
  routing phase would consume: a successful parse with `N < pr.2.n` makes the frozen Boolean checker
  **reject**. It is a statement about `contentSemanticAccepts` and about nothing else.
* `contentSemanticAccepts_parsed_target_le_pair_length` is the same bound at the split
  `z := Fin.append x w`, where `N` is the compacted content length `a+m` the fixed-phase tape ABI is
  laid out against.
* `countdown_drained_accepted_content` takes it: on an accepted word whose parse succeeds, G2v's
  drain runs at `F := a+m`, so the lane cap is **derived** from acceptance instead of assumed. The
  room stays a hypothesis.

G2w-b closes the remaining free budget by *choosing* it, at
`B := polyClock 3 (pairLength a m) = (2*a+1+m)^3 + 3`, a fixed cubic function of the split's own two
lengths. Acceptance caps the target at `N`, `gammaZeros n <= n` caps the width at `N`,
`borrow_pins` caps the borrow by the width, and G2u's clock expands to
`fullClock zeros d n = d + n*n + n*(2*zeros+6) + 2*zeros + 7`, whose every summand is then below a
fixed quadratic in `N`; the cube dominates it because `3 <= pr.2.n <= N` is in force.

* `concatBitstring_eq_append` is a word-shape bridge and nothing else: the verifier interface's
  `concatBitstring x w` and the fixed-phase split `Fin.append x w` are the same function of the two
  blocks. No parse, no acceptance, no header, no codec and no machine occurs in it.
* `countdown_drained_accepted_content_at_polyClock` has exactly **three** proposition hypotheses —
  the successful parse, the Boolean acceptance and `3 <= pr.2.n` — and no others: no tag premise
  (the factorization `fixedTag_semantic_factorization` derives it from acceptance), no cap, no
  room, no free `B`, no free `F`, no runtime premise and no correctness premise. Both the room
  `gammaZeros pr.2.n + 2 + N <= a+B` and the clock bound `fullClock zeros d pr.2.n <= B` are
  **conclusions**, exported as conjuncts alongside `3 <= N` and the derived tag, and the endpoint is
  transported from `fullClock` to exactly `B` steps by the persistence conjunct G2v already proves.
* `probe_countdown_polyClock_accepted_target_three` inhabits those three premises **jointly** — one
  accepted word per exponent, GATE-0's zero-prefix query for the all-false table on three variables
  followed by its certificate — at the pinned target `pr.2.n = 3` and hence the pinned width
  `gammaZeros 3 = 2`, and reads the `qDone` endpoint state back after exactly `B` steps. So G2w-b
  is not a statement about an empty premise set. That probe exhibits one word per exponent and
  claims nothing about any other; in particular it exhibits no *rejected* and no *overshooting*
  word.

Deferred and deliberately not claimed. The **fence**: `F` is a parameter of every G2v statement, the
tape is the unchanged canonical `loopTape` — blank at `N+3+zeros+F` — and nothing here lays a cutoff
cell, adds a `qOverflow` state or shows that any execution theorem survives an installed
`some false` in the lane. The executed-fence requirement recorded in the G2s-a and G2u entries below
stands unchanged: the lane is still uncapped *in the machine*, a target too large for the budget
still runs `qRunEnd` off the end of the tape and sticks there, which is a timeout and therefore
neither verdict, and G2w-a's bound does not change that — it identifies a cap value that is
legitimate for accepted words, not a mechanism that enforces one. The *other* half of that recorded
requirement, that the `F = N` justification be derived or replaced, is what G2w-a supplies, and only
in the form stated above: `F = N = a+m` for **accepted** words, at the concrete
`treeCircuitWitnessCodec (thresholdPoly k)` and conditional on acceptance, never from parser success
and never codec-generically. The executed-fence half stands. The **room** is carried and never
derived in G2v and G2w-a — `B` is a free budget there — and is sufficient and used, never shown
necessary; G2u's `check_below_room_drain_probe` still exhibits a budget where it fails while the
drain completes. G2w-b **derives** that room, but only by instantiating `B`: the condition is still
sufficient only, and nothing shows the cubic budget necessary. The **exponent** `3` is chosen to
dominate the quadratic clock; nothing shows it least and no smaller exponent is ruled out. The same
number `B` plays two roles in the G2w-b statement — the tape budget `startConfig` and `tapeLength`
are laid out against, and the number of steps the machine is run for — and that is an instantiation
choice, not a theorem: nothing says the two must agree, only that this one value is large enough for
both. `polyClock` is the repository's pinned clock family, and using it here is **not** a runtime,
`DecidesWithin`, `UniformP` or `NP` claim about anything.
**First arrival**: `qDone` absorbs, so the all-times conjunct is persistence and nothing more, and no
theorem says `qDone` is entered for the first time at `fullClock zeros d n`. **Every converse**:
nothing derives a header, a width, `2 <= zeros`, the cap, the room, the borrow length or a parsed
target from `qDone`, from the endpoint tape or from a mark in the lane, and no endpoint-to-parse
direction exists; on the G2w-a side nothing derives acceptance, a parse or a header from
`pr.2.n <= N`, and a `false` verdict can equally come from a failed parse or a failed witness check.
The more expensive `boundedContentCap` alternative — a polynomial lane derived from
`boundedContentInput?` success rather than a linear one derived from acceptance — is documented in
the G2w-a module and **not implemented**, and **no new direct import** is taken for it.
`BoundedContentSemanticVerifier` and the I1 gate-closure module are both already in the transitive
closure of both new modules, through `FixedContentTagGateCorrect`, which the G2v bridge reaches via
the G2o header-value bridge; the accurate statement is that no declaration of `boundedContentInput?`
or of its verifier is *used* here. What the new proofs do use from that direction is G2o's
`contentInput?_target_eq_contentHeader`, whose own proof invokes I1's
`contentInput?_lengthGate_vacuous`; on the G2w-a side the used dependencies are FEAS-0's
`contentAccepts_parsed_tableLen_le_of_header_target_wide` and `instanceSize_lt_treeMCSPPrefixM`. The
degenerate widths `zeros <= 1` stay out of reach of the machine theorems, since `3 <= n` forces
`2 <= zeros`; the two G2v parser-side theorems carry no width premise and cover them. The gamma
leading-digit convention stays destroyed and the endpoint register is all `some false`. Also every
malformed-gamma branch, parser execution, `accepts`, `AcceptsAt`, language membership, advice
freedom, `NP` membership, `ContentVerifierBridge` and P-vs-NP mainline progress. The lane holds `n`
**marks** — the tally is exactly as long as the decoded target, stated as a cell predicate, not as a
claim that the machine re-encoded `n` in unary. `fullClock` counts this phase's steps alone, not one
of the steps `startConfig` embeds and no clock of any earlier phase, so nothing here composes a
pipeline clock. `qDone` is phase-local acceptance of a machine handed a retagged actual prior
endpoint, not raw-input language acceptance. Infrastructure only.

**Part A G2u, the countdown iterates and drains the register (infrastructure only).**
New pnp3 module `Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration`, the iteration the
G2s-a entry below deferred as G2s-c. There is **no new machine and no new table row**: every step is
G2s-a's fixed 11-state, 33-row table, run for longer. Write `N = a+m` and `S = N+2+zeros` for the
separator blank. Three clocks and three public execution theorems, all composing landed ones.

* `roundsClock zeros r k = k*k + k*(2*zeros+2*r+6)` is the closed form of
  `sum_{i<k} roundClock zeros (r+i)`, written so that no `Nat` subtraction occurs anywhere;
  `drainClock` adds the exhaustion and `fullClock` the entry. `rounds_clock_pins` pins the three
  closed forms, the recurrence `roundsClock zeros r (k+1) = roundClock zeros r +
  roundsClock zeros (r+1) k` that drives the induction, and
  `fullClock zeros d 1 = firstClock zeros d + zeroClock zeros`, which says exactly that the
  one-round case is G2s-a's `first_round` followed by G2s-a's exhaustion. `high_iff_lt` is the only
  new arithmetic: no digit above `zeros` and `v < 2^(zeros+1)` are one condition.
* `iterate_generic` (seven hypotheses: the room, `r+k <= F`, `k <= v`, the width hypothesis and the
  three configuration equations): `k` rounds out of an arbitrary `qLoop` configuration on `S` cost
  exactly `roundsClock zeros r k` and leave `qLoop` on `S` with the register holding `v-k` and
  `r+k` marks — the same canonical `loopTape`, so the endpoint is again an entry point of the same
  theorem. `k <= v` and the width hypothesis are both load-bearing: drop either and some round meets
  a register whose `zeros+1` cells are all `false`, which by G2s-a's own `exhaust_generic` runs to
  the absorbing `qDone` instead of borrowing, so at `0 < k` the conclusion fails in state and in
  tape. Both failures land on the same separator cell, so neither is a head mismatch.
* `drain_generic` (six: `r+v <= F` replaces both `r+k <= F` and `k <= v`): taking `k := v` empties
  the register and G2s-a's `exhaust_generic` then fires, so after exactly
  `drainClock zeros r v` steps the machine is in the
  absorbing `qDone` on `S` with an all-`false` register and `r+v` marks, and that endpoint persists.
  There is no `1 <= v` hypothesis — at `v = 0` no round runs and the exhaustion fires at once.
* `register_drained` (seven): the concrete exact run, not out of an arbitrary configuration but out
  of the landed phase-local `startConfig B x w` — the *actual* G2q machine retagged at G2q's own
  length-only `deadline (a+m)`. It re-derives G2s-a's `first_round` entry identification, the
  portion that does not use positivity, and composes `entry_generic` with `drain_generic` at
  `r = 0`: the machine *enters* `qLoop` on `S` after exactly `d+2` steps with the register holding
  `v`, and after exactly `fullClock zeros d v` steps is in `qDone` there with every register cell
  `some false`, exactly `v` marks in `[N+3+zeros, N+3+zeros+v)`, blanks beyond, and the endpoint
  persisting. Its hypotheses are `first_round`'s with `1 <= v` dropped and the room split into
  `v <= F` and `zeros+2+F <= a+B`. `v = 0` is a legitimate `drain_generic` case but cannot inhabit
  these digit hypotheses under `2 <= zeros`, so no concrete zero-target coverage is claimed.

**The fence policy, reconciled.** The G2s-a entry recorded two requirements: that the iteration's
loop theorem take `F` as a parameter with room premise `zeros+2+F <= a+B`, and that the `F = N`
justification be derived or replaced first. They are about two different objects. This slice
satisfies the first literally and leaves the second untouched. Its theorems are **canonical bounded
execution lemmas**: `F` is a parameter of the *statement*, the tape is the unchanged canonical
`loopTape`, and no cell of it is a cutoff. They are **not** execution with an installed cutoff and
are not claimed to survive one — an installed `some false` at `N+3+zeros+F` is not a `loopTape`,
which is blank there, so the execution theorems would have to be re-proved against that tape and nothing
here is evidence that it can be. The executed-fence requirement stands unchanged and undischarged
for the fenced machine a later phase must build. The production statements leave `F` abstract; the
tests use literal budgets. No general `F = N` bound is claimed *here*.

The `F = N` half of that obligation has since been supplied separately, by G2w-a in the entry
above, which changed no declaration of this slice: `contentSemanticAccepts_parsed_target_le_pair_length`
derives `pr.2.n <= a+m` for **accepted** words at the concrete
`treeCircuitWitnessCodec (thresholdPoly k)`, covering both the wide and the narrow case. It remains
codec-specific and conditional on acceptance — parser success alone still bounds no target — and it
installs nothing, so the executed-fence half of the requirement stands undischarged.

`lane_room` is **sufficient and used, never shown necessary**, and it is not even the tightest
sufficient condition: it reserves exactly the cell an installed cutoff would occupy, so it can fail
where the canonical unfenced drain still completes. `check_below_room_drain_probe` exhibits one — at
`a = m = zeros = 0`, `v = F = 1`, `B = 2` the condition reads `3 <= 2` and fails, while
`drainClock 0 0 1 = 12` steps still reach `qDone` with the register cleared and one mark laid.

Deferred and deliberately not claimed. The **fence phase** itself: the lane is still uncapped in the
machine, a register too large for the budget still runs `qRunEnd` off the end of the tape and sticks
there, which is a timeout and therefore neither verdict, and the `qRunEnd`-on-`some false` row stays
pinned and unexercised. The **pnp4 parsed-target drain**, and with it every connection to
`contentHeader?`, `contentInput?` or a parsed target: `v` is universally quantified here, the
probes' `24` and `3` are hand-written literals, and no theorem of pnp3 produces either from a parse
— that companion has since landed separately, as the G2v entry above, which changed no declaration
of this slice. Also every converse, first arrival — `qDone` absorbs, so every persistence conjunct is persistence
and nothing more — any footprint or budget theorem, a malformed-gamma branch, parser execution,
`accepts`, `AcceptsAt`, `ContentAccepts`, language membership, `ContentVerifierBridge` and P-vs-NP
mainline progress. The gamma leading-digit convention stays destroyed. The lane holds `v` **marks**,
where `v` is the parameter whose register digits are *hypothesised*; calling them the target in
unary would be a claim about a decoded value and nothing here decodes anything. `qDone` is
phase-local acceptance of a machine handed a retagged actual prior endpoint, not raw-input language
acceptance, and every clock counts this phase's steps alone — not one of the steps `startConfig`
embeds. Infrastructure only.

**Part A G2t, the first countdown round runs on the parsed target (infrastructure only).**
New pnp4 module `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownBridge`, the
companion the G2s-a entry below deferred. There is **no new machine and no new pnp3 module**: the
run is G2s-a's `first_round`, unchanged. G2s-a states it for a `v` that is universally quantified
and supplies none — its own probes use the hand-picked literals `24` and `23` — and on a decoded
header the G2r bridge already proves both digit facts for the decoded target `n`, so `v := n` is
the whole content of this slice. Write `N = a+m` and `d = borrow x w zeros`. Three public theorems,
all one-way out of a decoded `contentHeader? = some …` or out of a successful dependent parse.

* `countdown_room_iff_target_bound` (two hypotheses, a decoded header and a decoded width): on that
  header the three forms `2*(n+1) < 2^(a+B)`, `zeros+2 <= a+B` and
  `a+m+3+zeros < tapeLength (pairLength a m) B` are the same condition, the doubling being exact
  because the gamma bounds put `2*(n+1)` in `[2^(zeros+1), 2^(zeros+2))`. Two
  further conjuncts place it against G2q's room: it implies it, and at the boundary width
  `zeros+1 = a+B` G2q's holds while this one fails. Unlike the G2r analogue both halves of that
  separation are proved rather than probed, and `probe_countdown_room_boundary_nonvacuous` only
  shows the boundary hypothesis is inhabited.
* `first_countdown_header_value` (four: matching tag, decoded header, `3 <= n`, and the room
  `2*(n+1) < 2^(a+B)`): the landed `startConfig` *enters* `qLoop` on the separator blank `N+2+zeros`
  after exactly `d+2` steps with the register holding `n`, and after exactly
  `firstClock zeros d = 2*zeros+d+9` steps is back in `qLoop` there with the register holding `n-1`
  and **one mark** at `N+3+zeros`. Six cell conjuncts read every index of the endpoint tape, and the
  endpoint register cells pin `n-1` among the values with no bit above `zeros`. `3 <= n` does two
  jobs: it reaches `2 <= zeros` and discharges G2s-a's `1 <= v`.
* `first_countdown_parsed_target` (four, with the header replaced by a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec, no monotonicity and no
  injectivity premise): `pr.2.n = pr.1`, the decoded header and width, and the same concrete
  endpoint at the actual parsed target `pr.2.n`.

A fourth number is now on the tape. `zeros` is the physical gamma width, `n+1` the encoded gamma
integer, `consumed = 2*zeros+1` and `treeMCSPPrefixM codec pr.1` length conventions, `n` what G2r
left in the register, and `n-1` what this round leaves there. The lane holds one **mark**; calling a
tally the target in unary would be a claim about a decoded value and no theorem here decodes
anything.

Deferred and deliberately not claimed. The **iteration**: this bridge is one round and one only —
nothing *here* composes rounds or states a clock beyond `firstClock zeros d`, which counts this
phase's steps alone, and the pnp3 iteration landed later as G2u above is not carried across to a
parsed target by anything in this bridge — the G2v entry above is the bridge that does it, and it
changed no declaration of this one. **Persistence**: `qLoop` is not terminal, so unlike G2r's
`qDone` these endpoints hold at
exactly their stated time and there is no all-times conjunct, no deadline and no clamp. The
**fence**: the room allocates the *first* lane cell and is not a bound on the countdown; a target
too large for the budget would run the lane off the tape, which is a timeout and therefore neither
verdict, and nothing here excludes that. Also every converse, first arrival, any footprint or budget
theorem, any malformed-gamma branch, the exhaustion, parser execution, `accepts`, `AcceptsAt`,
`ContentAccepts`, language membership, `ContentVerifierBridge` and P-vs-NP mainline progress. The
gamma leading-digit convention stays destroyed. Infrastructure only.

**Part A G2s-a, the gamma target unary countdown round (infrastructure only).**
New pnp3 module `Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown`: a **new** fixed 11-state,
33-row machine, the second new table since the G2p-d round. Write `N = a+m`. Out of the retagged
G2q endpoint it *enters* `qLoop` on the separator blank `N+2+zeros` in exactly `d+2` steps, writing
nothing; one round then subtracts one more from the target register and lays **one mark** in the
tally lane past that blank, in exactly `roundClock zeros r = 2*zeros+2*r+7` steps at `r` marks
already laid; an all-`false` register exhausts to the absorbing `qDone` in exactly
`zeroClock zeros = 2*zeros+5` steps with the tape unchanged. `first_round` runs the entry and the
first round out of the phase-local `startConfig` at `firstClock zeros d = 2*zeros+d+9`.

Everything is symbol-driven: no width, digit index, register address, mark count, clock, counter,
proof term, advice or producer mark occurs in any row, and every branch is decided by the one symbol
under the head. `qPadL` and `qPadR` pad each sweep back out to the full register, which is why the
round clock does not depend on how long the borrow ran. The statement-level `lowRun` is read off the
value and is private and structural; the machine finds the same cell by reading symbols.

**Entry ABI**, which any phase inserted before this machine must re-establish: `qStart` on the
cleared stopping digit `some false` at `N+1+zeros-d`, exactly `d` cells of `some true` to its right,
the separator blank at `N+2+zeros`, a blank lane beyond.

Deferred and deliberately not claimed. The **iteration** (G2s-c): nothing *in this pnp3 module*
iterates the round — that has since landed separately, as the G2u entry above, under an explicit
lane-budget parameter `F` and installing no cutoff. The **fence**: the
lane is uncapped, so a register too large for the budget runs `qRunEnd` off the end of the tape and
sticks there, which is a timeout and therefore neither verdict; the `qRunEnd`-on-`some false` row is
the reject hook the future fence phase will use, and it is pinned and unexercised. The **pnp4
bridge**, and with it every connection to `contentHeader?`, `contentInput?` or a parsed
target: `v` is universally quantified and no theorem *in this pnp3 module* supplies one — that
companion has since landed separately, as the G2t entry above. A footprint or budget
theorem, so every room premise is sufficient and used but never shown necessary. Every converse. A
malformed-gamma branch, since G2q characterises no non-`qDone` endpoint to route. And any
restoration of the gamma leading-digit convention, which this phase destroys further each round.

`qLoop` does not absorb, so every `qLoop` endpoint is an exact time and **not** a deadline, and
`exhaust_generic`'s all-times conjunct is persistence, not first arrival — no theorem says `qDone`
is entered for the first time at `zeroClock zeros`. The lane holds marks; calling it the target in
unary would be a claim about a decoded value, and nothing here decodes anything. `qDone` is an
internal control tag of a machine started from a phase-local retag of an actual prior run, so
reaching it is neither halting of a composed machine nor language acceptance; the module states no
`accepts`, no `AcceptsAt` and no language membership, and the clocks compose no earlier clock.
Infrastructure, not P-vs-NP mainline progress.

**Part A G2r, the decremented register is the parsed target's digits (infrastructure only).**
New pnp4 module `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge`,
the composition that both entries below deferred. There is **no new machine and no new pnp3
module**: the run is G2q's `register_decremented`, unchanged, and everything added is a statement
about what its endpoint cells *are*. Write `N = a+m` and `d = borrow x w zeros`. Five public
theorems, all one-way out of a decoded `contentHeader? = some …` or out of a successful parse; no
converse is stated anywhere.

The composition is short, and that is the point. G2q's `decBit_sub_one` is arithmetic about an
**arbitrary** `v` whose bit `zeros-j` is register digit `j` at every `j ≤ zeros` and which has no
bit above `zeros`; G2p-g's `exhaustion_register_digits` proves exactly those two facts for
`v = n+1` on a decoded header. Instantiating one at the other, and using `n+1-1 = n`, is the
whole mathematical content of this slice: the register that held the digits of the encoded gamma
integer `n+1` now holds the digits of the **decoded target `n` itself**, at every `j ≤ zeros`.

Three theorems are parser-side: no machine, no tag and no clock occurs in any of them, and only
`decrement_room_iff_target_bound` mentions the budget `B`. `decremented_register_digits` (one
propositional hypothesis, a decoded header) produces `zeros` with `consumed = 2*zeros+1`, the
bounds `2^zeros ≤ n+1 < 2^(zeros+1)`, the bound `d ≤ zeros` that keeps the borrow inside the
register, the equation `decBit x w zeros d j = n.testBit (zeros-j)` at every `j ≤ zeros`, and the
completeness fact that `n` has no bit above `zeros`, so those `zeros+1` cells carry *all* of the
decoded target's digits. `decBit` and `borrow` are G2q's endpoint-content functions — pure
functions of the word and the width — so this theorem runs nothing.
`decremented_register_determines_target` (four hypotheses) adds uniqueness: any `v` whose bit
`zeros-j` is the decremented digit `j` for every `j ≤ zeros` and which has no bit above `zeros`
**is** `n`. It is arithmetic about digits, not a decoding step any machine performs.
`decrement_room_iff_target_bound` (two hypotheses) makes G2q's **stronger** room premise legible:
`n+1 < 2^(a+B)`, `zeros+1 ≤ a+B` and `N+2+zeros < tapeLength (pairLength a m) B` are the same
condition; it implies G2p-g's `n+1 < 2^(a+B+1)`; and at the boundary width `zeros = a+B` it
*fails*. That G2p-g's can still hold at that boundary is no conjunct of it — the probe
`probe_decrement_room_strictly_stronger` exhibits that at a literal word, and only together do
the two show the one extra cell `qRegEnd` needs is a real strengthening rather than a
restatement.

Two are machine-side, at G2q's own endpoint. `decremented_register_header_value` (four
hypotheses: matching tag, decoded header, `3 ≤ n`, and the room `n+1 < 2^(a+B)`): the landed G2q
machine run out of the landed `startConfig` for exactly `decClock N zeros d` steps is in `qDone`
on the stopping cell `N+1+zeros-d` with tape `decTape B x w zeros d`, every register cell `N+1+j`,
`j ≤ zeros`, holds `some (n.testBit (zeros-j))`, `n` has no bit above `zeros`, those endpoint
cells *pin* `n` among all values with no bit above `zeros`, every cell outside the register is the
incoming G2p-f endpoint cell of `finishTape B x w zeros`, and the endpoint persists at every later
time. One conjunct looks backwards instead of forwards — the incoming `finishTape` register cells
hold `some ((n+1).testBit (zeros-j))` — so both sides of the subtraction are visible in a single
statement. `decremented_register_parsed_target` (four hypotheses, for an arbitrary codec) replaces
the header by a successful **dependent parse** `contentInput? codec (Fin.append x w) = some pr`,
exports `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is what
`ContentAccepts` feeds to the search relation, is the outer Sigma index and the target a decoded
`contentHeader?` *returns* — and restates every endpoint conjunct in terms of `pr.2.n`. That is
the actual parsed dependent target, not a convention length: `consumed = 2*zeros+1` and the window
length `treeMCSPPrefixM codec pr.1` stay length conventions, and no conclusion here puts either in
a register cell.

**The gamma leading-digit convention is not restored, and must not be read back in.** The
convention encodes `n` as the bits of `n+1` precisely so that the leading digit is a `true` the
decoder can find, and subtracting one destroys that. When the incoming register is exactly
`2^zeros` the borrow runs its whole length and clears digit `0`, so the decremented register's top
cell is `some false`; the theorems say so rather than excluding it, and the probe
`probe_decrement_cleared_top_digit` exhibits the case on a literal word — gamma `0001`, payload
`000`, header `(7, 7)`, `borrow = 3`, `decClock 15 3 3 = 18`, endpoint register `0111₂` at cells
`16 … 19`, the four digits of `7` with a `false` on top. For the same reason G2p-g's virtual-tail
conjunct has **no analogue** here: a truncated payload's register cell is `some false` before the
phase and the borrow may flip it to `some true`, so only the general statement, that the cell holds
`n`'s digit, is made. The other probe, `probe_decrement_register_width_three`, is the ordinary
shape: header `(12, 7)`, incoming register `1101₂`, `borrow = 0`, `decClock 15 3 0 = 15`, endpoint
register `1100₂` — the digits of `12`. Both derive their cells from
`decremented_register_header_value` for every budget and reduce no `startConfig`.

Deferred, and deliberately not claimed: every converse — nothing derives a header, a width,
`2 ≤ zeros`, room, or the borrow length from `qDone`, from the endpoint tape, or from a digit at a
register cell; parser execution of any kind (`n` and `pr` occur only in statements, and G2q's
control reads one tape symbol and nothing else); reading the register as a number *on the tape*,
the pinning conjunct being arithmetic about the digits found there; a footprint or budget theorem,
so the room premise is carried and sufficient, never shown necessary; a malformed-gamma branch and
the degenerate widths `zeros ≤ 1` **on the machine side**, which `register_decremented` inherits
from `payload_exhausted` and excludes, while the three parser-side theorems carry no width premise
and cover them; **first arrival**, which no conjunct of either machine theorem states — they give
the endpoint at exactly `decClock` and its persistence at every later time, and nothing says
`qDone` is not entered earlier, minimality being G2q's own `decrement_strict`, stated there for an
arbitrary configuration of the G2p-f endpoint shape and neither instantiated nor restated here;
and the handoff of this endpoint onward.
Given a decoded header `3 ≤ n` is exactly `2 ≤ zeros` — both directions follow from the exported
bounds, only the direction used here is proved. `decClock` counts the steps of the G2q phase
alone, not one of the steps its `startConfig` embeds, so no clock here composes a pipeline, and
`qDone` is an internal control tag of a phase whose `startConfig` retags an *actual* prior run, so
reaching it is neither halting of a composed machine nor language acceptance. Nothing here is a
`ContentAccepts` statement. Clock composition, the fixed parser, advice freedom, `NP` membership,
`ContentVerifierBridge` and P-vs-NP mainline progress stay out of scope.

**Part A G2q, the gamma target register decrement (infrastructure only).** New pnp3 module
`Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement`, and the first **new machine** since
the G2p-d round: a fixed 7-state, 21-row table that subtracts one from the target register the
G2p-e/G2p-f loop left on the tape. A new table was unavoidable, not convenient — that loop only
ever appends a digit and marks a consumed gamma zero, and no row of its 22-state table performs a
borrow. Write `N = a+m`. Fifteen public theorems; every one of the module's 33 public declarations
is restated in the surface test and printed in `pnp3/Tests/AxiomsAudit.lean`.

Everything is symbol-driven, which is the design. No width, digit index, register address,
counter, proof term, advice or producer mark occurs in the table: every branch reads the one
symbol under the head. Out of G2p-f's endpoint — halted on the tag cell `7` with tape
`finishTape B x w zeros` — `qSeekTerm` runs right over everything that is not `some true`, so
the first it meets is the walking terminator (the restored gamma zeros are `some false`, the
consumed trail blank); `qSeekGap` runs right over the non-blank content, so the first blank it
meets is the boundary cell `N`; `qRegEnd` runs right over the register, so the first blank past it
is `N+2+zeros`, and one left step lands on the least significant digit `N+1+zeros`. `qBorrow` then
does the arithmetic in two rows: `some false` becomes `some true` and the head moves left,
`some true` becomes `some false` and the machine halts in the absorbing `qDone` there. The low run
of `false` digits is flipped, the `true` that stops it is cleared, every higher digit is left
alone — which is subtraction of one. `borrow_pins` produces the stopping index from G2p-d's
`registerBit_pins` and bounds it by `zeros`, so the sweep never leaves the register; `borrow` is a
statement-level quantity read off the digits, not advice, since no row of the table mentions it.

`decrement_generic` is that run out of an **arbitrary** configuration matching the G2p-f endpoint,
in exactly `decClock N zeros d = N+zeros+d-3` steps at borrow length `d`, ending in `qDone` on the
cell `N+1+zeros-d` with the whole tape equal to `decTape B x w zeros d`. The clock is **not**
length-only, and in two ways: it depends on the decoded width, and through `d` on the stored
digits. `clock_pins` decomposes it under the width guard `9+zeros ≤ N` and states the length-only
bound `deadline N = 3*N` in the guarded form `9+zeros ≤ N → d ≤ zeros → decClock ≤ deadline`;
both guards are hypotheses, not caution. `decrement_schedule` pins the control and head at every
time of the phase, so with `decrement_generic` the control is named at every time up to and
including the halt, and `qReject` is entered nowhere in that range — nor later, by the clamp.
`decrement_strict` proves both directions: `qDone` is not entered strictly earlier, and the
configuration is constant from `decClock` on, in particular at `deadline N`. That minimality is
measured from *this* configuration, not from the G2p-d `startConfig` of the previous phase.
`decTape_pins` says what the endpoint tape is: the register cells hold `decBit`, the stopping
cell is `some false`, the cells under it `some true`,
and every cell outside `[N+1, N+1+zeros]` is the incoming `finishTape` cell. It is a statement
about the tape function, not about which cells were visited.

`register_decremented` is the slice's concrete exact run, out of the phase-local `startConfig` on
four hypotheses: a matching tag, `gammaZeros? (Fin.append x w) = some zeros`, `2 ≤ zeros`
(inherited from G2p-f, so `zeros ≤ 1` stays outside the proved surface), and the room
`N+2+zeros < tapeLength (pairLength a m) B`. That room is one cell more than G2p-f's, because
`qRegEnd` finds the register's right end by the blank past it and by nothing else; `room_iff`
reads it as `zeros+1 ≤ a+B` and proves it implies G2p-f's own premise, so exactly one room
premise is carried. Sufficient and used, never shown necessary: there is still no footprint
theorem. The handoff consults no decoded data — `startConfig` retags the G2p-d round machine at
the **length-only** time `priorDeadline N = 3*(N*N)`, `handoff_exact` pins that retagging replaces
the control and nothing else, and `prior_covers` proves that time is at or past G2p-f's exact
`totalClock N zeros` at every decoded width, so G2p-f's clamp identifies the incoming
configuration. That is the length-only loop deadline the G2p-e/G2p-f loop never stated, and it
bounds that loop's own phase-local clock and nothing else: it counts no step the G2p-d
`startConfig` embeds, and `decClock` counts the steps of this phase alone.

What the decrement *means* is kept apart from what it *does*. `sub_one_bits` and `decBit_sub_one`
are arithmetic about `Nat` — no machine, no tape, no parser, no codec. For an **arbitrary**
natural `v` whose bit `zeros-j` is register digit `j` at every `j ≤ zeros` and which has no bit
above `zeros`, the endpoint digits are the bits of `v-1` at the same positions, and `v-1` has no
bit above `zeros` either. **No theorem here supplies such a `v`.** Those two hypotheses are
exactly what the G2p-g bridge's `exhaustion_register_digits` proves for `v = n+1` on a decoded
header, and composing the two is a pnp4 step this slice does not take; nothing here mentions
`contentHeader?`, `contentInput?`, or a parsed target. The G2p-g entry below says the register
holds the digits of `n+1` and not of `n`; this slice supplies the *machine* that borrows one out
of those cells, and not the identification of the result with `n`. That identification is now
supplied, outside this module, by the G2r bridge at the top of this file, which instantiates this
`v` at `n+1`; it changes nothing inside pnp3, which still mentions no header and no parse.

Nonvacuity is independent of the endpoint theorems. Two literal probes identify the phase-local
start configuration for every budget from G2p-f's `payload_exhausted` and `prior_covers` alone,
then reduce this machine's own `run` by kernel computation at `B = 0`. Both words decode to
`zeros = 4` behind the tag `10110010`, and they exercise the two shapes of the borrow. The
physical probe (`N = 17`, terminator at `16`, `totalClock 17 4 = 64`, `priorDeadline 17 = 867`)
has `borrow = 0` and `decClock 17 4 0 = 18`: `qBorrow` reaches the least significant digit `22` at
step seventeen, that digit is `some true`, and step eighteen is `qDone` on `22` with `[18,22]`
reading `11001` before and `11000` after. The truncated probe (`N = 15`, terminator at `14`,
`totalClock 15 4 = 54`, `priorDeadline 15 = 675`) has `borrow = 3` and `decClock 15 4 3 = 19`:
`qBorrow` walks `20, 19, 18` — three `false` digits, two of them the virtual zeros of the
truncated payload — and stops on `17`, so step nineteen is `qDone` on `17` with `[16,20]` reading
`11000` before and `10111` after. Those are cell contents read from the register's leading cell;
no probe claims them to be a decoded value. Both sample a cell outside the register and run past
the endpoint, exhibiting `qDone` absorbing. `check_probe_inputs_valid` and `check_clock_values`
pin the hypotheses and the literal clocks separately, and
`check_decBit_sub_one_instance` shows the arithmetic's premises are satisfiable — the truncated
register's digits are the bits of `24`, the endpoint's the bits of `23`. That `24` is a
**hand-written literal** matched to the digits; no theorem of this slice or of pnp3 derives it
from a parse, which is precisely the deferred pnp4 step.

Deferred by *this module*, and deliberately not claimed in it: that pnp4 bridge and every
connection to a parsed target — the bridge has since landed as the G2r entry at the top of this
file, and no declaration of this module changed;
a footprint or budget theorem; every converse — nothing derives `zeros`, the borrow length, or
anything about the incoming digits from `qDone` or from an endpoint cell; a malformed-gamma
branch; first arrival measured from the previous phase's `startConfig`; the handoff of this
endpoint onward; and **any restoration of the gamma leading-digit convention**. That last is a
real gap, not a formality: when the register holds exactly `2^zeros` the borrow clears digit `0`,
so the decremented register need not begin with a `true`, and nothing here re-establishes the
invariant the gamma encoding relies on. `qDone` is `machine.accept` of a machine started from a
phase-local retag of an actual prior run rather than from `initialConfig` on a raw pair input, so
reaching it is neither halting of a composed machine nor language acceptance; the module states no
`accepts`, no `AcceptsAt` and no language membership. Clock composition, the fixed parser, the
checks, advice freedom, `NP` membership and `ContentVerifierBridge` are out of scope. It is
infrastructure, not P-vs-NP mainline progress. Long-form design notes are in
`pnp3/Docs/UniformP_V1.md`.

**Part A G2p-g, the exhausted register is the parsed target's digits (infrastructure
only).** New pnp4 module
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetPayloadExhaustionBridge`, the
companion the G2p-f slice below left deferred. There is **no new machine and no new pnp3
module**: the run is G2p-f's `payload_exhausted`, unchanged, and everything added is a
statement about what its endpoint cells *are*. Write `N = a+m`. Five public theorems, all
one-way out of a decoded `contentHeader? = some …` or out of a successful parse; no
converse is stated anywhere.

Three are parser-side: no machine, no tag and no clock occurs in any of them, and only
`room_iff_target_bound` mentions the budget `B`, through the tape length.
`exhaustion_register_digits` (one propositional hypothesis, a decoded header
`contentHeader? (Fin.append x w) = some (n, consumed)`) produces the width `zeros` with
`consumed = 2*zeros+1`, `2^zeros ≤ n+1 < 2^(zeros+1)`, and the **register equation**
`registerBit x w zeros j = (n+1).testBit (zeros-j)` at *every* `j ≤ zeros` — the
bootstrap's leading `true` at `j = 0` is the header's own leading digit, and each later
`j` is the payload cell `8+zeros+j`. Two further conjuncts make "complete" precise. `n+1`
has **no** bit above `zeros`, so the `zeros+1` register cells carry all of its digits and
none is stored elsewhere. And for `1 ≤ j ≤ zeros` with `a+m ≤ 8+zeros+j` — the **virtual
tail**, where the payload cell has left the physical word — the register digit is `false`
*and* the parsed `(n+1).testBit (zeros-j)` is `false` too. That conjunct is the point of
the slice. `registerBit` pads with `false` because the cell is not in the word (on
`contentTape` it is blank); the decoder pads with a virtual zero because `contentHeader?`
reads through `VirtualZeroTailReader`. Those are two different paddings, and this is where
they are proved to agree, so a virtual `false` in a truncated register is *the parsed
target's own digit* rather than the default G2p-f could only call content.
`register_determines_target` (four hypotheses) adds uniqueness: any `v` whose bit
`zeros-j` is the register digit `j` for every `j ≤ zeros` and which has no bit above
`zeros` **is** `n+1`. Both premises are needed — without the second, `v + 2^(zeros+1)`
would match every cell. This is arithmetic about the digits, not a decoding step any
machine performs. `room_iff_target_bound` (two hypotheses) makes the room premise legible:
on a decoded header `n+1 < 2^(a+B+1)`, `zeros ≤ a+B`, and the premise G2p-f inherits from
the G2p-e iteration, `N+1+zeros < tapeLength (pairLength a m) B`, are the *same*
condition.

Two are machine-side, at G2p-f's own endpoint. `exhausted_register_header_value` (four
hypotheses: matching tag, decoded header, `3 ≤ n`, and the room `n+1 < 2^(a+B+1)`): the
landed G2p-d round machine run out of the landed `startConfig` for exactly
`totalClock N zeros` steps is in `qDone` on the tag cell `7` with tape
`finishTape B x w zeros`, every register cell `N+1+j`, `j ≤ zeros`, holds
`some ((n+1).testBit (zeros-j))`, every virtual-tail cell holds `some false` together with
the matching parsed `false`, those endpoint cells *pin* `n+1` among all values with no bit
above `zeros`, the tag cell `7` with the gamma zero field `[8, 7+zeros]` is back to the
incoming content tape, and the endpoint persists at every later time.
`exhausted_register_parsed_target` (four hypotheses, for an arbitrary codec) replaces the
header by a successful **dependent parse** `contentInput? codec (Fin.append x w) = some pr`
and exports `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is the
`pr.2.n` that `ContentAccepts` feeds to the search relation, is the outer Sigma index and
the target a decoded `contentHeader?` *returns* — then restates the register, pinning
conjunct included, in terms of `pr.2.n`. It re-exports every conjunct of the header form except the
gamma zero field restoration, which is about the tape and not about the target.

Three numbers stay apart. `pr.2.n` is the **actual parsed target**: the value a decoded
`contentHeader?`, and the dependent parser after it, *returns* once the gamma convention has
been applied — not a value the header stores. `n+1` is the **encoded gamma integer** that
convention writes: the integer whose bits physically occur in the header and in the
exhausted register, so that the leading digit is a `true` the decoder can find. The register
holds the digits of `n+1`, *not* of `n`, and the decrement is performed by no machine here
and is not claimed. `consumed = 2*zeros+1` is the header's
**cell count**, a length convention that is not the target and never sits in the register;
the parser's other length convention `treeMCSPPrefixM codec pr.1` occurs only in the type
of `pr`.

Room is carried, not derived. A decoded header does not imply it: `B` is free, and
`room_iff_target_bound` reads it as `zeros ≤ a+B`, a condition on the `x` side and the
budget. The surface probe `probe_exhausted_room_not_implied` makes that sharp — one
twelve-cell word with a matching tag and the decoded header `(5, 5)`, hence `3 ≤ n`, split
once as `a = 8, m = 4` and once as `a = 1, m = 11`, with the word identity of the two
splits pinned as a conjunct; every reader here sees `Fin.append x w`, so both splits decode
to the same header, but at `B = 0` room holds on the first and fails on the second. The
probe states the tape form on the first split and refutes the outer two of the three
equivalent forms on the second, which `room_iff_target_bound` makes all three. Room is
therefore sufficient and used,
never shown necessary: there is still no footprint theorem on the pnp3 side. Two further
probes derive their cells from `exhausted_register_header_value` for every budget: header
`(12, 7)` gives the wholly physical four-digit register `1101₂` at cells `16 … 19` with
`totalClock 15 3 = 31`, and header `(5, 5)` gives `110₂` at cells `13 … 15` whose last
digit is the virtual tail — endpoint cell `some false`, parsed `(5+1).testBit 0 = false` —
with `totalClock 12 2 = 5`, the finish alone.

The decrement of `n+1` to `n` is now discharged, in two steps that were landed separately. The
G2q machine above borrows one out of these very register cells and proves, arithmetically and for
an arbitrary `v`, that the resulting digits are the digits of `v-1`; the G2r bridge at the top of
this file instantiates that `v` with the `n+1` this entry's `exhaustion_register_digits` supplies,
so the decremented register is proved to hold the digits of `n` — at G2q's own endpoint, under its
stronger one-extra-cell room premise, and for the parsed `pr.2.n` as well. Nothing about *this*
entry's theorems changed: they are still about the G2p-f endpoint, where the register holds `n+1`.
Deferred, and deliberately not claimed here: that composition, which is G2r's; reading the
register as a number *on the tape* (the pinning conjunct is arithmetic about the digits found
there, not a decoding step the control performs — no machine here executes `contentHeader?`,
`contentInput?`, or any parser, and control reads a tape symbol and nothing else); every
converse — nothing derives a header, a width, `2 ≤ zeros`, or room from `qDone`, from the
endpoint tape, or from a digit at a register cell; a footprint or budget theorem; a
malformed-gamma branch; first arrival measured from `startConfig`. The two machine theorems
inherit G2p-f's exclusion of `zeros ≤ 1`, since on a decoded header `3 ≤ n` is exactly
`2 ≤ zeros` (both directions follow from the exported bounds; only the direction used here
is proved, as in G2p-c); the three parser-side theorems carry no width premise and do cover
those widths. `zeros = 2` is admitted, where the G2p-e round count `zeros-2` is zero and
the endpoint is the finish alone. `qDone` is an internal control tag of a phase whose
`startConfig` retags an *actual* prior run, so reaching it is neither halting of a composed
machine nor language acceptance, and `totalClock` counts no step that `startConfig` embeds,
so it clocks no composed pipeline. Nothing here is a `ContentAccepts` statement. Clock
composition, advice freedom, `NP` membership, `ContentVerifierBridge` and P-vs-NP mainline
progress stay out of scope.

**Part A G2p-f, the gamma payload exhaustion finish (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion`. Still **no new
machine**: the landed G2p-d `FixedGammaTargetPayloadRound.machine` — the same fixed
22-state, 66-row table — already carries the stopping rule in its `qCntL`/`qFin` rows,
and `machine_reused` pins that identity together with the five rows this phase runs.
Write `N = a+m`.

What is new. G2p-e left the machine in the `r = zeros` instance of the loop invariant
`loopTape B x w zeros zeros`, where every gamma zero carries a consumed-source mark, so
`r = zeros` *is* exhaustion. Out of that configuration `exhaust_generic` proves the whole
finish: `qLoop` leaves the walking terminator into `qCntL`, `qCntL` scans left over the
blank trail, and the first non-blank it meets is cell `7+zeros` — at every earlier index
an unconsumed gamma zero, `some false`, which sent the round on through `qCntZ`, and here
a consumed mark, `some true`, which fires the `qCntL` row into `qFin`. `qFin` then sweeps
the counter field `[8, 7+zeros]` back to `some false` and halts on the tag cell `7`,
which a matching tag already holds as `some false`. The rule reads one tape cell and
nothing else: no width, digit index, address, counter value, proof term, advice or
producer mark occurs in control. Its hypotheses are a matching tag,
`gammaZeros? (Fin.append x w) = some zeros`, `1 ≤ zeros`, and the three projections of an
**arbitrary** incoming configuration — six propositional premises and **no room premise
at all**, because the finish only ever moves left from a head the hypothesis already
places inside the tape.

The restoration is the semantic point, and `finishTape_pins` states both halves of it.
On `[7, 8+zeros)` — the counter the loop consumed, plus the tag cell the sweep stops on —
the endpoint tape is back to the incoming `contentTape` and reads `some false`.
Everywhere else it is the incoming invariant untouched: consumed sources still blank, the
walking terminator still standing at `8+zeros+termWalk N zeros`, and the completed
register `[N+1, N+1+zeros]` still holding its `zeros+1` digits. So the endpoint is **not**
`contentTape`, and nothing claims it is; the probes pin a consumed payload cell blank and,
in the truncated shape, a content `false` overwritten by the terminator's `some true`.

Clocks. `exhaustClock N zeros = termWalk N zeros + zeros + 2`, where
`termWalk N zeros = walk N zeros zeros`: one step off the terminator, `termWalk N zeros`
blank-trail steps, the step that fires the rule, `zeros-1` further unmarking steps, and
the halt. It is neither length-only nor shape-independent — `2*zeros+2` on a physically
present payload, `N-7` on a truncated one — and it is the one clock of this loop that is
not padded flat, because the finish is performed once and no induction has to add up a
sequence of its costs. `clock_pins` pins both shapes and, under `9+zeros ≤ N`,
`exhaustClock N zeros ≤ roundClock N`; that guard is a hypothesis of the conjunct and not
editorial caution — at `N = 0`, `zeros = 100` the finish costs `102` while `roundClock 0`
truncates to `0`. `totalClock N zeros = loopClock N zeros + exhaustClock N zeros` counts the
G2p-e rounds and this finish only: not one step that `startConfig` embeds, so it clocks no
composed pipeline.

Because `qDone` absorbs — which `qLoop`, where both round endpoints sit, does not — this
endpoint may be transported forward, and `exhaust_strict` proves **both** directions
available here: the endpoint holds at every later time, and `qDone` is not entered at any strictly
earlier time, so `exhaustClock` is a proved first arrival. That minimality is measured
from the `r = zeros` configuration, not from `startConfig` — the G2p-e rounds carry no
strictness theorem, so `qDone`-freeness across them is established nowhere here — the two
probes pin a handful of pre-endpoint states only, not the absence of `qDone` throughout
that segment. `exhaust_schedule` pins the control at every time of the phase (`qLoop`,
then `qCntL`, then `qFin`), which with `exhaust_generic` leaves no time at which a source
or register state could occur. `payload_exhausted` is the slice's concrete exact run: on
a matching tag, a gamma field decoding to `zeros` with `2 ≤ zeros`, and the inherited G2p-e
room `N+1+zeros < tapeLength (pairLength a m) B` — four premises, the decode `gammaZeros?
(Fin.append x w) = some zeros` and the bound on `zeros` being two of them — the same machine
run out of the landed `startConfig` for exactly `totalClock N zeros` steps is in `qDone` on
cell `7`, its tape is `finishTape B x w zeros`, the gamma zero field is back to the content
tape, and the endpoint persists at every later time. The register conjunct is
**preservation, not completion**: that `[N+1, N+1+zeros]` holds its `zeros+1` digits is
G2p-e's `register_complete`, and all this slice adds is that the finish carries it through
unchanged — nothing decodes those digits, and where the payload is truncated the digits past
it are `registerBit`'s virtual `false`, which no theorem calls the payload's value. That
room premise is sufficient and used; it is not shown necessary, since there is no footprint
theorem.

Probes. Two literal probes identify the phase-local start configuration for every budget
from the landed G2p-d foundation endpoint alone, then reduce the round machine's own `run`
by kernel computation at `B = 0` across both remaining rounds *and* the finish, invoking no
execution theorem of this module. Both words decode to `zeros = 4`. The physical probe
(`N = 17`, `loopClock 17 4 = 54`, `termWalk 17 4 = 4`, `exhaustClock 17 4 = 10`,
`totalClock 17 4 = 64`) pins `qCntL` on the last counter mark `11` at step fifty-nine,
`qFin` on `10` at step sixty, `qFin` on `7` at step sixty-three, and `qDone` on `7` at step
sixty-four with cells `7,8,9,10,11` all back to `some false`, the consumed payload cell `13`
blank, the terminator at `16` and the register `[18,22] = true, true, false, false, true`.
The truncated probe (`N = 15`, `loopClock 15 4 = 46`, `termWalk 15 4 = 2`,
`exhaustClock 15 4 = 8`, `totalClock 15 4 = 54`) is two steps cheaper. That gap tracks `N`
alone: both probes lie in the band `9+zeros ≤ N ≤ 9+2*zeros`, where the clock is `N-7`, so
the pair is no witness of the clock's dependence on `zeros`. It pins the same restoration,
cell `14` carrying the terminator's `some true` over an input `false`, and the register
`[16,20] = true, true, false, false, false`. Both run past the endpoint, exhibiting `qDone`
absorbing. `check_probe_inputs_valid` states separately that both words satisfy the
tag/width hypotheses and, at `B = 0`, the room hypothesis.

Two of this slice's deferrals are now discharged by the G2p-g bridge above, which supplies
the pnp4 companion and ties every register cell — virtual tail included — to a digit of the
decoded header's, and of the actual parsed input's, target. A third is discharged on the
machine side by the G2q decrement above, which borrows one out of this endpoint's register in
a new fixed 7-state table, out of a phase-local retag of this slice's own endpoint; what that
slice does *not* supply is the identification of the result with `n`, so the digits-of-`n`
reading stays open. The rest stand as written. Deferred, and deliberately not claimed here:
that identification, any reading of the register as a *number* (`registerBit` gives content,
not a value), a footprint/budget theorem, every converse — nothing says that `qDone` at
`totalClock N zeros`, or any endpoint cell, implies anything about `zeros` — first arrival
measured from `startConfig`, the degenerate widths (`zeros = 0` is excluded from `exhaust_schedule`,
`exhaust_generic` and `exhaust_strict` by their `1 ≤ zeros` premise, which the tape-shape
theorem `finishTape_pins` does not carry; `zeros = 1` satisfies those three but is produced
by nothing here, since `payload_exhausted` needs `2 ≤ zeros`; `zeros = 2` is covered, with
`loopClock N 2 = 0` making `payload_exhausted` the finish applied directly to the retagged
foundation endpoint), and a malformed-gamma branch. `qDone` is `machine.accept` of a
machine started here from a phase-local retag of an actual prior run rather than from
`initialConfig` on a raw pair input, so reaching it is neither halting of a composed
machine nor language acceptance; this module states no `accepts`, no `AcceptsAt` and no
language membership. Clock composition, the fixed parser, advice freedom, `NP` membership
and `ContentVerifierBridge` stay out of scope. Nothing here is P-vs-NP mainline progress.

**Part A G2p-e, iterating the gamma payload round (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadIteration`. There is **no new
machine**: the landed G2p-d `FixedGammaTargetPayloadRound.machine` re-enters `qLoop`
at the end of a round, so the *same* fixed 22-state, 66-row table iterates, and
`check_machine_reused` records that identity. Write `N = a+m`.

What is new. `round_generic` carries the loop invariant `loopTape B x w zeros r` from
`r` to `r+1` for **every** index with `1 ≤ r` and work remaining (`r < zeros`), out of
an **arbitrary** configuration matching the `r`-instance rather than out of
`startConfig`. That double quantification — over the index and over the incoming
configuration — is exactly what the hard-coded `r = 2 → r = 3` theorem could not
support, and it is what makes an induction possible. Its hypotheses are a matching
tag, `gammaZeros? (Fin.append x w) = some zeros`, `1 ≤ r`, `r < zeros`, that index's
own room `a+m+2+r < tapeLength (pairLength a m) B`, and the three projections of the
incoming configuration (`qLoop`, head `8+zeros+walk N zeros r`, tape
`loopTape B x w zeros r`); its conclusion is state, head and the whole tape after
exactly `roundClock N = 2*N-7` steps. The cost stays length-only at every index
because every `r`-dependence cancels. A round is a counter phase costing
`2*walk N zeros r + 2*(zeros-r) + 3`, a register walk out and back costing `2*(r+1)`,
a content carry out and back costing `2*(N-9-zeros-r)` that only the physical shape
performs, and six fixed steps. In the physical shape `walk = r`, so the counter phase
is already free of `r` and the carry's `-2*r` cancels the register walk's `+2*r`; in
the virtual shape there is no carry, `walk` is the constant `N-9-zeros`, and it is the
counter phase's `-2*r` that cancels the register walk. Both shapes take the same six
fixed steps; three of the virtual ones pass through the `qVa`/`qVb`/`qVc` padding,
standing at the positions where the physical shape enters `qClear`, `qCarry` and
`qBackCont`.
`check_round_generic_subsumes_round_step` derives the landed hard-coded `round_step`
statement back out of `round_generic` at `r = 2`, so the generic round is a strict
generalisation of the landed one rather than a parallel claim beside it.

`rounds_iterate` is the induction: at `2 ≤ zeros`, `2+k ≤ zeros` and the room every
round needs, running the same machine for exactly `k * roundClock N` steps out
of the landed G2p-d `startConfig` reaches the `r = 2+k` instance. `register_complete`
is its `k = zeros-2` instance: after exactly `loopClock N zeros = (zeros-2)*roundClock N`
steps the register `[N+1, N+1+zeros]` holds all `zeros+1` digits
`registerBit x w zeros j`. `register_digits` spells those out — digit `0` is the
bootstrap's leading `true` and digit `i+1` is the payload cell `9+zeros+i` read through
the blank padding, so `i < zeros` covers exactly the payload block
`[9+zeros, 9+2*zeros)` and a truncated payload contributes virtual zeros; "exactly" is
its own conjunct, an iff pinning those source addresses as precisely that block. That is
register **content** at an exact time, not a decoded number: no theorem here mentions
`contentHeader?` or any parsed header value.

Room and clocks. `room_iff` reads the iteration's room premise
`N+1+zeros < tapeLength (pairLength a m) B` as `zeros ≤ a+B` — the premise the G2p-d
round slice recorded as "assumed nowhere" — while a single round at index `r` assumes
only `r < a+B`; at `3 ≤ zeros` the iteration premise implies the round's `3 ≤ a+B` and
at `2 ≤ zeros` the foundation's `2 ≤ a+B`. Those premises are sufficient and used —
each round's trace reaches `N+2+r` and writes there, the largest such cell over the
rounds iterated being `N+1+zeros` at `r = zeros-1` — but nothing proves them
necessary: there is no footprint theorem here, and the deferred exhaustion finish has
none either, so nothing claims this to be the room a *complete* loop needs. `qLoop`
does **not** absorb, so every endpoint above is an *exact* time and may not be
transported past it; no deadline is exported and no first-arrival or strictness
direction is proved. None of these clocks counts the steps `startConfig` embeds, so
none clocks a composed pipeline.

Probes. Nonvacuity is independent of the endpoint theorems: two literal probes first
identify the phase-local start configuration for every budget from the landed G2p-d
foundation endpoint alone, then reduce the round machine's own `run` by kernel
computation at `B = 0` for **two** consecutive rounds. Both words decode to
`zeros = 4`, so exactly two rounds remain. The physical probe (`N = 17`,
`roundClock 17 = 27`, `loopClock 17 4 = 54`) pins round one's physical source `15`
with its `false` carried in the control as `qClear0`, the round-one re-entry into
`qLoop` on the advanced terminator `15` with a `false` appended at `21`, then round
two's `qCntMark` on counter cell `11`, its physical source `16` with the `true`
carried as `qClear1`, and the final register `[18,22] = true, true, false, false,
true` — so the two rounds drive both carried-bit halves of the table. The truncated
probe (`N = 15`, `roundClock 15 = 23`, `loopClock 15 4 = 46`) pins the virtual
schedule at both round endpoints: the terminator is at `14` after each round and the
corresponding appended register digits are false. In round two it additionally pins
the boundary source `15` and entry through `qVa`/`qVb`/`qVc`; the final register is
`[16,20] = true, true, false, false, false`.
`check_probe_inputs_valid` states separately that both probe words satisfy the
tag/width hypotheses the general theorems assume, and at the probes' own budget
`B = 0` the room hypothesis too, so those are not statements about an unsatisfiable
premise set.

Deferred: the exhaustion finish — at `r = zeros` the next round's counter scan finds
the marked cell `7+zeros` and leaves `qLoop` through `qFin`, and that behaviour,
`qDone`, and the restoration of the gamma zero field are outside every theorem here —
the loop's own deadline, a first-arrival/strictness direction, the decrement from
`n+1` to `n`, the all-times clamp/footprint/budget package, and every converse:
nothing says that `qLoop` at `loopClock N zeros`, or any register digit, implies
anything about `zeros`. `zeros = 2` is covered only degenerately (`loopClock N 2 = 0`
makes `register_complete` a restatement of the retagged foundation endpoint
`startConfig`) and `zeros ≤ 1` is excluded by `2 ≤ zeros`. No pnp4 bridge exists for
this module; `startConfig` is a phase-local retag of an actual prior run, not a
composed execution from the raw pair input, and `qDone` is not language acceptance.
Nothing here is P-vs-NP mainline progress.
The exhaustion finish deferred here — the stopping rule, `qDone`, and the restoration of
the gamma zero field — is discharged by the G2p-f slice above, together with a
first-arrival/strictness direction and an all-times clamp for that phase (the clamp only
because `qDone` absorbs, which `qLoop` does not; minimality comes from that phase's
closed-form schedule instead). A *length-only* loop deadline, the decrement from `n+1` to
`n`, a footprint/budget theorem and every converse still stand — G2p-f's
`payload_exhausted` does export persistence from `totalClock N zeros`, but that clock
depends on the decoded width. G2p-f adds no room premise of its own: it inherits this
slice's `zeros ≤ a+B`, and its `payload_exhausted` does claim that room *sufficient* for a
complete loop with the finish included, so the sentence above — that nothing claims this to
be the room a *complete* loop needs — now holds of *necessity* only, which no footprint
theorem establishes.

**Part A G2p-d round, first remaining payload digit (infrastructure only).** New
pnp3 module `Complexity.Uniform.V1.FixedGammaTargetPayloadRound`: one fixed
22-state, 66-row machine — every row pinned literally, and restated literally again
in its surface test — that executes **one** round of the self-stopping gamma
payload loop whose markers the G2p-d foundation installed. It is one round, not the
loop: the iteration, the exhaustion finish and the loop's own deadline are
deferred. Write `N = a+m`. `startConfig` definitionally retags the *actual* G2p-d
`FixedGammaTargetPayloadLoopFoundation` configuration at that phase's own
length-only deadline, replacing only the control field; `handoff_exact` pins head
and tape to that endpoint. So this is a real phase-local provider, not one fixed
machine running from the raw pair input, and `roundClock N = 2*N-7` is this phase's
cost alone and omits every step inside the start configuration; clock composition
remains out of scope.

What the round does. The foundation left the tape in the `r = 2` instance of the
loop invariant `loopTape B x w zeros r` — counter prefix `[8,7+r]` marked, trail
`[8+zeros, 8+zeros+walk N zeros r)` blank, walking terminator at
`8+zeros+walk N zeros r`, register `[N+1,N+1+r]` holding its `r+1` digits — and
`round_step` carries that invariant to `r = 3`. Under a matching tag,
`gammaZeros? (Fin.append x w) = some zeros` with **`3 ≤ zeros`** (work remains) and
the round's own room `a+m+4 < tapeLength (pairLength a m) B`, after exactly
`roundClock (a+m)` steps the machine is back in `qLoop` at head
`8+zeros+walk (a+m) zeros 3` with the whole tape equal to `loopTape B x w zeros 3`.
The round tests the tape counter (`qCntL`/`qCntZ` scan left over the blank trail
into the gamma zero field), marks the first unconsumed zero, cell `10`, walks back
to the terminator, reads the next source, **appends** its bit to the register at
cell `N+2+r`, and advances the walking terminator when the source was physical.
Every branch is decided by the symbol under the head: no width, digit index, target
address, proof term, advice or producer mark enters the control. It carries only the
scanned source result: a physical bit until its write, and the physical-versus-blank
branch until `qLoop` re-entry. There is no arithmetic carry —
the register write is an append, and the decrement from `n+1` to `n` stays a separate
deferred phase; `qCarry_b` names that held source bit.

Source, clock and room. The source is the third payload digit, index `2` of the
block `[9+zeros, 9+2*zeros)`, i.e. the cell `11+zeros`, and there is such a digit
exactly when `3 ≤ zeros` — which is also what makes cell `10` an *unconsumed* gamma
zero, so the counter can grow. `source_pins` states the address direction only: with
`11+zeros < N`, `sourceCell N zeros = 11+zeros`, and with `N ≤ 11+zeros` it is the
boundary blank `N`. In the latter branch `round_step` leaves the terminator unmoved,
while `registerBit_source` identifies the appended digit as virtual `false`.
`roundClock N = 2*N-7` is **length-only** and
identical in both shapes: the virtual branch's `qVa`/`qVb` are pure padding, which
is what makes the cost independent of the source shape and of the width. It is an
*exact* time and not a time from which the endpoint persists — `qLoop` does not
absorb — so no deadline is exported and the endpoint may not be transported later.
Room is strictly wider than the foundation's because the register grows:
`room_iff` reads `a+m+4 < tapeLength (pairLength a m) B` as `3 ≤ a+B`, one cell more
than `2 ≤ a+B`; this is sufficient for the proved run, whose head reaches `N+4` and
writes there, and implies the foundation premise so the handoff stays available. By
the proof's table trace (not an exported all-times theorem), the decoded-width
`round_step` path never goes below cell `9`: the tag prefix and first counter mark,
cell `8`, are never scanned, while cell `9` stops `qCntZ`. `malformed_rejects` covers the retag of a failed gamma
scan: the retagged foundation rejection rejects again in one step, room-free, at the
boundary head (cell `8` when `a+m = 8`), on the unchanged content tape — with no
first-arrival direction and no converse.

Probes. Nonvacuity is independent of the endpoint theorems: two literal probes
first identify the phase-local start configuration for every budget from the landed
G2p-d foundation endpoint alone, then reduce this machine's own `run` by kernel
computation at `B = 0`. The physical probe (`zeros = 3`, `N = 15`) pins the third
counter mark at cell `10`, the head on the source cell `14`, the `true` it reads
carried in the control as `qClear1`, the vacated cell `13` blanked, the appended
digit written at `N+4 = 19`, a still non-terminal `qBackCont` one step before the
end, and the halt-free re-entry into `qLoop` at step `23 = 2*15-7`. The virtual
probe (`zeros = 3`, `N = 12`, `walk N 3 2 = 0`) pins the opposite schedule: the
source address is the boundary blank `12`, the padding states `qVa`/`qVb` are
entered, the appended digit at `N+4 = 16` is the virtual `false`, and `qLoop` is
re-entered at step `17` on the *unmoved* terminator `11`.

Deferred: the iteration of this round, the exhaustion finish that restores the
gamma zero field (`3 ≤ zeros` excludes `qFin` only during the first `roundClock N`
transitions, the exact `r = 2 → r = 3` segment), the complete target register,
the loop's own deadline, a cell-by-cell `r = 3` layout theorem (the endpoint is
already a full tape equality to the public `loopTape`, whose `r = 2` layout the
foundation pins), a first-arrival/strictness direction for the round, the all-times
clamp/footprint/budget package, the decrement from `n+1` to `n`, the room a full
loop needs (`N+1+zeros < tapeLength (pairLength a m) B`, assumed nowhere), and the
degenerate widths `zeros ≤ 2`. No converse is stated: nothing says that `qLoop` at
`roundClock N`, or the digit at `N+4`, implies `3 ≤ zeros`. Nothing here is
connected to `contentHeader?` or to any parsed header value and no pnp4 bridge
exists for this module. The public `startConfig` at `zeros = 2` can follow exhaustion
through `qFin` to `qDone`, but `zeros ≤ 2` and exhaustion remain outside the proved
theorem surface; `qDone` is not language acceptance. Nothing here is P-vs-NP mainline progress.
Three of those deferred items are discharged above: the iteration of this round and the
complete target register by G2p-e, and the exhaustion finish that restores the gamma zero
field by G2p-f. A fourth moves rather than closes: the premise
`N+1+zeros < tapeLength (pairLength a m) B` recorded here as assumed nowhere is now
assumed and characterized (`zeros ≤ a+B`), and G2p-f's `payload_exhausted` proves it
*sufficient* for a complete loop with the exhaustion finish included; whether that much
is *necessary* is still open, there being no footprint theorem. A fifth shrinks: of the
degenerate widths deferred here, `zeros = 2` is now inside G2p-f's `payload_exhausted`,
which needs only `2 ≤ zeros`, so only `zeros ≤ 1` stays outside the proved surface. The
rest still stand — a *length-only* loop deadline among them, since G2p-f's exported
persistence is from the width-dependent `totalClock N zeros` — including the two items
G2p-f discharges for its own phase only: the first-arrival/strictness direction and the
all-times clamp hold for the finish, where `qDone` absorbs, and not for this round, whose
endpoint sits in the non-absorbing `qLoop`.

**Part A G2p-d loop markers, foundation slice (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation`: one fixed
14-state, 42-row machine — every row pinned literally — that installs on the tape
the two markers a *self-stopping* gamma payload loop needs, and halts as soon as
they are in place. It is the finite preamble of that loop, not the loop: the round,
its iteration and the exhaustion finish are deferred. Write `N = a+m`. The target
register grows from scratch cell `N+1`; G2p-a wrote the leading `true` of `n+1`
there, G2p-b the first payload digit at `N+2`, G2p-c the second at `N+3`, so at a
decoded width `2 ≤ zeros` — the only width this slice proves anything quantified
about — exactly two payload digits, `9+zeros` and `10+zeros`, are consumed when
this phase starts, a constant of the phase ABI rather than data read off the tape;
the degenerate widths have consumed fewer, one at `zeros = 1` and none at
`zeros = 0`, the payload having fewer than two digits there. The markers are (i) a
**counter** inside the gamma zero field, a consumed zero rewritten
`some true` **left to right**, so that scanning left from the terminator
the first non-blank cell is an unconsumed zero while work is left and the last
consumed marker when the payload is exhausted — right-to-left marking would be
indistinguishable from tag cell `7`, which is also `some false` — and (ii) a
**walking terminator**, the `some true` at `8+zeros` moving one cell right per
*physical* source consumed with the vacated cell blanked, so the cell right of the
terminator is always the next source. `startConfig` definitionally retags the
*actual* G2p-c `FixedGammaTargetSecondPayload` configuration at the G2p-c
deadline, replacing only the control field (`handoff_exact` pins head and tape).
`markers_installed`: on a matching tag, `gammaZeros? = some zeros`, `2 ≤ zeros`,
and the inherited G2p-c room `a+m+3 < tapeLength (pairLength a m) B` (four
hypotheses), the machine has from step `exactClock zeros = zeros+7` on halted in
the absorbing `qDone` at head `8+zeros+walk (a+m) zeros 2` with tape
`loopTape B x w zeros 2` — the gamma zeros at `8` and `9` marked, the terminator
trail blank, the walking terminator installed, the three inherited register digits
untouched — and `markers_strict` excludes both terminal states at every earlier
step, so `zeros+7` is the *first* terminal time. `walk N zeros r =
min r (N-9-zeros)` covers the three source shapes in one closed form: both
consumed sources physical (`10+zeros < N`, terminator to `10+zeros`), only the
first physical (`10+zeros = N`, terminator to `9+zeros`), neither (`9+zeros = N`,
terminator unmoved); a virtual source costs the same three steps as a physical one,
which is what keeps the clock width-only. The advance is destructive only as far as
it moves, so the writes are shape-dependent: the both-physical shape overwrites
`9+zeros` and `10+zeros` with `some true` and blanks the first again, the middle
shape overwrites only `9+zeros` as the new terminator, and the tight shape
overwrites neither; the input terminator cell `8+zeros` is blanked exactly when
`9+zeros < N`, which is how `loopTape_layout` states it (a conditional conjunct, not
an unconditional one). The endpoint tape is therefore not `contentTape`, and
`loopTape_layout` pins it cell by cell (both marks, the conditionally blanked input
terminator, the walking terminator, the three register cells, blanks past `N+3`, and
the untouched tag prefix `[0,6]`). `markers_at_deadline` restates the endpoint at the
phase's length-only `deadline N = N`, and `malformed_rejects` inherits the G2p-c
rejection in one step, room-free. Room is inherited rather than needed: the head
never moves past `N`, which every budget allocates, so no `.right` move of this
phase can clamp; the premise (`room_iff`: `2 ≤ a+B`) is what makes the incoming
tape known and what allocates the register cells. Nonvacuity is independent of the
endpoint theorems: for both extreme shapes plus width zero, width one and a
malformed gamma, the surface tests first identify the phase-local start
configuration for every budget from the landed G2p-c endpoint theorems alone, then
reduce this machine's own `run` by kernel computation at `B = 0`. Deferred: the
round (counter test, source read, carry, register write), its iteration, the
exhaustion finish, the complete target register, the intended loop's own deadline,
the all-times clamp/footprint/budget package, the decrement from `n+1` to `n`, the
room a full loop needs (`N+1+zeros < tapeLength (pairLength a m) B`, assumed
nowhere), and the *quantified* endpoints of the two degenerate widths — where this
machine halts after two steps (`zeros = 0`) and after five with its counter mark
restored (`zeros = 1`), which is exercised here only by the literal probes at
concrete inputs — together with `malformed_strict`, the first-arrival direction of
the malformed branch, which this slice does not prove. The two surface obligations this slice
owed to the next one are now discharged by the G2p-d round slice above: all 42
table rows are restated literally in `check_table_rows` of the foundation's surface
test, and the 14 `Fin` state constants have direct `#print axioms` entries instead
of being reached only through `raw`/`machine`.
This foundation is **not** connected to `contentHeader?`: no theorem mentions a
decoded header field and no pnp4 bridge exists for it; `qDone` is an internal
endpoint, never language acceptance. Nothing here is P-vs-NP mainline progress.

**Part A G2p-c3 second-payload `contentHeader?` semantic bridge (infrastructure
only).** The pnp4 module
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetSecondPayloadBridge`
reads the landed G2p-c register against the parsed content header. Write
`N = a+m`. It has exactly four public theorems, all one-way implications out of
a decoded `contentHeader? = some (n, consumed)` and no converse anywhere; only
the last three reach a machine conclusion, because the first is machine-free.
`header_digits` is generic and machine-free — one hypothesis, any
`z : PrefixBitVec N`, no tag: a decoded header fixes `zeros` with
`gammaZeros? z = some zeros`, `consumed = 2*zeros+1`,
`2^zeros ≤ n+1 < 2^(zeros+1)`, the leading digit `(n+1).testBit zeros = true`,
and, for **every** `t < zeros`, the payload cell `9+zeros+t` read as
`(physicalSymbol z (9+zeros+t)).getD false = (n+1).testBit (zeros-1-t)`. The
`getD false` and the `t < zeros` guard are both load bearing: the decoder reads
its payload window through a virtual zero tail, so a payload cell at or past the
physical word is the digit `0` rather than a physical cell, and past the window
the truncated index `zeros-1-t` would repeat digit `0` at an address outside the
block. The other three theorems are about the landed machine at its
length-only, **phase-local** deadline `2*N`. Under a matching tag, a decoded
header with `3 ≤ n`, and exactly the room
`a+m+3 < tapeLength (pairLength a m) B` (four hypotheses), some `zeros ≥ 2` has
the header bounds above and the endpoint is `qDone` at head `7` on
`secondPayloadTape` with both digits taken from that same header, with cells
`N+1`, `N+2`, `N+3` holding `(n+1).testBit zeros`, `(n+1).testBit (zeros-1)`,
`(n+1).testBit (zeros-2)` — the three leading binary digits of `n+1`. Under a
matching tag and `consumed = 3`, with only the G2p-b room
`a+m+2 < tapeLength (pairLength a m) B` (three hypotheses), the two-digit G2p-b
register survives and every *allocated* cell past `N+2` stays blank, so no third
digit is written. Under a matching tag and the header `(0,1)` (two hypotheses)
the one-digit G2p-a register survives, with no room premise. Given a
decoded header the premise `3 ≤ n` is exactly `2 ≤ zeros`, since the exported
bounds make `zeros` the index of the leading digit of `n+1`; that equivalence is
derivable from the exported conjuncts and is *not* stated as an equivalence
theorem. The three concrete header hypotheses — `3 ≤ n`, `consumed = 3`, and
the header `(0,1)` — are jointly exhaustive over decoded headers, since
`header_digits` splits them by width: `zeros = 0` forces the header `(0,1)`,
`zeros = 1` forces `consumed = 3`, and `2 ≤ zeros` forces `3 ≤ n`. That coverage
is not free: the width-one branch assumes the G2p-b room and the positive branch
the wider one. Room, by contrast, is not implied by
the header — `room_iff` reads it as `2 ≤ a+B`, a condition on the `x` side and
the budget that a decoded header does not constrain — so `hroom` stays an
explicit premise. This bridge states no `qReject` theorem at all, and not for
want of room in one direction: on a matching tag,
`contentHeader? = none → qReject` at this deadline is already room-free from the
imports (`fixedGamma_header_contract` plus `malformed_at_deadline`, which takes
no room premise). What needs room is
the opposite direction, hence the `qReject ↔ contentHeader? = none` equivalence
that G2p-a states for the bootstrap: excluding `qReject` on a decoded header of
width one or more runs through the endpoint theorems, which assume `N+2` and
`N+3` allocated. `deadline` and `exactClock` remain phase-local: `startConfig`
retags the *actual* G2p-b endpoint configuration and embeds every earlier step,
which neither clock counts, so nothing here is a `UniformP` execution, a
runtime, or a clock for the composed pipeline. Nonvacuity is theorem-derived
rather than an independent machine reduction: for every budget, the probes pin
the one-digit register for header `(0,1)` (digit at cell `10`, with cell `11`
and every later allocated cell blank), `11₂` at cells `12,13` with cell `14`
still blank for `(2,3)`, `100₂` at `12,13,14` for `(3,5)`, `110₂` at `13,14,15`
for `(5,5)` (second payload digit the virtual zero at the boundary), and `111₂`
at `14,15,16` for `(6,5)` (second payload digit physical). No pnp3 machine,
source, or test file changed in this slice; only pnp3 documentation.
Deferred: the remaining `zeros-2` digits, the decrement of the stored `n+1` to
`n`, parser execution, `contentInput?`, `ContentAccepts`, language acceptance
from `qDone`, the raw-input composed machine and its clock, the all-times
footprint/budget package, `ContentVerifierBridge`, advice-freedom, and `NP`
membership. Nothing here is P-vs-NP mainline progress.

**Part A G2p-c2 second gamma payload digit, positive-width execution
(infrastructure only).** `FixedGammaTargetSecondPayload` now runs its fixed
14-state, 42-row control on the `2 ≤ zeros` route and proves that the second
gamma payload digit is copied into the target register. Write `N = a+m`. The
premises are explicit and satisfiable: a matching tag
(`tagMatches (Fin.append x w) = true`), a *decoded* width
(`gammaZeros? (Fin.append x w) = some zeros`) with `2 ≤ zeros`, and exactly the
room the run needs, `a+m+3 < tapeLength (pairLength a m) B` — equivalently
`2 ≤ a+B` by `room_iff`, so it fails at `a = B = 0` and at `a+B = 1`. Under
those premises `second_payload_exact` gives, for **every** `s` with
`exactClock N zeros = 2*N-7 ≤ s`, the endpoint state `qDone`, head `7`, and the
whole tape equal to `secondPayloadTape B x w b0 c`: every content cell restored,
the blank boundary at `N`, the register `true` at `N+1`, the G2p-b digit `b0` at
`N+2`, the second digit `c` at `N+3`, and blanks after `N+3`
(`secondPayloadTape_layout`). `second_payload_strict` excludes *both* terminal
states for every `s < 2*N-7`, so `2*N-7` is the **first** terminal time: the
former design constant is now derived row by row rather than assumed, and it is
the same value in all three shapes of the route (both payload cells physical,
source cell exactly at the boundary, first payload cell already at the
boundary). The copied value `c` is the *content* symbol at the logical source
address `10+zeros`, the second payload cell of the block `[9+zeros, 9+2*zeros)`
— `second_source_cell` pins `10+zeros = 9+zeros+1` and places it inside the
block under `2 ≤ zeros`, that direction only and with no converse — so `c` is
`(physicalSymbol (Fin.append x w) (10+zeros)).getD false`. That endpoint is
extensional, and the three shapes realize it by three different schedules. When
`10+zeros < N` the source is physical and the control really does read it: the
run steps *over* the first payload cell `9+zeros` in `qStepOne` and reads
`10+zeros` in `qRead`, and that bit is copied verbatim (`second_physical_exact`,
premise `physicalSymbol (Fin.append x w) (10+zeros) = some b`). When
`10+zeros = N` the source address *is* the blank boundary, so `qRead` is entered
and scans that blank, taking the virtual zero. When `9+zeros = N` the *first*
payload cell is already the blank boundary, so `qStepOne` reads *that* blank and
hands straight to the register: `qRead` is never entered, and `10+zeros` is then
`N+1`, the register cell — the head passes it, but in `qReg0` and over a tape
holding the register `true`, which is crossed rather than read as a source. Both
virtual shapes copy `false` (`second_virtual_exact`, premise `a+m ≤ 10+zeros`),
which is what `Option.getD` records for a `none` content symbol. Neither the
register `true` at `N+1` nor the G2p-b digit at `N+2` is ever taken as the
source: both are crossed in the register state that the selection already
fixed. Two more exports cover the local fit obligations of this branch:
`positive_width_head_range` bounds the head by `[7, N+3]` at every time, and
`positive_width_no_boundary_clamp` shows that no transition of the run clamps at
either tape end — the head *enters* the last allocated cell of the run, `N+3`,
on the preceding right move out of `N+2`, and the transition taken *at* `N+3` is
the write, which moves left, so no right move is attempted from the last cell.
Both are head facts, not a footprint: they say nothing about which cells may
differ from the incoming tape. The all-times footprint (`which cells differ`)
and `budget_independence`
remain deferred for every branch of this module. Scope caveats are unchanged and
still binding: `startConfig` is a **phase-local handoff** that definitionally
retags the actual G2p-b `FixedGammaTargetFirstPayload` endpoint configuration at
the G2p-b deadline (`handoff_exact` pins head and tape), so the provider is real
rather than synthetic, but this is *not* one fixed machine running from the raw
pair input; the length-only deadline `2*N` and the exact clock `2*N-7` are this
phase's cost alone and omit every step embedded in the start configuration;
clock composition stays out of scope; `qDone` is an internal endpoint, not
language acceptance; and no theorem has a converse — nothing here says that
`qDone`, or a written digit, implies `2 ≤ zeros` or a well-formed gamma.

The foundation of the same module is unchanged. This slice is the second part of
the G2p-c second-payload specialization (a separate line of work from the
generic payload round); the G2p-c1 part landed the table, the phase-local input
ABI, exact room, the phase-local clocks, and the two decoded widths at which the
machine provably makes no net payload or register write and leaves the tape
unchanged end to end (the anchor *is* blanked in flight and restored, so what is
proved is the absence of a net tape change). No width, digit index, bit, target
address, proof term, or clock enters the control; the eight positive-route
states (`qSeekTerm`, `qStepOne`, `qRead`, `qCarry0`, `qCarry1`, `qReg0`,
`qReg1`, `qBackReg`) that the foundation slice landed without exercising are
exactly the states the positive-width trace above now runs. The machine blanks
the tag cell `7` as its single anchor and steps onto cell `8`: a terminator at
`8` is width zero and a terminator at `9` is width one, and in both cases it
turns around, restores the anchor, halts in `qDone` at head `7`, and hands back
the tape it was handed unchanged. For those two widths the private traces keep
the head in `[7,9]`, but that read bound is internal: what is exported there is
the tape equality, which pins the net effect of the run and not the cells it
visited. The two sweeps have different delimiters: only the leftward `qScanLeft`
sweep is delimited by a cell the run maintains (the blanked anchor at `7`); the
rightward sweep is delimited in phases by cells the run maintains none of — the
input terminator at `8+zeros` ends the `qSeekTerm` scan at every width, and on a
positive width the layout blank at `N` then ends the walk across the content and
the first blank after the register, the target cell `N+3`, ends the register
walk, that last delimiter being consumed by the write rather than maintained.
Exports: all 42 rows pinned literally with the resource counts; the phase-local
handoff; `room_iff`; `exactClock` with values `3`, `5`, `2*N-7` by *decoded*
width, **all three** of which are now proved exact first arrivals (endpoint from
that time on, plus exclusion of both terminals before it); a malformed gamma has
no decoded width and is clocked separately by `malformedExactClock = 1`, which
`malformed_exact` and `malformed_strict` together prove to be its first terminal
time; `exactClock_le_deadline` under `3 ≤ N` (sharp at width one, and free in
scope since `N ≥ 9+zeros ≥ 11` on the positive branch); and full
state/head/tape endpoints for malformed, width zero, width one, and now the
positive width. The width-one endpoint additionally proves that every
*allocated* cell after `N+2` is blank, the target cell `N+3` included whenever
it is allocated — its premise allocates only `N+2`, so that claim is vacuous
exactly when `N+3` does not exist. Room premises stay exact per width and are
never inferred from a decoded header: width zero needs none, width one needs
only the G2p-b premise `a+m+2 < tapeLength (pairLength a m) B`, and the positive
width needs `a+m+3 < tapeLength (pairLength a m) B`. No theorem covers a width
without its premise, so nothing here says that `qReject` implies a malformed
gamma. Independent literal reduction probes identify the actual start
configuration for five concrete inputs from the landed G2p-b endpoint theorems
and then reduce this machine's own run by kernel computation, without invoking
any endpoint theorem of this module. Of the three foundation probes, the
width-zero and width-one probes pin the width dispatch at cells `8`/`9` and the
anchor blank and its restoration, the width-one probe alone also pins the target
cell `N+3` — which every one of these five inputs allocates — still blank at the
endpoint, and the malformed probe pins instead that the handed-over
configuration is in neither terminal state and that one step rejects in place at
the boundary head. The two positive-width probes walk the whole route in its two
extreme shapes. The physical probe (`zeros = 2` at `N = 13`) pins
`qStepOne` over the first payload cell, `qRead` at the source cell `12`, and the
`qCarry1` that records the source bit. The tight probe (`zeros = 2` at `N = 11`,
both payload digits virtual) pins the opposite schedule: `qStepOne` reads the
blank first payload cell and the next step is already `qReg0` at `12 = N+1`, so
`qRead` is never entered and the register `true` that its endpoint pins at that
address is crossed rather than read. Both then pin the head on the still-blank
target cell at step `N-4`, the digit written by the transition taken there and
visible at step `N-3`, a non-terminal control at step `2*N-8` — which, both
terminal states being absorbing, also excludes any earlier terminal arrival —
and the halt at step `2*N-7`. The `contentHeader?` reading of these endpoints is
now supplied outside pnp3, by the G2p-c3 bridge described above; this module
itself still states no pnp4 reader or parser fact and needed no change for it.
Deferred: the remaining `zeros-2` digits, the decrement to `n`, the all-times
footprint/budget package, parser execution, and `ContentVerifierBridge`. This is
a specialization, not an iterating round: the same rows cannot walk a general
payload, because that needs both a counter and an advancing source marker,
neither of which this control has. Nothing here is P-vs-NP mainline progress.

**Part A G2p-b first gamma payload bit (infrastructure only).**
`FixedGammaTargetFirstPayload` is a fixed 18-state, 54-row machine whose start
configuration only retags the actual G2p-a bootstrap configuration at the
bootstrap deadline; no width, bit, index, or proof enters the control. Write
`N = a+m`. The target register is filled most significant bit first from scratch
cell `N+1`, where the bootstrap wrote the leading `true` of `n+1`; this slice
adds its second digit at `N+2` and nothing else. On a matching tag the machine
blanks the terminator `8+zeros` as a marker and cell `7` as an anchor. Width
zero restores both without reading cell `9` and needs no room. Positive width
reads the payload cell `9+zeros`: a physical `some b` is carried as `b`, and
the blank boundary (`9+zeros = N`) as the virtual `false`. The machine steps over
the scratch `true` at `N+1` without reading it as source, writes the carried bit
at the target cell `N+2`, and restores the terminator and cell `7`. At the
length-only deadline `3*N` the endpoint is `qDone` at head `7`. For width zero
the tape is the bootstrap scratch tape. For positive width it is that tape with
the carried bit at `N+2`, under the exact premise
`a+m+2 < tapeLength (pairLength a m) B` (equivalently `0 < a+B`); the header does
not imply it, since it fails at `a = B = 0`. Malformed gamma ends in `qReject` at
head `N` on `contentTape`, with no room premise. All 54 rows are pinned
literally. At every time, clamp freedom and budget independence hold on every
tagged input whose positive gamma width has room (for both budgets in the
latter), and on decoded widths the head stays in `[6,8]` (width zero) or
`[6,N+2]` (positive width) with footprint `{7, 8+zeros, N+1, N+2}`, again
assuming room for positive widths. No theorem covers a positive width without
room, so nothing here says that `qReject` at this deadline implies malformed
gamma. The pnp4 companion
`ContentFixedGammaTargetFirstPayloadBridge` proves one direction for matching
tags. Suppose `contentHeader? z = some (n, consumed)` with `0 < n`
and the room premise. Then for some `zeros > 0` with `consumed = 2*zeros+1` and
`2^zeros ≤ n+1 < 2^(zeros+1)`, cells `N+1` and `N+2` hold `(n+1).testBit zeros`
and `(n+1).testBit (zeros-1)`. For the header `(0, 1)`, the register stays the
one digit of `1`. Part A G3b above later added the exact first-arrival surface
this slice had deferred: `exactClock N zeros` (`6` at width zero,
`2*N + zeros - 6` at a positive width), `malformedExactClock = 1`, the matching
`*_exact`/`*_strict` pairs at a positive width, at width zero and at a
malformed gamma, and
`strict_first_terminal`, which bundles them with `exactClock_le_deadline` and
the identification of the first-arrival configuration with the deadline one. The
remaining `zeros-1` payload digits, the decrement to `n`, clock composition, and
`ContentVerifierBridge` are not provided, and nothing here is P-vs-NP mainline
progress.

**Part A G2p-a terminator-to-scratch bootstrap (infrastructure only).**
`FixedGammaTerminatorScratchBootstrap` is a fixed 9-state, 27-row machine whose
start configuration only retags the actual G2m dispatcher configuration at the
dispatcher deadline. Write `N = a+m`. On a matching tag it normalizes the
dispatcher heads `6`/`7` to cell `8` and scans the gamma zeros. It blanks the
physical terminator at `8+zeros` as a return marker (the only blank cell below
`N`), scans to the blank boundary `N`, and writes `true` at scratch cell `N+1`,
which exists for every budget. It then steps back over `N`, scans left to the
marker, restores the terminator, and halts in the absorbing `qTerm`. The first
terminal time is exactly `2*N-11-zeros` and the length-only deadline is `2*N`.
The endpoint head is `8+zeros`, and the endpoint tape is `contentTape` changed
only at `N+1`. A failed gamma scan rejects after one step. Every row is pinned
literally, and an explicit schedule gives the exact state, head, and tape at
every time. The module proves strict first arrival, the head window `[6, N+1]`
on successful runs, and clamp freedom and budget independence for every tagged
input and budget. The pnp4 companion
`ContentFixedGammaTerminatorScratchBootstrapBridge` proves two facts at that
deadline, for matching tags. The bootstrap rejects exactly when
`contentHeader? = none`. For a header `(n, 2*zeros+1)` the scratch cell holds
`(n+1).testBit zeros`, the leading binary digit of `n+1`. Only that digit is
written: the shuttle crosses the payload cells, but neither decodes nor copies
their digits. Nothing here claims
parser execution, content acceptance, untagged behavior, or P-vs-NP mainline
progress.

**Part A G2o dispatcher header-value bridge (infrastructure only).**
`ContentFixedGammaPayloadDispatcherHeaderValueBridge` adds seven public
theorems. Two hypothesis-free reader iffs, covering width zero and
out-of-range windows, say that `VirtualZeroTailReader.readNatBE` is `some 0`
exactly when `allZeroSlice?` is `some true`, and that `allZeroSlice?` is
`some false` exactly when the read is `some payload` with `0 < payload`. The
hypothesis-free, subtraction-free iff
`contentHeader?_eq_some_iff_gammaZeros_payload` says
`contentHeader? z = some (n, consumed)` exactly when, for some `zeros` and
`payload`, the physical scan gives `gammaZeros? z = some zeros`, the payload
read at logical length `2*N+1` over `[9+zeros, 9+2*zeros)` is `some payload`
(cells at or past `N` read as virtual zeros), `n+1 = 2^zeros + payload`, and
`consumed = 2*zeros+1`. The one-way
`contentInput?_target_eq_contentHeader` has the single premise
`contentInput? codec z = some pr` (any codec, no monotonicity or injectivity)
and yields some `consumed` with `contentHeader? z = some (pr.1, consumed)`
together with `pr.2.n = pr.1`, so on a successful parse the target read by
`ContentAccepts` equals the header target. Each dispatcher iff has the single
premise of a matching tag: at the common deadline, `qReject` holds exactly when
`contentHeader? = none`; `qAllZero` exactly when
`∃ n zeros, contentHeader? = some (n, 2*zeros+1) ∧ n+1 = 2^zeros`; and
`qHasOne` exactly when the same header shape has `2^zeros < n+1`. Width zero
(header `(0, 1)`) and virtual payload cells are included. The gamma width and
the payload natural are never identified with the header target; the parsed
target equals the header target only through a successful `contentInput?`.
Nothing claims that the dispatcher stores or materializes `n` or the payload,
that any machine executes the parser, that an endpoint is acceptance of the
content language, or anything about untagged input, uniform heads, clock
composition, `ContentVerifierBridge`, advice freedom, or NP membership; this is
not P-vs-NP mainline progress.

**Part A G2n total dispatcher semantic bridge (infrastructure only).**
`ContentFixedGammaPayloadDispatcherSemanticBridge` connects the fixed G2m
deadline classifier to the strict content reader at the shared logical length
`2*(a+m)+1`. On matching tags, `qAllZero` is equivalent to the existence of a
decoded gamma width whose exact payload scan is `some true`, `qHasOne` is
equivalent to the analogous `some false`, and `qReject` is equivalent to gamma
failure (also to gamma failure conjoined with `contentHeader? = none`). The
proof covers width zero, derives fit from `gamma_contract`, and constructively
identifies physical true with a true padded read. It does not identify decoded
values, payload naturals, acceptance, parser correctness, untagged behavior,
uniform heads, or cross-machine clocks, and is not P-vs-NP mainline progress.

**Part A G2m dispatcher deadline/classifier (infrastructure only).**
`FixedGammaPayloadDispatcherDeadline` gives the fixed G2k/G2l dispatcher the
transparent common deadline `2*N*N`, constructively partitions every decoded
gamma payload into first-true, first-virtual, or exhausted branches, and lifts
all exact endpoints by absorption.  On matching tags it classifies the total
deadline endpoint with branch-specific heads: malformed at `a+m`, zero width
at `7`, and cleaned positive paths at `6`.  The physical endpoint equivalences
say `qHasOne` exactly when a physical true occurs in the payload window,
`qAllZero` exactly when none occurs for valid gamma, and `qReject` exactly when
`gammaZeros? = none`.  This adds no pnp4 reader/parser semantics or acceptance
claim and remains infrastructure rather than P-vs-NP mainline progress.

**Part A G2l dispatcher positive rounds (infrastructure only).**
`FixedGammaPayloadDispatcherRounds` now proves the same-machine, zero-offset
positive physical-true, first-virtual, and full-false exhausted executions of
the fixed G2k dispatcher from its actual G2a-derived start configuration. The
strict cleaned endpoints restore literal content at head 6, and the public
guards exclude `k = 0` and the final `k = zeros` boundary from pending formulas.
No semantic iff, parser/decode theorem, length-only cap, or pnp4 claim is added.

**S11 one-gate acceptance closure (infrastructure only).** The single reviewed
unfreeze of the frozen TMVerifier tree added
`TuringToolkit/GateOneAcceptsClosure` and its literal probes, closing
acceptance of the one fixed gate machine for *every* request. The two
endpoints are hypothesis-free — the sole binder is `r : G1Request`:

```lean
g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome

g1CS_accepts_iff_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.WellFormed
```

The first says the real `G1M` run, from the real initial configuration on the
standard encoded point and read after exactly its own unchanged
`g1Clock (encodeG1 r).length` steps, carries the accepting state exactly when
the pure result `r.spec` is defined; the second composes that with main's
pre-existing pure `spec_isSome_iff`, so the verdict is exactly
`r.WellFormed = r.Canonical ∧ r.operandsInBounds`. This is main's T1
transducer convention: a defined
`false` accepts exactly as a defined `true` does, because both output-done
handoffs enter the same literal accept state, and the result *value* sits on
the output cell rather than in the verdict. Among the nonaccepting requests
only the noncanonical class is a literal rejection; a canonical request with an
out-of-range operand idles at a `bOOB` boundary that is proved distinct from
both sinks. Acceptance is **exact-step, not halting** — no theorem says the
machine halts — and every statement is scoped to the image of `encodeG1`, so
nothing is claimed for a physical word outside that image and this is not a
language-membership theorem. No transition row, clock, step count, head
position, encoder or `GateN` declaration changed. This is one gate, not the
multi-gate chain: it is unrelated to the Part A uniform gamma track above, it
adds no `GateN`, `ContentVerifierBridge` or content-verifier claim, it reduces
no pnp4 source obligation, and it is not P-vs-NP mainline progress.

**GN-E2-4a values rewind (infrastructure only).** The second authorized
unfreeze slice continues the frozen GN chain one phase past the landed
`recordDone` endpoint. It activates that row — previously a stationary
self-loop — into a read-only right-to-left pass that anchors on the word's
leading `bof` and stands on p0 of the frame after it, in a `valuesEntry` state
that was a new dormant arrival **when this slice landed** — GN-E2-5a below has
since activated it into the values/tail pass, exactly as stage (a) recorded in
`GateNValuesRewind.lean` — with the physical tape left as the *same term* it
was at `recordDone`. `gnCS_encodeGN_valuesEntry_exact` is genuine
`TM.runConfig (M := GNM)` execution from the real
`GNM.initialConfig (gnPoint (encodeGN r))` for exactly `gnValuesEntrySteps r g`
rows, for the actually selected first gate supplied by `hg`. The point of the
phase is only that the current values the installer still owes the delegated
request word sit at the left end of the word while the head was at the right
end. **No value is copied and no frame is written** *in this slice*, and
GN-E2-4a itself adds no values or tail writer, completed request word, extended
exit dispatcher, launch, delegation, commit, next-gate loop, total installer
clock, verdict, acceptance, or any claim that the pure evaluator
`evalGNProgram` is executed by the machine. Those exclusions are scoped to
GN-E2-4a as it landed and are **not** the state of the tree at this head:
GN-E2-5a below adds the values/tail control, the extended exit dispatcher and a
written tail. It still copies no value on the proved path, and `evalGNProgram`
is still not executed by this machine.

**GN-E2-5a values/tail control and the input-free first request
(infrastructure only).** The third authorized unfreeze slice installs the
complete finite values/tail writer control in the frozen GN machine and proves
the tail phase. `gnCS_encodeGN_firstRequestReady_exact` is genuine
`TM.runConfig (M := GNM)` execution from the real
`GNM.initialConfig (gnPoint (encodeGN r))` for exactly
`gnFirstRequestReadySteps r g` rows, landing in state `requestReady` at head
`4 * (F + R + m + 2)` with the complete physical tape pinned, under exactly two
premises: `hg : r.program.gates[0]? = some g` and `hinputs : r.inputs = []`.
It writes the fixed `[output false, finish]` tail; the room fact is proved
internally, not assumed. **The finite data-copy rows are installed and pinned
but dormant** — with `r.inputs = []` the classification meets the first
reserved output slot immediately, so no theorem in this slice executes them,
and the zero-input literal probe is a nonvacuity witness for execution, **not**
a witness of a values copy. At the GN-E2-5a split, the per-value copy round,
list induction and nonempty-request capstone were assigned to GN-E2-5b.
The authorized GN-E2-5b slice proved one copy and its real-input endpoint;
GN-E2-5c now executes the list induction and completes the nonempty request. The older label `E2-4b` is retired
in favour of that name. The frozen `GateNValuesRewind.lean:531` owner label
now also says `GN-E2-5b`, through the separate two-stage docstring migration
recorded in `pnp3/Docs/TMVERIFIER_FREEZE.md`. Historical references in that
record and `TMVerifier_Session_Plan.md` retain their dated context. There is no rewind to
the scratch `bof`, launch, delegation, commit, next-gate loop, total installer
clock, verdict, acceptance, language-level statement, or any claim that
`evalGNProgram` is executed by this machine.

**Historical engineering priority (GN-E2-5a, 2026-09-29).** The one-tape
`pnp3/Complexity/TMVerifier/` tree was frozen at Git tree `14525256`, the
subtree of commit `1e7fe405`. This paragraph records the GN-E2-5a snapshot;
the current GN-E2-5c pin and validation limits are in the header and
`pnp3/Docs/TMVERIFIER_FREEZE.md`. At that date there had been five
unfreezes since `42c59881` (the reviewed S11 one-gate acceptance closure; the
authorized GN-E2-3b body-driver slice, landed by PR #1777 as merge
commit `48151689` on 2026-09-23, an ancestor of this branch, so its history was
preserved: its exact-head local `./scripts/check.sh`, its two independent
read-only reviews, the owner attestation and the `tmverifier-unfreeze` label
were recorded before that merge, while local Git records neither the remote gate
results against its final head nor the required PR review, so neither is
claimed here; the authorized GN-E2-4a values-rewind slice, whose stage (a)
landed the new frozen bytes and whose stage (b) repinned the freeze onto them,
and which **PR #1801 merged into `main` on 2026-09-28 as the merge commit
`71179c6d`**, preserving history, so its provenance commit `b35bdca2` and its
final head `a312622f` are both ancestors of `main` and the post-merge
provenance audit `git merge-base --is-ancestor b35bdca2 origin/main` exits `0`
— an exact-head Codex **APPROVE**, an exact-head Fable 5.1 **APPROVE**, a
complete local `./scripts/check.sh` in which all checks passed,
the owner's full-SHA attestation and the `tmverifier-unfreeze` label were
recorded against its pre-merge head `6718b422`, the docs-only final head
`a312622f` that followed carries no gate result of its own, and local Git
records neither the remote gate results for that merge nor the required PR
review, so neither is claimed here — that record's last word on the review is
that PR #1801 carried no approving review, its only GitHub review being an
automated `qodo-code-review` pass submitted as **COMMENTED**, which is not an
approval, while the separate Qodo summary comment is a generated description and
not a review at all — and `main`'s copy of that slice's record, which this
branch's copy predated, is the copy the first of the two integration merges
described below brought into this tree and is authoritative for it; and the
authorized
GN-E2-5a values/tail writer slice described above, whose stage (a) `11dc8e82`
landed the new frozen bytes and whose stage (b) `311abc6b` repinned the freeze
onto them; and the owner-docstring correction, whose stage (a) `1e7fe405`
changes only the owner label and whose separate stage (b) repins it). **History through
`bceb38db98cf7d43fda523384969d3f320ed4ced` (review inventory recorded
2026-09-29): no GN-E2-5a head has a full `./scripts/check.sh` of its own**.
Stage (a) ran targeted builds, stage (b) the freeze checker; the docs-only
corrections `3195ffc1`, `40ea2346` and `51db7753` recorded the earlier local
check suites and no Lean build. The separate `bceb38db` author account records
only whitespace, doc-honesty and read-only freeze checks, with no full check or
build; it does not inherit the earlier shell/policy tests or reviewer runs.
`TMVERIFIER_FREEZE.md` gives each account and its evidence. One complete run is
nevertheless on record for this branch's content, logged between `4abaac92`
and `d01e2c3e` at
`/root/pnp2-agent-reports/gn-e25-4aba-full-check.log` — this slice's own
118-object freeze pin in its preflight, all seventeen numbered steps, no
`error:` line and a closing "All checks passed" — but the log names no commit,
branch or working directory, its fingerprint matches the audit-command layout
at `4abaac92` without establishing exact bytes or checkout identity, and its
exclusivity is unestablished, so it is no head's gate result and does not cover
the G3l Lean modules `d01e2c3e` merged in;
`TMVERIFIER_FREEZE.md` states exactly what it does and does not establish. The
exclusive full run at the final head is still owed, and GN-E2-4a's passing run
at `6718b422` transfers nothing to it. At GN-E2-4a's stage-(b) head
`e2c3ee33`, Codex and
Claude reviews were reported as **APPROVE**, and an earlier Codex pass returned
**REQUEST_CHANGES** on documentation; at its docs head `4e182c03`, both the
Codex and Claude reruns returned **BLOCK** on contradictory review claims. At
GN-E2-5a's stage-(b) head `311abc6b` the two exact-head reviews split: Codex
**APPROVE** with one P3 documentation note, Claude **BLOCK** on four
documentation findings, neither reporting a Lean, execution, surface or
freeze-content defect; the docs-only correction `3195ffc1` resolves those four.
Two further exact-head reviews ran at the second integration-merge head
`d01e2c3e` and split the same way: Codex found no blocking theorem or
freeze-content defect and states that merge readiness is not established, while
Claude returned **BLOCK** on two documentation-consistency findings with five
further accuracy findings, again reporting no Lean, execution, surface or
freeze-content defect; the docs-only correction `40ea2346` resolves all seven.
One further exact-head review ran at that correction, `40ea2346`: Codex reported
two **P2** documentation findings — the freeze header's blanket denial of any
review at the later heads, and this file's, the freeze record's and the session
plan's blanket denial of any full check — with no APPROVE/BLOCK label and again
no blocking theorem or freeze-content defect, while a second run there ended at
its turn limit with no verdict; `51db7753` fixes both findings. The exact-head
Codex review of `51db7753` returned **FINDINGS**, one P3 and no P0–P2: the
historical log establishes layout agreement, not byte identity. `bceb38db`
fixes that P3. At `bceb38db`, Codex initially returned **PASS**, while Opus
returned **FINDINGS** on P2-A (author-check attribution) and P2-B (stale review
history). The subsequent Codex adjudication upheld both and the nonblocking
six-of-eight scan wording nit, acknowledged its earlier documentation PASS was
too broad, and qualified Opus's stronger claims about absent checks and reviews.
None reported a blocking theorem or freeze-content defect. The freeze record
names the reports, evidence, limits and dispositions, including that the
historical author scan covers six of eight changed `.lean` files, not a
retroactively enlarged scan. The later first-parent heads through `bceb38db`
are `3195ffc1`, `4abaac92`, `d01e2c3e`, `40ea2346`, `51db7753` and `bceb38db`.
No review is claimed for `3195ffc1` or `4abaac92`; reviews apply only to their
named SHA, and **none reviews or approves a later documentation correction SHA**.
GN-E2-5a still owes a fresh exact-head review of the corrected head,
the complete `./scripts/check.sh`, final-head remote CI and freeze-policy
success, the owner's exact full-SHA attestation and label, the required PR
review, and a non-squash merge preserving both stage commits, with the owner's
attestation and label reissued against whatever head is finally merged — none is
claimed). The `≤ 1500` changed-Lean-LOC gate is measured against the current
merge base with `main`, which was `13f36c1d` — GN-E2-5a's own base — once
PR #1801 merged, became **`71179c6d`** when this branch merged that `main` in,
and is now **`9445a93e`**, the `main` that PR #1802 created when it merged the
Part A G3l origin-alignment handoff, because this branch has since merged that
`main` in too; the measurement is the same at all three and the gate is
**green**: **1497 changed Lean lines (1467 added, 30 deleted) across 8
modules**, inside that bound and the `≤ 10`-module bound. Neither merge of
`main` enlarged it — `main`'s G3j and G3k modules became shared history and left
the diff at the first, and its G3l module and that module's surface test did the
same at the second — and a measurement against either superseded base,
`13f36c1d` or `71179c6d`, would now count those main-only modules too, so
neither is the prescribed one and neither is reported as one. The gate was
recorded **red, not waived**, before PR #1801, at 2496 lines against the
older merge base `20850b93`, because GN-E2-4a's 1041 then-unmerged lines sat
underneath GN-E2-5a's 1497, and that merge cleared it exactly as the record
said it would. These migrations, this prose correction and both integration
merges of `main` are **Infrastructure only**: neither
`VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound` is reduced.
At that date GN-E2-5b and later construction required fresh authorization.
GN-E2-5b subsequently covered one value; GN-E2-5c now executes all values and
the first-request tail. Later gate-by-gate construction remains deferred.
Active model-repair work otherwise uses the versioned uniform complexity
foundation outside that tree.

**P1a/P1c uniform foundation (infrastructure only).** The independent namespace
`Pnp3.Complexity.Uniform.V1` provides finite `UniformTM` data with the distinct
symbols `some false`, `some true`, and blank `none`; same-budget exact/within
decision semantics; `polyClock`; a versioned `UniformP`; complement closure;
and an arbitrary-length parity scanner proving that input length is observable.
P1c explicitly codes the finite machines, proves the versioned `UniformP`
languages countable, and directly diagonalizes a length-only language outside
that class. See `pnp3/Docs/UniformP_V1.md`. This does not rebind, characterize,
or change the legacy canonical repository `P`/`NP`, define `UniformNP`, prove a
lower bound, or reduce a pnp4 mainline source obligation.

**P2-1 Uniform V1 pair codec (infrastructure only).**
`Complexity.Uniform.V1.PairEncoding` encodes `(x,w)` as false-tagged input
bits, one true separator, and the untagged witness.  Its executable structural
decoder has exact image, malformed-word, dependent roundtrip, and packed
cross-length injectivity theorems, plus direct initial-tape layout bridges.
The complete finite words are uniquely decodable, but the family is not
prefix-free because witness extension extends an encoding.  This slice adds no
relation/verifier or parser machine, does not define `UniformNP`, prove
`P ⊆ NP`, migrate canonical definitions, or reduce a pnp4 mainline obligation.

**P2-2 advice-free relation semantics / versioned `UniformNP` (infrastructure
only).** This slice defines one length-indexed `WitnessRelation`, its
total raw-word language through the P2-1 decoder, and `VerifiesRelation` over
every raw length and word at `polyClock verifierExponent N`. Malformed words
and false relation answers require literal rejection. `UniformNP` fixes one
relation, one finite machine, one verifier exponent, and an independent
witness exponent before inputs, with witness bound
`m ≤ polyClock witnessExponent n`. Named wrappers and paired axiom roots cover
all seventeen P2-2 theorems. Executable controls distinguish acceptance,
rejection, and timeout. This slice adds no parser machine,
`UniformP ⊆ UniformNP`, canonical `P`/`NP` rebind, pnp4 theorem, or lower-bound
claim.

**P2-3a fixed Uniform V1 pair-parser executable core (infrastructure only).**
`Complexity.Uniform.V1.FixedPairParserCore` adds one fixed ten-state parser,
its exact table/public-step bridge, exact `2*N+1` clock and `3*N+2`
exact-clock tape allocation, and only closed malformed/valid exact-run and
whole-tape-restoration capstones. The namespaced surface wrappers live in
`Tests.UniformV1FixedPairParserCoreSurfaceTests`, with paired direct/wrapper
roots in the central axiom audit. This slice proves no all-length parser
correctness, universal decoder equivalence, arbitrary-budget theorem,
parser/verifier composition, relation verification, `UniformP` inclusion,
gate bound, or P-vs-NP mainline result.

**P2-3b universal exact Uniform V1 pair-parser correctness (infrastructure
only).** `Complexity.Uniform.V1.FixedPairParserLanguage` gives independent DFA
and inductive-grammar semantics and proves their equivalence to dependent
`decodePair` success. `Complexity.Uniform.V1.FixedPairParserCorrectness` proves,
for every raw `y : Bitstring N`, the exact `clock N = 2*N+1` final state, strict
absence of either public terminal at every earlier step, head-zero and full
allocated-tape restoration, exact acceptance/rejection iff decoder
success/failure, exact `DecidesAt`, and only then derived `DecidesWithin`. The
proof has a dedicated empty-input root and positive-input forward/rewind
invariant roots. It introduces no parser/verifier composition, relation
verification, class inclusion or migration, pnp4 theorem, or circuit bound.

**P2-3cA ambient-budget fixed-parser transport (infrastructure only).**
`Complexity.Uniform.V1.FixedPairParserAmbient` relates the exact-clock tape to
every ambient budget `B` satisfying `clock N ≤ B` through explicit dependent
`Fin` embedding/projection and a four-clause blank-extension invariant. It
proves through-clock simulation of the same fixed parser, full ambient padding
blankness, exact final state/head/tape restoration, strict preterminality,
decoder-equivalent literal acceptance/rejection, and `DecidesWithin` using
`clock N` as an explicit witness. It introduces no configuration casts,
runtime advice, generic verifier budget theorem, parser/verifier composition,
relation verification, class inclusion, pnp4 theorem, or circuit bound.

**P2-3cB1 generic bounded budget transport (infrastructure only).**
`Complexity.Uniform.V1.BudgetTransport` proves for every fixed `UniformTM` that
a run of `s ≤ C` transitions from canonical head zero is a genuine blank
extension when the budget grows from `C` to `B`. The proof derives unit head
speed and strict right room at every pre-step `r < s`, so it does not assume an
unrestricted budget theorem. Exact-time accept/reject/decision predicates are
invariant, while within-budget predicates are transported only forward using
the same witness. This adds no provider, advice, machine family, combined
parser/verifier machine, relation/class theorem, pnp4 result, or gate bound.

**P2-3cB2 routed combined-machine constructor and parser handoff
(infrastructure only).** `Complexity.Uniform.V1.CombinedMachine` builds one
fixed machine from a fixed verifier `V` using exactly `8 + V.stateCount`
controls: eight nonterminal parser controls followed by all verifier controls.
Parser-accept rows restore cell zero and enter injected `V.start` in the same
transition; malformed/empty paths enter injected `V.reject`. The verifier side
maps `V.step`. Full same-budget verifier embedding, bounded parser-prefix
translation, successful full-configuration handoff, and literal malformed
rejection are proved. No host restart or extra handoff step exists. This slice
does not yet prove the total verifier suffix, relation verification, class
inclusion, pnp4 result, or gate bound.

**P2-3cB3 total combined correctness and relation packaging (infrastructure
only).** `Complexity.Uniform.V1.CombinedCorrectness` proves that the routed
machine executes one parser prefix of `2*N+1` steps and one verifier suffix of
`N^c+c` steps with no additional handoff. Malformed raw words remain literal
combined reject; successful words execute the embedded verifier at the same
ambient budget. The exact total clock is dominated by `polyClock (c+3)`, while
`c+2` fails at length one. Consequently every fixed verifier satisfying
`VerifiesRelation V c R` yields
`VerifiesRelation (combinedMachine V) (c+3) R` on all raw words. This is still
generic infrastructure: it does not construct the concrete tree-circuit
relation body, bridge to the legacy TM/framing model, prove class inclusion,
add a pnp4 theorem, or establish P versus NP.

**Part A P2-4a guarded content/tree witness relations (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.TreeCircuitContentWitnessRelation` packages
the content and tree-prefix semantic Booleans as distinct V1 witness relations,
rejecting every noncanonical certificate length. The content relation uses a
computable query-first concatenator; a separate proposition-level theorem
identifies it with canonical `concatBitstring`, whose historical definition is
noncomputable. This constructs no verifier machine, proves no equality between
the two semantic relations, supplies no `ContentVerifierBridge`, and establishes
no NP membership or lower bound.

**Part A G0-B1 explicit content-window cap (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixExplicitCap` derives transparent,
choice-free exponents directly from `thresholdPoly`, the concrete witness width,
and `treeMCSPPrefixM`. Under successful authoritative content semantics it bounds
both the header-designated window and the actual dependent parser target by
`N ^ contentCapExponent k + contentCapExponent k`. The exponent is executable
data fixed by `k`, not an existential witness or runtime advice. This does not
yet implement compressed virtual-zero-tail semantics, compile a verifier to V1,
or supply `ContentVerifierBridge`.

**Part A G0-B2a virtual-zero-tail reader core (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentVirtualZeroTailReaderCore` implements
the strict content readers and complete tree-prefix parser against a physical
source plus an independent logical extent, without constructing a padded
vector. Its whole-result theorems recover the frozen operations on `padWord`,
including every failure branch. This is the semantic reader/parser layer only:
it does not yet compute capped schedules, evaluate the concrete codec, construct
a V1 machine, prove a runtime bound, or supply `ContentVerifierBridge`.

**Part A G0-B2b1 capped arithmetic (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentCappedArithmetic` adds exact
success/overflow contracts for capped naturals, addition, multiplication,
binary length, and exponentiation by halving. It avoids evaluating an uncapped
power before checking its intermediates. These are source-level arithmetic
facts, not yet the concrete content-size record, bounded semantic verifier,
V1 machine, runtime proof, or `ContentVerifierBridge`.

**Part A G0-B2b2 concrete capped size records (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentCappedSizes` computes every concrete
threshold/table/witness/gamma/index/ambient field behind the merged cap-aware
arithmetic. Its exact `some` and strict-overflow `none` biconditionals tie the
executable pipeline to authoritative `treeMCSPPrefixM`; successful results also
retain `witnessBits ≤ M`, `tableLen ≤ M`, and cap corollaries. This does not yet
construct the bounded content parser/semantic verifier, a V1 machine, a runtime
proof, or `ContentVerifierBridge`.

**Part A G0-B2c bounded content semantic glue (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.BoundedContentSemanticVerifier` feeds the
merged capped `ContentSizes` result into the virtual-zero-tail parser at exact
logical extent `sizes.M`. Its strongest unconditional parser theorem is the
cap-filter characterization; plain parser equality is available only under a
target-fit or semantic-acceptance hypothesis. Its source-level Boolean checker
is proved extensionally equal to authoritative `contentSemanticAccepts`. This
still does not provide a fixed `UniformTM`, tape-level evaluator, runtime proof,
`VerifiesRelation`, or `ContentVerifierBridge`.

**Part A tagged/content framing ABI (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ThresholdTaggedContentFraming` explicitly
connects canonical V1 `encodePair` inputs to headerless authoritative
`contentSemanticAccepts` and makes malformed raw words evaluate to `false`.
This closes a proposition-level framing equation, not an operational tape
conversion. `CombinedMachine` still hands its verifier the unchanged tagged
word, so a fixed compactor/evaluator and blank-preserving legacy simulation
remain open.

**Part A fixed pair-concat sentinel phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairConcatSentinel` is a closed seven-state
`UniformTM` that preserves every input bit, writes a positional `some true`
marker at the first blank cell, and returns to head zero in exactly `2*N+1`
steps. Full-configuration, all-prefix footprint, budget-independence,
preterminality, literal acceptance, and `polyClock 2` decision theorems are
proved, including `N = 0` and budget zero. This is only the reusable marker
phase: it does not remove pair tags, compact `x ++ w`, evaluate the content
relation, or provide the legacy bridge. The all-budget exact theorem includes
budget zero; the exported blank-after-marker lookahead fact separately assumes
positive budget so cell `N+1` actually exists.

**Part A fixed separator cursor (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairSeparatorCursor` is a closed five-state
`UniformTM` that consumes the sentinelized tagged pair layout, validates the
alternating query tags, confirms a nonblank successor for the separator, and
halts with the head exactly on that separator in `2*n+2` steps. It preserves
the entire tape and proves an exact valid trace plus an exact positive-budget
malformed trace, footprint, budget-independence, no-clamp, and strict terminal
behavior. Separator-first
deletion is intentionally rejected because it can collapse different pair
splits to an identical configuration. This cursor locates the split but does
not yet remove tags or compact the headerless payload.

**Part A fixed separator-hole phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairSeparatorHole` is a closed three-state
one-transition machine whose standalone start is obtained by proof-level
retagging of the validated cursor handoff. It blanks only
the separator cell, and leaves the head on the resulting interior hole. Query
tags/data, witness, sentinel, and padding remain at their original addresses.
The hole is unique only through the sentinel (global uniqueness is false with
extra padding); the final Nat-indexed tape view is injective in the original
pair, so the separator-deletion collision does not apply. This phase does not
remove query tags, shift the witness, or complete headerless compaction.

**Part A fixed all-tag-removal phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairTagRemoval` is a closed nine-state
machine that repeatedly compacts query data rightward into the separator-hole
region. At exact clock `n*(n+5)+2`, the tape is
`[n+1 blanks][query][witness][marker]`: every query tag is gone and query plus
witness are physically contiguous, but the content block remains offset from
the origin. The phase proves exact full execution, footprint, budget
independence, strict terminal timing, right-clamp avoidance, and this
construction's single left-origin clamp. It does not yet shift the contiguous
block to cell zero, evaluate the content relation, or provide the legacy bridge.

**Part A fixed one-cell origin-shift bootstrap (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairOriginShiftBootstrap` is a closed
seven-state rolling-hole machine that shifts the entire contiguous
`query ++ witness ++ marker` block one cell left. At exact clock
`4*n + 3*m + 5`, it transforms `[n+1 blanks][query][witness][marker]` into
`[n blanks][query][witness][marker]`, preserving order and leaving no interior
hole. The final right command clamps exactly when `B = 0`; otherwise it moves
to the physical blank after the erased old marker. The phase proves exact
execution, first terminal, footprint, scoped cross-budget accounting, exact
layout, and fixed-extent recovery. It is not full origin alignment when
`n > 0`, and it does not claim that headerless concatenation recovers a varying
query/witness split.

**Part A fixed complete origin-alignment execution core (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment` is a closed 26-state
machine that repeatedly performs structural origin probes and stable whole-block
left shifts. At exact clock `(10*n + 7)*(n + m + 1) + 3*n`, it reaches literal
accept with head at cell zero and the complete tape
`[query][witness][marker][blanks]`. The machine uses no runtime counter or
advice and never identifies the marker by its Boolean value. This foundation
slice proves the exact predecessor handoff, fixed table/resources, polynomial
clock identity, and exact full-configuration run. First-terminal, post-clock,
footprint, clamp, cross-budget, layout-projection, and recovery surfaces are
intentionally deferred to the dependency-closed safety follow-up; this slice
alone is not yet the final framing bridge or semantic verifier.

**Part A fixed complete alignment safety A (infrastructure only).**
The first safety slice for `FixedPairOriginAlignment` now exposes exact literal
final fields and the full origin-aligned tape layout, proves that the declared
clock is the strict first terminal time, proves absorbing exact post-clock
execution, bounds the complete head/write footprint through the clock, and
classifies all boundary clamps. In particular, the time-2 right move clamps
exactly when `B = 0`, and the sole left clamp occurs at source time `clock-3`.
Cross-budget synchronization, fixed-extent recovery, the explicit zero edge,
and the bundled complete phase contract remain in Safety B.

**Part A fixed complete alignment safety B (infrastructure only).**
The second safety slice for `FixedPairOriginAlignment` proves exact
cross-budget accounting: equal zero/nonzero budget classes agree from time zero,
and all budgets synchronize from time three through the clock in state, numeric
head, and equal-address tape values. It proves fixed-extent recovery of the query
and witness without claiming varying-split injectivity, exposes the exact
`n=m=B=0` edge, and bundles the complete predecessor handoff, endpoint,
first-terminal, footprint, inclusive blank boundary, and literal output contract.
Together with Safety A, the origin-alignment machine now has its full advertised
execution and safety surface; semantic evaluation and the final framing bridge
remain separate.

**Part A fixed trailing content-marker erasure (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase` is a closed
four-state machine that scans the origin-aligned nonblank block, locates its end
structurally via the following blank, validates and erases the trailing literal
marker, and accepts at exact clock `n+m+3`. The scan treats data zero and one
uniformly and never identifies a marker by Boolean value. The final tape is
physical headerless `query ++ witness` at the origin with every allocated cell
from `n+m` onward blank. The phase proves exact full execution, strict first
terminal, absorption, no clamps, complete footprint, unconditional budget
independence, fixed-extent recovery, the empty zero-budget trace, and a bundled
contract containing `Fin.append`, post-clock, and budget clauses. It is not a
universal malformed-format validator and makes no varying-split injectivity
claim.

**Part A fixed content tag gate (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedContentTagGate` is a closed
15-state phase that rewinds the marker-erasure output in place, restores every
content bit, and checks the fixed eight-bit parser tag `10110010`. Its exact
common deadline is `3 * (n + m) + 7`; it proves each earlier malformed terminal,
no right clamp, the unique origin-detection left clamp, tape preservation,
blank-suffix preservation, and cross-budget equality. Its local accept is only
a handoff at header offset eight, not semantic acceptance. The pnp4
`FixedContentTagGateCorrect` bridge proves that every local rejection is sound
for both `contentSemanticAccepts` and `boundedContentSemanticAccepts`, including
the length-seven virtual-zero case where the padded tag itself matches but the
gamma header still fails. This begins concrete semantic activation; gamma
parsing, capped sizes, witness addressing, circuit decoding/evaluation,
phase composition, and V1-to-legacy simulation remain separate.

**Part A G1 fixed-content gamma terminator scan (infrastructure only).**
`FixedContentGammaTerminator` is a real three-state, nine-entry fixed-control
scan. Under a successful tag-gate handoff it receives the unchanged tape and
head at cell eight, accepts on the first physical `true`, rejects on the first
physical blank, never writes, and exposes exact first-terminal, tape, head,
absorption, and cross-budget contracts. Under that same successful-handoff
premise, `FixedContentGammaTerminatorCorrect` identifies the machine verdict
with `contentHeader?` presence and factors both semantic verifiers through the
header-presence predicate independently of machine execution.
This phase does not read the payload, materialize the decoded target, call
`computeContentSizesCapped`, check a cap, compose the phases, or claim capped
execution. Header presence is the cap-facing boundary for this slice.

**Part A G2a fixed-content gamma anchor (infrastructure only).**
`FixedContentGammaAnchor` is a six-state phase retagged from merged G1. On G1
success it walks left across the zero run, checks tag cells 6=true and 7=false,
erases exactly cell 7 as a recoverable marker, returns across the unchanged
zero run, and accepts on the same terminator at clock `2 * zeros + 5`. Its
common absorbing deadline is `2 * (n + m)`; G1-none rejects at the content
blank in one step. No payload traversal/value decoding, virtual payload read,
capped arithmetic, or semantic acceptance is claimed. G2b must not write
`none` in its counter zone and must restore cell 7 before a `contentTape` phase.

**Part A G2b fixed gamma-payload cursor core (infrastructure only).**
`FixedGammaPayloadCursorCore` is a 14-state, 42-entry fixed-control tracer
retagged from the exact successful G2a final configuration. It executes the
zero-width case with literal cell-7 restoration and exposes the first
rolling-hole read partition: physical false produces a canonical
`qNextFalse` handoff. Physical true and the first virtual blank now have exact
actual-run cleanup theorems at clock `3 * zeros + 6`; they finish at head 6 in
`qOne` and `qVirtual`, respectively, with literal `contentTape` restored.
`qOne` and `qVirtual` are absorbing internal outcome
tags; `machine.accept = qOne` is only this tracer's ABI choice, and `qVirtual`
is not a machine terminal. This slice does not prove arbitrary-round induction,
whole-payload traversal, `allZeroSlice?`
correctness, capped arithmetic, or semantic acceptance.

**Part A G2c fixed gamma-payload round step (infrastructure only).**
`FixedGammaPayloadRoundStep` is a new 11-state, 33-entry successor; it does not
change the core's published absorbing `qNextFalse` row.  Its machine-neutral
`roundTape` and machine-specific `RoundInvariant` describe every boundary
`1 ≤ k ≤ zeros`.  From a
reachable boundary with `k < zeros`, one physical-false round runs in exactly
`2 * zeros + 4` steps, restores the old payload hole, spends counter cell
`8 + k`, opens the next payload hole, and re-enters its own `qStart`.  A real
`k = 1 → 2` corollary starts from the core's `first_physical_false_exact`.
True, virtual, and exhausted branches are only explicit internal exit tags;
`machine.accept = qOnePending` is a local ABI choice, not a semantic-acceptance
claim.  No cleanup, whole-payload verdict, capped arithmetic, or semantic
claim is made. Boundary-only induction is provided by the G2d proof driver.

**Part A G2d fixed gamma-payload round driver (proof only; infrastructure only).**
`FixedGammaPayloadRoundDriver` proves that every boundary `1 ≤ k ≤ zeros`
is reachable when every absolute content cell
`9 + zeros ≤ j < 9 + zeros + k` is physically present and false. Its
transparent successor-local clock is `(k - 1) * (2 * zeros + 4)`: boundary one
is the real `startConfig` itself at local clock zero. This is not a
cross-machine total clock. The driver adds no exhausted, true, or virtual
outcome, no whole-payload verdict, and no semantic claim or bridge.

**Part A G2e fixed gamma-payload exhausted tail (proof only; infrastructure only).**
`FixedGammaPayloadExhausted` composes the last G2d boundary with the exact
successor-local tail `zeros + 3`, reaching the absorbing internal tag
`qExhausted` at head `8 + zeros` and leaving `roundTape` unchanged. Its clock
`boundaryClock zeros zeros + (zeros + 3)` is not a cross-machine total clock.
The proof uses `0 < zeros` and the full physically present false prefix,
establishes strict first arrival and no-clamp bounds, and performs no tape
restoration or cleanup. The tag does not claim a semantic all-zero verdict,
acceptance, or a complexity bridge.

**Part A G2h fixed gamma-payload pending outcomes (proof only; infrastructure only).**
`FixedGammaPayloadPendingOutcomes` composes every reachable boundary
`1 ≤ k < zeros` with an exact local round of cost `2 * zeros + 4`.  A physical
true at cell `9 + zeros + k` reaches absorbing `qOnePending`, while equality of
that cell with `a + m` reaches absorbing `qVirtualPending`; both stop on the
read cell with the same `pendingTape`, and both are strict first pending
outcomes.  The clock is successor-local.  This slice excludes `k = 0`,
`k = zeros`, cleanup, a whole-payload or semantic verdict, and any
cross-machine clock or complexity bridge.

**Part A G2f fixed gamma-payload physical zero cleanup (infrastructure only).**
`FixedGammaPayloadZeroCleanup` is a new five-state successor that retags the
exact G2e `qExhausted` endpoint without changing that absorbing predecessor
row. It scans right across the complete physical-false payload, fills the
cursor with literal `false`, returns across the payload and terminator, fills
the contiguous counter/anchor holes through cell 7, and stops on fixed tag
cell 6 in absorbing internal `qDone`. Its exact successor-local clock is
`3 * zeros + 3` for `0 < zeros`, with strict first arrival, head 6, and literal
`contentTape` restoration. The table has 15 rows and is independent of tape
budget; the proof also exposes its initial footprint and the exact arithmetic
bounds used to type its phase configurations. No run-level no-clamp theorem is
claimed. This is not
a semantic all-zero or acceptance result, and its clock is not combined with
any predecessor-machine time.

**Part A G2i fixed gamma-payload pending cleanup (infrastructure only).**
`FixedGammaPayloadPendingCleanup` is an eight-state successor of both exact G2h
pending endpoints for `1 ≤ k < zeros`. One retagged `qStart` reads the pending
cell: physical true selects `qBackOne`, the virtual blank selects
`qBackVirtual`, and physical false rejects. Thus no proof becomes branch
advice. Each branch restores holes `8+k` through `7` with physical false and
stops at cell 6 in distinct absorbing `qOne` or `qVirtual`. The strict first
successor-local endpoint is `zeros + k + 4`, with literal `contentTape`; the
wrong tag is excluded throughout. All 24 rows/resources are pinned, no row
moves right, heads are nonincreasing, and cells above the initial head remain
fixed. This is structural infrastructure only: no semantic verdict,
dispatcher correctness, acceptance meaning, cross-machine clock, or
complexity bridge is claimed, and it is not P-vs-NP mainline work.

**Part A G2k fixed gamma-payload dispatcher (infrastructure only).**
`FixedGammaPayloadDispatcher` is a 28-state/84-row fixed routed block sum from
the actual G2a deadline endpoint. It preserves three absorbing outcomes:
`qAllZero`, distinct internal `qHasOne`, and shared malformed `qReject`; the
control/table contain no input, zero count, width, or proof data. This slice
activates exact executable malformed, zero-width, and `k=0` true/virtual paths,
including literal tape and case-specific head outcomes (7 for zero width, 6
after cleanup), endpoint absorption, and budget independence. Later round,
pending, and exhausted routes are table-wired but not covered by unified run
theorems, so this is not a whole-dispatcher semantic claim and not mainline.

**Part A G2g fixed gamma-payload zero semantic bridge (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadZeroSemanticBridge`
characterizes `VirtualZeroTailReader.allZeroSlice? = some true`, under exact
logical fit, by false blank-padded reads. With explicit physical and logical
fit it specializes this to the gamma payload window
`[9 + zeros, 9 + 2 * zeros)`, and combines the existing G2f endpoint with the
result at logical length `a + m`; the physical-false prefix itself proves that
fit. This is a one-way consequence of the existing `htag`/`hg`/`hzero`/full
physical-false hypotheses. It is not a `qDone` equivalence, semantic acceptance,
dispatcher correctness, complete parser correctness, or P-vs-NP mainline
progress.

**Part A G2j cleaned pending strict-reader semantics (infrastructure only).**
`ContentFixedGammaPayloadPendingSemanticBridge` freezes the strict-reader
boundary: for positive width, `allZeroSlice? = none` exactly when the logical
window does not fit, while under fit `some false` exactly means that some
`padRead` in the window is true.  It conjoins the G2i `qOne` and `qVirtual`
cleanup endpoints with their respective `some false` and `some true` scans for
arbitrary `T` satisfying `9 + 2 * zeros ≤ T`.  The virtual scan is exactly
`none` at physical `T = a + m`.  Both pending branches, and the small G2g zero
branch, also have corollaries at the shared frozen window `2 * (a + m) + 1`.
The payload remains exactly `[9 + zeros, 9 + 2 * zeros)`.  These are one-way
parallel consequences only, with no endpoint iff semantics, dispatch, parser,
decode, acceptance, cross-machine clock, or P-vs-NP mainline claim.

**P1b-0 fixed-width DAG-bundle composition (infrastructure only).**
`Complexity.DagBundleCompose` layers a fixed-output `DagBundle` over one shared
predecessor bundle with exact gate count `B.gates + S.gates`, and iteration from
the zero-gate identity has exact count `t * S.gates` and `Nat.iterate`
semantics.  `Complexity.DagGadgets` adds the small direct projection, constant,
NOT, AND, OR, and MUX surface.  See `pnp3/Docs/DagBundleCompose.md`.  This slice
does not provide a UniformTM configuration/step/run compiler, a polynomial-size
theorem, a `PpolyDAG` bridge, or a complexity-class rebind; it is not P-vs-NP
mainline progress.

**P1b-1 direct Uniform V1 configuration encoding (infrastructure only).**
`Complexity.Uniform.V1.CircuitEncoding` fixes the state/head/presence/value
layout with exhaustive block coverage, canonical three-symbol tape rails,
exact concrete encoding, and a two-shared-gate `initialBundle` with zero-gate
input projections.  Its length-one capstone separates a present false input
bit from blank padding.  The module reaches canonical `Complexity.Interfaces`
through the DAG gadgets; that interface transitively imports legacy
`PsubsetPpolyInternal.TuringEncoding`.  The P1b-1 construction and proofs use
neither that legacy TM nor its `runTime`, simulator/compiler, or frozen
`TMVerifier` semantics.  This slice provides no transition/step or run
compiler, polynomial-size simulation theorem, `UniformP`/`PpolyDAG` bridge,
canonical class rebind, or P-vs-NP mainline progress.

**P1b-2 encoded one-step semantic kernel (infrastructure only).**
`Complexity.Uniform.V1.StepKernel` defines a pure Boolean `encodedStep` that is
exact on canonical configuration encodings, including public-step terminal
semantics, old-head writes, and real clamped head movement.  Iteration agrees
with `UniformTM.run`.  A caller-supplied `StepSpec S` yields an exact
`runBundle` with `2 + t*S.gates` gates, but this slice constructs no concrete
step/action bundle or `StepSpec` witness.  `DagGadgets.bigOrCircuit` supplies a
linear direct false-seeded list disjunction with exact `List.any` semantics and
exact size `2 + sum C.size`, including size two for the empty list.  This slice
proves no polynomial simulation, `PpolyDAG` bridge or rebind, and is not
P-vs-NP mainline progress.

**P1b-3 direct shared step bundle (infrastructure only).**
`Complexity.Uniform.V1.StepBundle` materializes scan, exact three-symbol
classification, symbol-major transition rows, and filtered public-`M.step`
action rails in one shared predecessor graph. A `15*T` old-head update layer
is substituted once, yielding `stepBundle`, `StepSpec`, and the explicit bound
`19*T + 16*Q + 13`. This does not prove polynomial size for a run family,
`UniformP ⊆ PpolyDAG`, a canonical rebind, or P-vs-NP mainline progress.

**Final P1b versioned UniformP bridge (infrastructure only).**
`Complexity.Uniform.V1.PpolyDAG` builds the clocked run circuit solely from a
fixed `UniformTM`, clock exponent, and input length.  Its exact size is the
initial three units plus the clock times the direct step-bundle gate count, and
the all-input polynomial theorem uses the explicit exponent
`3 + (c+1)*(19*c + 16*M.stateCount + 70)`, with separate zero/one-length
proofs.  The completed endpoint is
`uniformP_subset_PpolyDAG : ∀ L, UniformP L → PpolyDAG L`, where `UniformP` is
only the versioned V1 class and `PpolyDAG` is the canonical DAG target.  P1c
separately proves countability and the length-only diagonal for that versioned
class. Neither slice rebinds or proves an equivalence for canonical `P`,
defines `UniformNP`, or proves a lower bound; neither is P-vs-NP mainline
progress.

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Simulation fine-grained boundary:
`pnp3/Docs/Simulation_FineGrained_Status.md`.
Research method boundary:
`pnp3/Docs/Research_Method_Boundary.md`.

## Verified State

- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes on the current tree (strict policy:
  no `sorry`/`admit` anywhere, no `sorryAx` in any term).
- Inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- That inclusion theorem is coarse polynomial-size DAG inclusion only; it is
  not a fine-grained Cook-Levin or hardness-magnification compiler adequacy
  theorem.
- The repository contains substantial DAG endpoint plumbing, including the
  fixed-slice DAG-to-formula bridge
  `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`.
- The former fixed-slice pnp3 AC0 endpoint is quarantined in
  `pnp3/LowerBounds/AC0_GapMCSP.lean`. Its standard-looking names are
  deprecated: `SmallAC0Solver_Partial` contains `params` and an enriched
  `easyData` payload that already imply `False` without solver correctness.
  The proved statement is only enriched-package inconsistency, not a standard
  AC0 lower bound and not P-vs-NP mainline progress.

## Current Audit Result

There is still **no unconditional in-repo theorem** `P != NP`, and the
current blockers are sharper than the old "remove residual payload" wording.

**Repository `P` runtime-advice caveat.**  The exact-step machine model described
under "Runtime model caveat on input (2)" below has a `P`-side consequence too:
since `runTime : Nat -> Nat` is unrestricted data, the `P` predicate bounds it
pointwise but never requires it to be computable or time constructible.
`lengthAdviceLanguage_in_repo_P`
(`pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean`) therefore proves
that every `A : Nat -> Bool`, with no computability hypothesis, yields a
length-only language in the current repository `P`, using a two-state machine
whose zero-or-one-step runtime stores `A n`.  The definition thus admits
arbitrary length languages, including languages obtained from noncomputable
sequences.  The theorem does not itself construct a noncomputable sequence or
formalize undecidability or a cardinality separation.

**Category: Infrastructure.** This is an interface audit, not a repair of the
model or P-vs-NP mainline progress.

The active public DAG endpoint is now the honest research-gap boundary:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

The legacy `hMS`/provider/support-bounds endpoints still compile, but they are
explicitly audit routes in `Magnification.FinalResultAuditRoutes`, not the
public closure boundary.  The falsifiability audit proves:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `MagnificationAssumptions -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`
- `MagnificationAssumptions_fromPipeline -> False`
- `FormulaCertificateProviderPartial -> False` (Probe 13, PR 13 audit)

So the legacy support-bounds, multi-switching, and certificate-provider
final routes are vacuous: they compile, but they route through inconsistent
assumptions.

**Note on PR #1366 canonical asymptotic infrastructure.**  PR #1366 landed
`canonicalAsymptoticHAsym` (unconditional fill of the
`AsymptoticFormulaTrackHypothesis` data structure) and a 7-session
TM-verifier construction plan for the canonical spec.  Probe 13 above shows
that the downstream wiring `i4_final_wiring_of_formulaCertificate` (the
consumer of a hypothetical `canonicalAsymptoticNPBridge_of_TM W`) is
ex-falso via `FormulaCertificateProviderPartial -> False`.  Therefore:

- The canonical infrastructure (slice-equality bridge, computable decider,
  TM-verifier scaffold) is sound Lean engineering and can be retargeted.
- The 7-session TM-verifier construction targeting `canonicalAsymptoticSpec`
  is **NOT** a path to unconditional `NP ⊄ P/poly` in the current
  formalization.  A future TM-witness consumer must route through a NEW
  provider that does not universally quantify over `PpolyFormula` (so it
  is not satisfied by truth-table hardwiring).

**Note on post-PR13 retarget chain (May 2026).**  The post-PR13 audit chain
landed three D0 / L0 deliverables under `seed_packs/`:

1. `seed_packs/post_pr13_provider_retarget_D0` (opus47):
   `RETARGET_EXISTING_ROUTE` — identified
   `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
   `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` as the
   two non-refuted DAG-side consumers of the canonical track.
2. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55, PR #1378):
   `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` — confirmed neither
   route imports `FormulaCertificateProviderPartial` or universally
   quantifies over `PpolyFormula`, and that NOGO-000004/6/8/9 do not
   transfer.
3. `seed_packs/hInDag_triviality_probe_D0` (gpt55, PR #1383):
   `YELLOW_INCONCLUSIVE` — no markdown-only argument settles the
   triviality question; blocking construction is either
   `canonicalAsymptotic_in_P` (multi-session TM-verifier plan) OR a
   direct DAG truth-table hardwiring at fixed slice.
4. `seed_packs/hInDag_triviality_probe_L0` (gpt55, PR #1388):
   `RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN` — the L0-A route closed.
   `pnp3/Tests/HInDagTrivialityProbe.lean` (121 LOC, kernel-checked,
   no `axiom`/`opaque`/`sorry`/`native_decide`, no refuted-predicate
   imports) defines:

   ```lean
   noncomputable def fixedSlice_gapPartialMCSP_in_PpolyDAG
       (p : GapPartialMCSPParams) : InPpolyDAG (gapPartialMCSP_Language p)

   noncomputable def hInDag_for_canonicalAsymptoticHAsym :
       ∀ n β, InPpolyDAG (gapPartialMCSP_Language
         ((eventualGapSliceFamily_of_asymptotic
             canonicalAsymptoticHAsym).paramsOf n β))
   ```

   via per-slice truth-table DAG hardwiring at the single encoded length
   `partialInputLen p` plus `constFalseDag` elsewhere.  The polynomial
   bound holds with a slice-dependent constant `K_p` because
   `InPpolyDAG.polyBound_poly` requires polynomiality in the input
   length `n`, and constant-in-`n` is polynomial.

**Structural consequence of the L0 landing.**  Both
`AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
`AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` have
the shape `∀ hInDag, <structural conclusion>`.  With
`hInDag_for_canonicalAsymptoticHAsym` now Lean-witnessed, the `∀`
collapses to instantiation at the hardwired witness.  But the derived
`ppolyDAGSizeBoundOnSlicesEventually F hInDag` under truth-table
`polyBound = K_p` is a per-slice constant of order `2^N` at canonical
input length `N = 2 · 2^m`, doubly-exponential in the slice index.
"Small DAG" under this bound admits essentially every DAG of size
`≤ 2^N`, so the iso-strong / promise-YES conclusions now ask for
YES-isolating combinatorial structure for **arbitrary-size DAGs**, not
just polynomial-size DAGs.

**Note on canonical asymptotic track conclusion-side refutation
(May 2026, completed).**  Following the L0 hInDag triviality
landing, the audit chain continued with three additional D0 and L0
deliverables that ultimately **refuted the canonical track at the
conclusion level**:

5. `seed_packs/global_hInDag_contract_repair_D0` (codex53, PR #1396):
   `REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS` — proposed
   `GlobalAsymptoticDAGWitness` structure with single shared
   `(coeff, exponent)` polynomial bound to structurally close the
   hardwiring loophole.
6. `seed_packs/global_hInDag_contract_L0` (gpt55, PR #1404):
   `RED_GLOBAL_CONTRACT_CORE_LANDED` — landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with
   `GlobalAsymptoticDAGWitness` + `globalPolyDAGSizeBound` +
   `AsymptoticPromiseYesWeakRouteEventually_global` +
   `globalWitness_to_hInDag` forward projection.  Hypothesis-side
   hardwiring loophole structurally closed.
7. `seed_packs/isoStrong_conclusion_audit_D0` (codex53, PR #1407):
   `INCONCLUSIVE_NEEDS_LEAN_PROBE` — 4/4 D0 workers identified the
   conclusion-side question needs Lean probe.
8. `seed_packs/isoStrong_conclusion_L0` (codex, PR #1413):
   `YELLOW_PARTIAL_LANDING` — landed
   `pnp3/Tests/IsoStrongConclusionProbe.lean` (80 LOC; now archived under
   `archive/pnp3/Tests/`, subsumed by stage 14) with `F_Mof =
   n+2` simp lemma + `canonical_isoStrong_implies_eventual_strict_slack`
   slack-inequality extraction.  Identified pigeonhole
   z-construction as L1 blocker.
9. `seed_packs/isoStrong_conclusion_L1` (4 codex sessions, PRs
   #1416, #1423, #1427, #1433):
   **`RED_CONCLUSION_REFUTED`** — the canonical iso-strong route is
   **formally inconsistent** at canonical `sYES=1, sNO=2`.  Total
   staging file size: 409 LOC, kernel-checked, no `axiom`/`opaque`/
   `sorry`/`admit`/`native_decide`, no refuted-predicate imports.

The L1 chain (4 sessions) proved the **fourth major refutation** in
the post-PR13 chain via a corrected pigeonhole argument over
size-1 candidate traces on truth-table rows:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

**Proof structure:**
1. Pigeonhole core (session 1): `Size1Candidate n` finite type with
   `Fintype.card = n + 2`; `exists_trace_not_size1_of_card_lt` shows
   that under slack `n + 2 < 2 ^ Fintype.card α`, there exists a
   Boolean labeling outside all size-1 traces.
2. Encoding bridge (session 2): `traceSize1CandidateOnRows` evaluates
   size-1 candidates on truth-table rows via `Nat.testBit`;
   `diagonalPartialTable` constructs the candidate counterexample
   `z := encodePartial (diagonalPartialTable p yYes D label)`;
   `diagonal_z_valid` (ValidEncoding) and `diagonal_z_agrees_on_D`
   (AgreeOnValues) verify two of the three required properties.
3. Not-YES bridge + composition (session 3):
   `is_consistent_diagonal_table_implies_label_trace` (size-1
   consistency → label equals trace);
   `diagonal_z_not_yes_of_label_not_trace` (contradiction with
   label-not-in-trace hypothesis);
   `exists_valid_agreeing_not_yes_under_slack` (full composition).
4. Main theorem assembly (session 4):
   `correctOnPromiseSlice_of_InPpolyDAG_family` (lift InPpolyDAG to
   CorrectOnPromiseSlice); `slack_for_D_of_isoStrong_slack` (convert
   iso-strong slack κ-form to D.card-form); compose with `hForce`
   and `exists_valid_agreeing_not_yes_under_slack` to derive
   contradiction.

**Consequence.** The canonical asymptotic track via
`canonicalAsymptoticHAsym` is closed at conclusion level in the
following precise sense:

- The iso-strong route is formally refuted.  The in-build kernel-checked
  witness is the general theorem `isoStrong_conclusion_negative_general`
  (`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, stage 14 below), which
  subsumes the canonical instance `isoStrong_conclusion_negative_for_canonical`.
  The original canonical-specific staging probe
  (`IsoStrongConclusionProbe.lean`, stages 9–11) has been archived to
  `archive/pnp3/Tests/` now that the general theorem covers it.
- The promise-YES weak and promise-YES certificate routes are now also
  exposed as standalone Lean negation theorems in
  `pnp3/Tests/PromiseRouteConclusionProbe.lean`:
  - `promiseYesCertificate_conclusion_negative_for_canonical` and
  - `promiseYesWeak_conclusion_negative_for_canonical`,
  each with the same `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym, ¬ ...`
  shape as the iso-strong companion.  They are corollaries of the
  iso-strong negation composed with the pointwise versions of the
  existing route-level implications
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  (`pnp3/Magnification/FinalResultMainline.lean:348`) and
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
  (`pnp3/Magnification/FinalResultMainline.lean:400`).
- This makes the audit chain self-contained in Lean: instead of the
  closure of the certificate / weak routes living in the prose paragraph
  above, the closure is now three theorems with the same shape.
- Inhabitancy caveat: `GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`
  is referenced only as a universal hypothesis (`∀ W : ...`) in the
  inspected files; no explicit inhabitant is constructed in the current
  codebase.  This is recorded as context; the `∀ W, ¬P(W)` theorem is
  logically meaningful as-is.

This does **NOT** prove `P ≠ NP` or even `NP ⊄ P/poly`.  It rules
out the canonical asymptotic track at the canonical `sYES = 1,
sNO = 2` spec as a route to those endpoints.  Future P-vs-NP mainline
work must pivot to a different route family:

- pnp4 frontier `SearchMCSPWeakLowerBound` /
  `VerifiedNPDAGLowerBoundSource`;
- or genuinely new research-level mathematics proving
  `ResearchGapWitness` directly.

The deprecated
`pnp3/LowerBounds/AC0_GapMCSP.lean::gapPartialMCSP_not_in_AC0` name is
only a compatibility alias for enriched-package inconsistency. The canonical
certificate `false_of_smallAC0Params_and_easyFamilyData` uses the parameter
capacity bound, AC0 realizability of the packaged family, and its
all-functions-scale cardinality lower bound; it does not use solver
correctness. It is not a standard AC0 exclusion.

A new canonical spec with non-trivial `sYES/sNO`, where the pigeonhole
argument does not apply (i.e., `Mof` grows fast
enough relative to `tableLen` to invalidate the slack inequality
used in `slack_for_D_of_isoStrong_slack`) is also an internal
spec-engineering option, not a publishable route on its own.

**Audit chain summary (16 stages, all kernel-checked).**

| Stage | Verdict | Lean witness |
|---|---|---|
| 1. PR 13 / Probe 13 | `FormulaCertificateProviderPartial → False` | `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` |
| 2. post_pr13_provider_retarget_D0 (opus47) | RETARGET_EXISTING_ROUTE | markdown audit |
| 3. asymptotic_isostrong_route_audit_D0 (gpt55, #1378) | YELLOW | markdown audit |
| 4. hInDag_triviality_probe_D0 (gpt55, #1383) | YELLOW_INCONCLUSIVE | markdown audit |
| 5. hInDag_triviality_probe_L0 (gpt55, #1388) | RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN | `HInDagTrivialityProbe.lean` (121 LOC) |
| 6. global_hInDag_contract_repair_D0 (codex53, #1396) | REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS | markdown audit |
| 7. global_hInDag_contract_L0 (gpt55, #1404) | RED_GLOBAL_CONTRACT_CORE_LANDED | `GlobalHInDagContractProbe.lean` (116 LOC) |
| 8. isoStrong_conclusion_audit_D0 (codex53, #1407) | INCONCLUSIVE_NEEDS_LEAN_PROBE | markdown audit |
| 9. isoStrong_conclusion_L0 (codex, #1413) | YELLOW_PARTIAL_LANDING | `IsoStrongConclusionProbe.lean` (80 LOC; staging probe now archived under `archive/pnp3/Tests/`, subsumed by stage 14) |
| 10. isoStrong_conclusion_L1 sessions 1-3 (#1416, #1423, #1427) | YELLOW_PARTIAL chain | extends to 340 LOC |
| 11. isoStrong_conclusion_L1 session 4 (#1433) | **RED_CONCLUSION_REFUTED** | extends to 409 LOC; `isoStrong_conclusion_negative_for_canonical` formally proved (staging probe now archived; subsumed by stage 14's general theorem) |
| 12. general_isoStrong_no_go D0 (codex53, ffd47f6) | NEEDS_LEAN_PROBE | markdown audit |
| 13. circuit_count_trace_bound L0 (codex53, c436392) | GREEN_COUNTING_BRICKS_LANDED | `CircuitCountTraceBoundProbe.lean` (~120 LOC) |
| 14. general_isoStrong_no_go L1 sessions 1-4 (codex53+opus47, 75c5ae0 → 24d51510) | **RED_GENERAL_ISOSTRONG_REFUTED** | `GeneralIsoStrongNoGoProbe.lean` (~460 LOC); `isoStrong_conclusion_negative_general` formally proved over arbitrary `GapSliceFamilyEventually` |
| 15. general_isoStrong_route_closure (opus47) | **ROUTES_NAMED_AS_CLOSED** | `GeneralIsoStrongRouteClosure.lean` (~120 LOC); four named route-closure theorems |
| 16. promise_route_conclusion_companions | **CONCLUSION_COMPANIONS_NAMED** | `PromiseRouteConclusionProbe.lean`; `promiseYesCertificate_conclusion_negative_for_canonical` and `promiseYesWeak_conclusion_negative_for_canonical` standalone theorems with the same `∀ W, ¬ ...` shape as `isoStrong_conclusion_negative_for_canonical` |

The canonical asymptotic track is now closed at conclusion side via
standalone Lean theorems (iso-strong via the in-build general theorem
`isoStrong_conclusion_negative_general`, which subsumes the archived
canonical `isoStrong_conclusion_negative_for_canonical`; promise-YES
certificate and promise-YES weak via the two companions in
`PromiseRouteConclusionProbe.lean`).  The
four major refutations in the post-PR13 chain:

1. `FormulaCertificateProviderPartial → False` (PR 13, formula-side
   truth-table hardwiring).
2. `hInDag_for_canonicalAsymptoticHAsym` provable
   (L0 #1388, DAG-side per-slice truth-table hardwiring).
3. Global contract structurally closes hypothesis side
   (L0 #1404).
4. **`isoStrong_conclusion_negative_for_canonical` provable
   (L1 sessions 1-4, canonical track formally inconsistent at
   conclusion level).**

**Note on general iso-strong refutation and route-level closure
(May 2026, completed).**  Following the canonical L1 session 4
landing, the audit chain continued with a D0 audit, an L0 counting-
brick probe, and four L1 sessions that lifted the canonical
refutation to the general `GapSliceFamilyEventually` schema.  After
these steps the route-level refutation lives in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` as

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag
```

and the strategic consequence is packaged as four named theorems
in `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`:

- `not_AsymptoticIsoStrongRoute_of_hInDag`
  (parameter-agnostic helper);
- `not_AsymptoticIsoStrongRoute_canonical`
  (instantiated via `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`);
- `not_AsymptoticPromiseYesCertificateRoute_canonical`
  (via `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`);
- `not_AsymptoticPromiseYesWeakRouteEventually_canonical`
  (via `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`).

All four are kernel-checked with standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`).  They make the iso-strong /
promise-YES certificate / promise-YES weak route class **formally
retired** at the canonical asymptotic instantiation: each named
theorem refutes the corresponding route prop directly, so a future
reader scanning the route catalogue can identify these three routes
as closed without re-deriving the meta-argument.

This does **NOT** prove `P ≠ NP` or `NP ⊄ P/poly`.  It closes the
iso-strong route class as a path to those endpoints; future
P-vs-NP mainline work must pivot to a different route family —
either the pnp4 frontier (`SearchMCSPWeakLowerBound` /
`VerifiedNPDAGLowerBoundSource`) or genuinely new research-level
mathematics proving `ResearchGapWitness`. The deprecated
`gapPartialMCSP_not_in_AC0` compatibility theorem proves only that an
inconsistent enriched easy-family package cannot exist; it is neither an AC0
lower bound nor a closure route.

## Fixed-Params Status

Session 67 introduced the stronger contract
`FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb`.

Session 68 established the current honest boundary:

- the Probe 7 singleton-provider attack does not directly port to fixed
  external `ac0` parameters;
- `fixedParams ac0 sb` alone is not currently refuted in the project;
- `fixedParams ac0 sb` plus uniform provenance for every formula witness under
  the same `ac0` reconstructs the old false support-bounds predicate;
- therefore the pair `fixedParams + uniformProvenance` is formally
  inconsistent in the current formalization.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
is useful as a gap-exposing theorem, not as progress toward an unconditional
claim.  Its assumptions describe the research-level hole.

The single-file boundary for future closure is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  It contains
`ResearchGapWitness` and the compiled bridge
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`; a future
unconditional proof should be localized there by proving
`ComplexityInterfaces.NP_not_subset_PpolyDAG` without using the refuted
support-bounds surfaces.

`ResearchGapWitness` is method-agnostic.  AC0/locality/restriction/shrinkage
routes, including `AcceptedFamilyCertificateAt`, are optional sufficient
routes and compatibility surfaces, not the required format for a future
algebraic, spectral, finite-field, SOS, or other non-combinatorial proof.

## What Is Closed

### Canonical asymptotic track (May 2026)

The asymptotic anti-checker pair `(hAsym, hNPbridge)` is no longer a
hypothesis parameter throughout the magnification mainline.  See
`pnp3/Magnification/CanonicalAsymptoticTrackData.lean`:

- `canonicalAsymptoticSpec : GapPartialMCSPAsymptoticSpec` — minimal legal
  asymptotic spec (`sYES = 1, sNO = 2`); all four structure fields built.
- `canonicalAsymptoticParams n hn : GapPartialMCSPParams` — per-slice
  parameters at slice `n ≥ 8` with Shannon-counting `circuit_bound_ok`
  proved unconditionally via `canonicalShannonBound`.
- `canonicalSliceEq : ∀ n hn x, asymp(...) = perSlice(...)` — Lean
  technical bridge for the `Classical.choose` dependent cast.  Closed via
  an `Eq.rec` motive parameterised over the type-level witness proof; the
  base case reduces the cast through `Subsingleton.elim` on the `Eq`
  proof.  The supporting helper
  `Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen` is in
  `Model_PartialMCSP.lean`.
- `canonicalAsymptoticHAsym : AsymptoticFormulaTrackHypothesis` —
  **unconditional**.
- `canonicalAsymptoticNPBridge_of_TM W`, `canonicalAsymptoticData_of_TM W`,
  `canonicalAntiCheckerAssumptions_of_TM W` — produce the strict NP
  package from a single concrete TM-verifier witness
  `W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

`pnp3/Tests/CanonicalIntegrationTests.lean` validates end-to-end
integration wiring surfaces, including
`i4_final_wiring_of_formulaCertificate` and
`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`.
The canonical conclusion-side closure is witnessed in-build by the general
iso-strong theorem `isoStrong_conclusion_negative_general`
(`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`) together with the two canonical
promise companions `promiseYesCertificate_conclusion_negative_for_canonical` /
`promiseYesWeak_conclusion_negative_for_canonical`
(`pnp3/Tests/PromiseRouteConclusionProbe.lean`).  The canonical-specific
iso-strong staging probe (`isoStrong_conclusion_negative_for_canonical`,
`IsoStrongConclusionProbe.lean`) is archived under `archive/pnp3/Tests/` and is
subsumed by the general theorem.

The historical remaining typed deliverable for that independent infrastructure
milestone was the TM verifier. Its implementation plan is now frozen; the
retained details under "What Is Still Open" are an archival record, not the
active engineering queue.

### Inclusion side

- Default inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- Default final wrappers no longer need external inclusion-contract bundles.
- The simulation layer is closed only at the coarse `P_subset_PpolyDAG` level:
  its active size contract is existential polynomial (`n^k + k`), not a
  fine-grained overhead bound.  This is sufficient for
  `ResearchGapWitness -> P_ne_NP_final`, but not for any future route that
  depends on exact magnification slack.

### DAG plumbing

- The fixed-slice DAG-to-formula bridge exists.
- Route-B, source-closure, blocker, asymptotic, and `_TM` endpoint wrappers are
  implemented.
- This plumbing is useful for future magnification arguments.

### Fixed-slice no-go status

The historical fixed-slice support-half route is a closed no-go branch under
fixed-slice `PpolyDAG` membership:

- `no_fixedSlice_stableRestriction_of_inPpolyDAG`
- `no_fixedSlice_blocker_of_inPpolyDAG`
- `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG`

## What Is Still Open

### Canonical-track TM-verifier deliverable (frozen historical roadmap)

> **Freeze note (GN-E2-5c, 2026-10-01).** The broader roadmap remains paused.
> The current tree is `b2762b378800f81e6adaaa3ecbe6b277ddd59482`, from stage-(a) provenance
> `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8`, repinned by its direct stage-(b) child.
> This seventh migration since `42c59881` executes the authorized values-list
> induction and fixed tail after GN-E2-5b, on exact main base
> `b71eb6ca3ff4101d6d1596dfb4fc06ce63f845c7`. The nonempty first request is
> fully installed at `requestReady`; launch, delegation, returned-bit commit,
> looping, verdict, acceptance and new-clock/runtime adequacy remain open.
> The header and GN-E2-5c record state the targeted build and freeze evidence;
> no full gate or independent/remote review transfers from an older slice.
> N1/N3 remain assigned to Lane B. Active model-repair work otherwise uses the
> uniform complexity foundation outside TMVerifier.

> **Scope note.**  After the canonical iso-strong / promise-YES
> conclusion-side refutations recorded above, the canonical asymptotic
> track is **no longer a P-vs-NP closure route**.  The TM-verifier
> deliverable below is therefore an independent formalization /
> infrastructure milestone for the reusable NP-verifier and decider
> scaffolding.  Finishing it does not reduce the `ResearchGapWitness`
> gap by itself, and it must not be presented as P-vs-NP progress.

Considered as an isolated infrastructure target, the canonical
asymptotic infrastructure reduces to a single typed object:

```
W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec
```

i.e., a concrete polynomial-time TM that verifies
`gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec` against a
size-1 circuit certificate.  Mathematically this is the published
OPS19/CJW20 fact `GapMCSP ∈ NP` (one-half-page argument in textbooks).

**Decomposition (May 2026)**:
`pnp3/Magnification/CanonicalAsymptoticDecider.lean` reduces the
obligation to a single TM-engineering target.  It contains:

- `decideAsymptotic : (n : Nat) → Bitstring n → Bool` — a computable
  decider equal pointwise to `gapPartialMCSP_AsymptoticLanguage
  canonicalAsymptoticSpec` (proved as `decideAsymptotic_iff`).
- `findCanonicalSlice` — fully axiom-free `Option Nat` detector for
  canonical input lengths `Partial.inputLen m = 2 · 2^m`.
- `decideYesAt1` — enumerates the `m + 2` size-1 circuit candidates
  and checks consistency via the now-proved `is_consistent_iff_bool`.
- `CanonicalAsymptoticVerifierComponents` — the minimum-sufficient
  structure: a TM `M` plus the property `accepts (x ++ w) = decideAsymptotic n x`
  for every certificate `w`, plus the polynomial-runtime bound.
- `witnessOfComponents : Components → GapPartialMCSP_Asymptotic_TMWitness
  canonicalAsymptoticSpec` — closed bridge.

After this decomposition, the only remaining sub-obligation **for the
infrastructure milestone** is to construct a TM whose acceptance
behaviour matches the (now-defined) `decideAsymptotic` function, with
polynomial runtime.  All decidability and language correctness are
closed; the engineering reduces to "build a TM that ignores `w` and
computes a known Bool function on `x`".  Again, this is reusable
NP-verifier infrastructure, not a P-vs-NP closure step.

**Multi-session plan**: see `pnp3/Docs/TMVerifier_Session_Plan.md` for
the 7-session decomposition (Variant B NP-style architecture):

1. Session 1: `seqList_run_full` (generic CS-composition correctness)
2. Session 2: `writeVecOfNatProgram` + `_run_full`
3. Session 3: `mcspCheckAllRows_correct`
4. Session 4: Witness decoder (`decodeCandidateSpec` + `_writeToTape_run_full`)
5. Session 5: `canonicalLengthCheckProgram_run_full`
6. Session 6: Top-level composition `verifierProgram_accepts_iff`
7. Session 7: Runtime bound + final `canonicalAsymptoticVerifierComponents` term

Each session = ~350 LOC, closes one leaf theorem with 0 sorry / standard
classical axioms.  Total estimated work: ~2500 LOC over 7 sessions.

### Research-gap source theorem (longer-horizon)

The remaining blocker is not endpoint plumbing.  It is the missing
non-vacuous source theorem for `ResearchGapWitness`, equivalently
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

A real lower-level route may still come from support/locality mathematics, but
only if it produces DAG separation through a provenance gate that:

1. does not quantify over arbitrary `PpolyFormula` witnesses;
2. cannot be satisfied by truth-table hardwiring or singleton provenance;
3. uses fixed, externally meaningful AC0 parameters;
4. does not combine with an overbroad uniform-provenance assumption to imply
   the old false support-bounds predicate.

That missing theorem is the research-level mathematical gap.  It should be
treated as open, not as a Lean engineering task.

Green CI and a passing `./scripts/check.sh` are formal hygiene checks, not
mathematical progress toward `NP_not_subset_PpolyDAG` by themselves.  They
prevent stale or vacuous route claims from re-entering the tree; they do not
replace the missing lower-bound idea.

### pnp4 conditional decision→search extraction chain (June 2026)

`pnp4/Pnp4/Frontier/ContractExpansion/` now formalizes a verified **conditional**
chain that replaces the abstract
`SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource` jump with explicit,
machine-checked interfaces: from a `PpolyDAG` membership of the prefix-extension
language it extracts a bounded search solver, and contrapositively
`NoPolynomialBoundedSearchSolver + growth ⇒ ¬ PpolyDAG`; combined with an
NP-membership witness it assembles a `VerifiedNPDAGLowerBoundSource`.

This is **not** unconditional progress: it proves neither `P ≠ NP` nor
`NP_not_subset_PpolyDAG`.  The codec/growth machinery is now concrete: the **first
concrete `TreeCircuitWitnessCodec`** is constructed (`ConcreteTreeCodec.lean`), and
`PolyBoundedInTable` is proved for the canonical polynomial thresholds
(`ThresholdGrowth.lean`).  So at a concrete polynomial threshold the original
consolidated theorem (`ConsolidatedTreeSeparation.lean`, `verifiedSource_treePoly` /
`NP_not_subset_PpolyDAG_treePoly`) has **exactly two** explicit open inputs:

1. `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))` — a
   genuine `P/poly` circuit lower bound for the concrete tree-MCSP search problem
   (the same research-level lower-bound gap described above);
2. `PrefixExtensionNPWitness (…)` — a concrete NP verifier (TM + runtime + certificate
   correctness).

The preferred verifier target is now the content-truthful reroute in
`ContentConsolidatedSource.lean`. Its concrete capstone
`NP_not_subset_PpolyDAG_treePolyCT` likewise has exactly two explicit hypotheses: the same
`NoPolynomialBoundedSearchSolver` and
`ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))`.

The post-GATE/I1/D1b boundary is exact. The convention-length equality gate and gamma narrowing are
proved; `contentInput?` retains exactly three tag/index/padding read-value tests; and concrete
`ContentAccepts` non-vacuity is proved. D1b is complete as a **conditional repackaging** from a
supplied `ContentVerifierBridge` to the content NP-witness interface. Still open are wrapper-level
`L'` padding invariance, an actual concrete verifier bridge (machine, runtime proof, and exact-step
acceptance equation), formal runtime/advice enforcement, and the
`NoPolynomialBoundedSearchSolver` lower bound. None of the closed specification or packaging work
constructs a bridge instance or proves NP membership.

**Runtime model caveat on input (2).**  `NP` there is `NP_TM`
(`pnp3/Complexity/Interfaces.lean`) over `Pnp3.Internal.PsubsetPpoly.TM`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`): a deterministic
single-tape binary-alphabet machine with no separate read-only input tape and fixed tape
length `n + runTime n + 1` (`TM.tapeLength`), whose `runTime : ℕ → ℕ` is a **structure
field** rather than a derived step count, and whose `TM.accepts` is evaluated **at
exactly step `runTime n`** (`TM.run` iterates `stepConfig` exactly `M.runTime n` times,
then checks `state = M.accept`) with no halting predicate.  Because the declared budget
is also the evaluation point, the verifier interfaces' `runTime_poly` field is a genuine
restriction on the machine, not a self-certification.  That restriction is numeric
only — it bounds the size of `runTime` without constraining *which* function it is — and
the `P`-side consequence of that is the runtime-advice caveat recorded above.  No
cross-model runtime-robustness theorem is formalized, so input (2) is an obligation
*in this model*.
This is the NP-side analogue of the coarse-inclusion caveat recorded above for
`proved_P_subset_PpolyDAG_internal`.

**Honest caveat — one-way extraction, not an equivalence.**  The decision→search
extraction is formalized in **one direction only**:

```text
PpolyDAG (prefix-extension language) → polynomial-size bounded search solver
```

that is `boundedSearchSolver_of_PpolyDAG_prefixExtension`
(`pnp4/Pnp4/Frontier/ContractExpansion/BoundedSolverFromPpoly.lean`), together with its
contrapositive in two forms: the exact-schedule
`not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver`
(`ContractExpansion/NoSolverContrapositive.lean`, no growth premise) and the
polynomial-target `not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`
(`ContractExpansion/ExtractedScheduleGrowth.lean`, which adds
`TreeMCSPExtractionGrowthAssumptions` and is derived from the exact-schedule form).
Both restate the same single direction.  The converse
(solver ⇒ `PpolyDAG`) is **not** formalized: `ContractExpansion/` contains no `Iff`
between `PpolyDAG` and a solver and no `PpolyDAG_of_boundedSearchSolver` declaration.

Since the instance length is `tableLen n = 2^n`, input (1) is therefore **at least as
strong as** the full `P/poly` lower bound "this concrete NP language is not in
`P/poly`" — and, absent the converse, possibly strictly stronger.  It is **not** a
weak/local bound amplified by hardness magnification, and no magnification theorem is
formalized: the chain makes the target precise and verified-conditional, not easier.
See `pnp4/Pnp4/Frontier/ContractExpansion/README.md` for the full module map and
proved-vs-open breakdown.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P != NP` is inaccurate until the
project has either a non-vacuous replacement for the refuted
support-bounds / multi-switching source, or a direct method-agnostic
proof of `ResearchGapWitness` / `ComplexityInterfaces.NP_not_subset_PpolyDAG`
(algebraic, spectral, finite-field, SOS, Fourier-analytic, or other),
together with a zero-argument final theorem that does not depend on
external provider payload.
