# TODO / Roadmap (current)

**GN-E2-5e (2026-10-02, Infrastructure only): canonical first-return commit is closed.**
`gnCS_firstReturned_commit_exact` has implicit parameters
`{r : GNProgram} {g : SLGate r.inputs.length}` and explicit parameters
`(hg : r.program.gates[0]? = some g) (res : Bool)`. It proves
`TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
  (gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res`.
`gnCS_encodeGN_firstCommit_exact` additionally assumes
`(hs : (gnFirstRequest r g).spec = some res)` and proves the same endpoint
from `GNM.initialConfig (gnPoint (encodeGN r))` after
`gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g)+1) +
  gnFirstCommitSteps r g`. Neither execution theorem assumes room, global
well-formedness, an execution contract, or second-gate success.
The separate `gnFirstReturnedConfig_eq_physical` lemma explicitly takes a
head-bound premise `hr`; its exact signature and all five public endpoint
signatures are in the [GN-E2-5e record](pnp3/Docs/GN_E2_5E_FIRST_RETURN_COMMIT.md).

The executed first slot write, first-record spent mark and next-cursor advance
(or single-gate final-output write) are closed. With `N = (encodeGN r).length`,
`n = r.inputs.length`, `m = r.program.gates.length`,
`L = gnRecordSize (gnGateFields g)` and `B = 4*(gnRecordsStart r + L)`,
the local clock is `N + 8*(L+n) + 4*m + 39`; the endpoint is
`firstCommitTerminal` at `B+8` if `m=1`, otherwise `firstCommitNext` at `B`.
The full tape is the bits of `encodeGNAtFrames r [res] ++
  g1OutputFrames (gnFirstRequest r g) res`, with false padding.
`gnFirstCommit_structure` links this run to `gnCommit? r [] res`;
`gnFirstCommit_scratch_preserved` preserves every cell at or above `N`.

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

Release candidate `95ba057c77f3cb60933c32b63bb4aec471d19239` passed the
17-step full gate and exact-head Codex/Opus reviews. The canonical evidence and
latest-head merge requirements are in the [GN-E2-5e record](pnp3/Docs/GN_E2_5E_FIRST_RETURN_COMMIT.md#ordered-content-addressed-migration)
and PR #1815.

**Current open obligations:** arbitrary-stage gate advance/loop, scratch
reset/reuse, program verdict, GN acceptance, first-arrival minimality, composed
clock/runtime adequacy, `ContentVerifierBridge`, advice freedom, and Lane B
N1/N3. The first-return endpoint does not establish readiness for round two.
No pnp4 bridge, `SearchMCSPWeakLowerBound`, `VerifiedNPDAGLowerBoundSource`,
or P-vs-NP mainline progress is supplied. Earlier dated snapshots below retain
their historical scope; their validation does not certify this head.

Updated: 2026-10-02

Canonical checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Simulation fine-grained boundary:
`pnp3/Docs/Simulation_FineGrained_Status.md`.
Research method boundary:
`pnp3/Docs/Research_Method_Boundary.md`.

## Snapshot

- Active `axiom` in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- GN-E2-5e: first-return commit closed; release candidate `95ba057c` passed the
  17-step full gate and exact-head reviews. PR #1815 remains authoritative for
  latest-head CI and review coverage.
- Inclusion is internalized as coarse `P_subset_PpolyDAG`.
- The simulation layer is not a fine-grained Cook-Levin or
  hardness-magnification compiler adequacy theorem.
- The final `ResearchGapWitness` port is method-agnostic; AC0/locality and
  `AcceptedFamilyCertificateAt` routes are optional sufficient routes, not a
  mandatory interface for every future proof.
- DAG endpoint plumbing is substantial.  The legacy formula-side
  support-bounds / multi-switching separation route is formally
  refuted; the current public closure boundary is `ResearchGapWitness`,
  whose `dagSeparation` field (= `NP_not_subset_PpolyDAG`) is the only
  remaining mathematical input.
- The former pnp3 fixed-slice AC0 surface is now an audit quarantine.
  Its enriched `SmallAC0Solver_Partial` package is inconsistent before solver
  correctness is used, so it is not an AC0 lower bound or P-vs-NP progress.
- Mainline scope: per `AGENTS.md`, P-vs-NP mainline progress means reducing
  `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` in `pnp4/`.  The
  pnp3 targets below are honest infrastructure and no-go hardening for the
  magnification route; they are not the mainline.  See Target 4.

## Hard Policy Update

The project must not treat the legacy support-bounds route as an unfinished
technical lemma.

The following assumptions are formally ex-falso in the current tree:

- `FormulaSupportRestrictionBoundsPartial`
- `FormulaSupportBoundsFromMultiSwitchingContract`
- `MagnificationAssumptions`
- `FormulaSupportBoundsPartial_fromPipeline`
- `MagnificationAssumptions_fromPipeline`

The fixed-slice support-half blocker branch is also a closed historical no-go
route, as recorded by:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

## Remaining Closure Targets

### Target 1. Preserve honest endpoint infrastructure

Status: keep green.

The DAG side has useful plumbing:

1. fixed-slice `PpolyDAG -> PpolyFormula` conversion,
2. asymptotic and `_TM` wrappers,
3. Route-B/source-closure/blocker surfaces,
4. final wrappers exposing the exact assumptions consumed.

This infrastructure is valuable when paired with either a non-vacuous
formula / locality source theorem, or a direct method-agnostic source
theorem that proves `ResearchGapWitness` /
`NP_not_subset_PpolyDAG`.

### Target 2. Replace the false support-bounds source

Status: open pnp3 research question.  This is **not** the P-vs-NP mainline — see the
Snapshot above and Target 4.

Do not try to "finish" the old `hMS` route.  It is inconsistent.

The current candidate shape is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

This fixed-params predicate blocks the known singleton-provider attack, but it
is not yet a proved source theorem.  Also, when paired with overbroad uniform
provenance for every formula witness under the same `ac0`, it reconstructs the
old false predicate and gives `False`.

Acceptance condition for real progress:

1. formulate a provenance-restricted support/locality theorem that cannot be
   instantiated by truth-table hardwiring;
2. prove it or clearly mark it as an external research assumption;
3. add falsifiability probes showing it does not imply the old false
   `FormulaSupportRestrictionBoundsPartial`.

### Target 3. Keep status docs honest

Status: active discipline.

Canonical docs must say:

1. no unconditional `P != NP` theorem exists in the repo;
2. the old support-bounds route is vacuous;
3. fixedParams is only a candidate contract shape;
4. `fixedParams + uniformProvenance` is itself inconsistent as currently
   stated;
5. the simulation route is coarse polynomial inclusion only, not a
   fine-grained compiler for slack-sensitive magnification;
6. green CI/check scripts are proof hygiene, not mathematical progress by
   themselves;
7. the remaining gap is mathematical, not just endpoint wiring;
8. the pnp4 decision→search extraction is formalized in one direction only
   (`PpolyDAG → solver` plus its contrapositive), never as an equivalence, and its
   no-solver input is not a weak bound amplified by magnification;
9. the preferred pnp4 `ContentPrefixExtensionNPWitness` obligation (and the retained
   `PrefixExtensionNPWitness` compatibility target) is stated in the repository's single-tape,
   exact-step `TM` model, with no cross-model runtime-robustness theorem and no formal prevention of
   input-length advice. P1c now proves countability and a direct no-length-advice diagonal for the
   separate versioned `Pnp3.Complexity.Uniform.V1.UniformP`; canonical `P` remains legacy and
   unchanged, with no rebind or equivalence inferred.

### Target 4. pnp4 mainline: the two consolidated source obligations

Status: the P-vs-NP mainline (per `AGENTS.md`).

The preferred content-truthful capstone in
`pnp4/Pnp4/Frontier/ContractExpansion/ContentConsolidatedSource.lean` reduces the verified-source
chain, at a concrete polynomial threshold, to exactly two explicit hypotheses:

```text
NP_not_subset_PpolyDAG_treePolyCT
  (k : Nat)
  (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
  (hNPWit  : ContentPrefixExtensionNPWitness
               (treeCircuitWitnessCodec (thresholdPoly k)))
  : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

1. `hNoPoly` is a genuine `P/poly` circuit lower bound for the concrete tree-MCSP search
   problem.  Research-level mathematics, not a Lean engineering task.  Because the
   extraction is one-way and the instance length is `tableLen n = 2^n`, it is at least as
   strong as "this concrete NP language is not in `P/poly`".
2. `hNPWit` is a concrete verifier TM plus polynomial runtime bound plus certificate correctness,
   in the model described in Target 3 item 9. D1b proves that a supplied
   `ContentVerifierBridge` repackages into this witness, but no bridge instance is constructed.
3. `PolyBoundedInTable threshold` is proved for the canonical polynomial thresholds
   (`ThresholdGrowth.lean`), so it is not an open input at `thresholdPoly k`.

Neither of the two open hypotheses is proved, so the endpoint stays strictly
conditional.  What *is* proved: the one-way decision→search extraction and its
contrapositive, the growth reduction, the concrete `treeCircuitWitnessCodec`
(`ConcreteTreeCodec.lean`), the threshold-growth discharge
(`polyBoundedInTable_thresholdPoly`), concrete `ContentAccepts` non-vacuity, gamma narrowing, and
vacuity of the convention-length equality gate. Exactly three tag/index/padding read-value tests
remain in the parser characterization.

For input (2), the remaining work is an actual concrete verifier bridge: machine construction,
runtime proof, and exact-step acceptance correctness. Part A G2w-b picks a concrete budget
`polyClock 3 (pairLength a m)` for the *gamma-target countdown phase* and runs that phase to exactly
that many steps, but this is **not** progress on the runtime proof: it is one phase's step count out
of a retagged phase-local `startConfig`, it composes no pipeline clock, it states no `DecidesWithin`,
`UniformP`, `accepts` or `AcceptsAt`, and the machine is still unfenced — a target too large for the
budget times out rather than rejecting. Part A G2x then executes **one** of the seventeen phase
handoffs — G2q's decrement into G2s-a's countdown — inside a single composed 18-state machine at
that same budget, switching at G2q's first arrival, Part A G2y executes the one before it — the
gamma payload loop into that composite — inside a single composed 40-state machine at the same
budget, switching at the loop's first arrival, Part A G2z executes the one before *that* —
G2p-d's marker preamble into the G2y composite — inside a single composed 54-state machine at the
same budget, switching at the preamble's first arrival `exactClock zeros = zeros + 7`, and Part A
G3a executes the one before *that* — G2p-c's second payload digit into the G2z composite — inside
a single composed 68-state machine at the same budget, switching at G2p-c's first arrival, which on
the only width an accepted parsed target reaches is the length-dependent `2N - 7`. Part A G3b then
supplied the prerequisite the next handoff down — G2p-b's first payload into G2p-c — was blocked on:
G2p-b now exports its exact first arrival (`exactClock N zeros`, `6` at width zero and
`2N + zeros - 6` at a positive width), strictness before it at every decoded width, and the deadline
identification a composition needs; G3b itself builds **no** composition. Part A G3c then executes
that handoff, **H13** — G2p-b's first payload digit into the G3a composite — inside a single
composed 86-state machine at the same budget, switching at G2p-b's first arrival `2N + zeros - 6`
on every positive width, the only kind an accepted parsed target reaches. Part A G3e then executes
the one before *that*, **H12** — G2p-a's scratch bootstrap into the G3c composite — inside a single
composed 95-state machine at the same budget, switching at G2p-a's first arrival
`2N - 11 - zeros`, which needs no width case and no room premise, so width zero enters through the
same statement. **Six** of the seventeen handoffs were then
performed by a finite table, the composed accept is still the countdown's phase-local `qDone`, and
no witness-check phase exists, so this is not the runtime proof either. The next handoff down,
**H11** — G2m's payload dispatcher into G2p-a — had two blockers. Part A G3f's
`FixedGammaPayloadDispatcherFirstArrival` closed the first: strict first arrival at any of the
dispatcher's three terminals, with equality to the deadline configuration. Part A G3g closes the
second — the dispatcher's *two non-reject* absorbing outcomes, `qAllZero` (its `machine.accept`)
and `qHasOne`, of which `UniformTM.seq` routes only the first — by the generic table transformation
`UniformTM.mergeAccept`, which retargets the two working-state rows into `qHasOne` at `qAllZero`
and leaves
`qHasOne` dead, and then executes H11 inside a single composed 123-state machine,
`(dispatcher.mergeAccept qHasOne).seq` the G3e composite, switching at the dispatcher's strict first
terminal time, which is input-dependent and has no length-only form. The two successful verdicts
are merged at the switch, exactly where G2p-a's landed retag already discards them. **Seven** of
the seventeen handoffs were therefore then performed by a finite table, and G3g builds no pnp4
bridge, no fence and no raw-input execution. Part A G3h then executes the one before *that*,
**H10** — G2a's gamma anchor into G2k's payload dispatcher — inside a single composed 129-state,
387-row machine, `FixedContentGammaAnchor.machine.seq` the G3g composite, with **no new table row**
and no new combinator: the anchor has exactly two absorbing states, so the landed `UniformTM.seq`
routes both and no `mergeAccept` is needed. H10's one live row — `qReturn` on `some true`, proved
the anchor's only row targeting its accept — fires at the anchor's width-only strict first arrival
`2*zeros + 5`, which carries no room premise and is bounded by the length-only deadline `2N`.
**Eight** of the seventeen handoffs were therefore then performed by a finite table, and G3h
constructs no `ContentVerifierBridge` or other pnp4 bridge, no fence, no raw-input acceptance and no
advice-freedom claim, so it is no P-vs-NP mainline progress. Part A G3i then executes the one before
*that*, **H9** — G2's gamma terminator into G2a's gamma anchor — inside a single composed 132-state,
396-row machine, `FixedContentGammaTerminator.machine.seq` the G3h composite, again with **no new
table row** and no new combinator: the terminator also has exactly two absorbing states, so the
landed `UniformTM.seq` routes both. H9's one live row — `qScan` on `some true`, the terminator's only
row targeting its accept once the accept's own absorbing three are excluded — fires at the
terminator's width-only strict first arrival `zeros + 1`, which carries no room premise and is
bounded by the length-only deadline `N - 7`; unlike G3h's, the newly routed reject row carries the
tag premise and is forward-direction only. **Nine** of the seventeen handoffs were therefore then
performed by a finite table, and G3i likewise constructs no `ContentVerifierBridge` or other pnp4
bridge, no fence, no raw-input acceptance and no advice-freedom claim, so it too is no P-vs-NP
mainline progress. Part A G3j then executes the one before *that*, **H8** — G1's content tag gate
into G2's gamma terminator — inside a single composed 147-state, 441-row machine,
`FixedContentTagGate.machine.seq` the G3i composite, once again with **no new table row** and no new
combinator: the gate too has exactly two absorbing states, so the landed `UniformTM.seq` routes
both. H8's one live row — the last tag state `12` on `some false`, the gate's only row targeting its
accept once the accept's own absorbing three are excluded — fires at the gate's **length-only**
strict first arrival `3N + 7`, which is also the gate's own deadline and carries no room premise;
the arrival itself was not exported in the shape `seq` consumes and is assembled here from the
gate's landed `exact_terminal_contract` and `run_deadline`. The terminator's reject took **one** live
row, proved unique; the anchor's took **six**, each pinned individually; the gate's is the target of
*many* live rows — the mismatch exits of the eight tag positions and the rewind's defensive rows — so
neither uniqueness nor a count is claimed for it, and rather than enumerate those rows one quantified
theorem routes every one of them to the composed reject. **Ten** of the seventeen handoffs were
therefore then performed by a finite table, and G3j likewise constructs no `ContentVerifierBridge` or
other pnp4 bridge, no fence, no raw-input acceptance and no advice-freedom claim, so it too is no
P-vs-NP mainline progress. Part A G3k then executes the one before *that*, **H7** — the trailing
content-marker erasure into G1's content tag gate — inside a single composed 151-state, 453-row
machine, `FixedPairContentMarkerErase.machine.seq` the G3j composite, once again with **no new table
row** and no new combinator: the marker-erase phase too has exactly two absorbing states, so the
landed `UniformTM.seq` routes both. H7's one live row — `qErase` on `some true`, the phase's only row
targeting its accept once the accept's own absorbing three are excluded — fires at the phase's
**length-only** strict first arrival `N + 3`, which is also the phase's own clock and carries no room
premise, and it is the first such row in forward execution order that *mutates* the cell it hands over: it writes
`none`, so the composed table performs the marker erasure itself. Because that arrival was already
landed in the shape `seq` consumes and is hypothesis-free, `handoff_exact` here takes **no hypothesis
at all** — the first executed handoff of the chain that takes none. Its reject side is the first that
is both complete and plural: exactly **two** live rows (`qErase` on `some false` and on `none`),
proved the only ones once both verdicts' own absorbing rows are excluded and each routed to the
composed reject, and neither ever taken out of this slice's start. **Eleven** of the seventeen
handoffs were therefore then performed by a finite table; the **six** earlier ones remained
proof-level identifications, the composed accept is still the countdown's phase-local `qDone`, G3k's
two inherited rejecting branches (malformed suffix, mismatched tag) are forward-direction only and
the mismatched one is timed only at the gate's length-only deadline, and G3k likewise constructs no
`ContentVerifierBridge` or other pnp4 bridge, no fence, no raw-input acceptance and no
advice-freedom claim, so it too is no P-vs-NP mainline progress. Part A G3l then executes the one
before *that*, **H6** — the pair origin alignment into the trailing content-marker erasure — inside a
single composed 177-state, 531-row machine, `FixedPairOriginAlignment.machine.seq` the G3k composite,
once again with **no new table row** and no new combinator: the alignment phase too has exactly two
absorbing states, so the landed `UniformTM.seq` routes both. In **forward execution order** H6 is the
first handoff of the chain whose live accept list is **plural** — the already-executed H11, further
right, routes six: **three** rows, the classification states `10`, `11` and `12` on `none`, proved by
`accept_rows_unique` the only ones targeting the phase's accept once the accept's own absorbing three
are excluded, each routed to index `26` keeping its own restoration write (`none`, `some false`,
`some true`) and its **left** move, a genuine step onto the origin and **not** a clamp: the landed
`boundary_clamps` puts the phase's sole left clamp two steps earlier, at source time `clock - 3`.
Which of the three fires on a given input is **not** claimed — those states are `private` in the
landed phase — and the surface test exhibits each of them by kernel reduction at a tiny fixture. Its
reject side is the longest such list so far: every row targeting it is one of **21**, five `none` and
sixteen Boolean, proved exhaustive in that one direction once both verdicts' own absorbing rows are
excluded and each routed to the composed reject, none ever taken out of this slice's start. Because
the phase's strict first arrival was already landed in the shape `seq` consumes and is
hypothesis-free, `handoff_exact` here takes **no hypothesis at all** and additionally pins strict
left-block confinement before the switch. This switch time, `(10 * a + 7) * (a + m + 1) + 3 * a`, is
the **first in the chain to depend on the split lengths `a` and `m` separately** — the landed ones
are length-only in `N = a + m`, width-only in the decoded `zeros`, or input-dependent — and
`clock_pins` exhibits `21`, `54` and `87` at `N = 2`, so `switchTime` and the chain clock take two
length arguments, the composed clock is quadratic in `a`, and it is **not** proved that
the cubic budget still dominates it. **Twelve** of the seventeen handoffs were therefore then performed
by a finite table; the **five** earlier ones remained proof-level identifications, the composed accept
is still the countdown's phase-local `qDone`, G3l's two inherited rejecting branches are
forward-direction only with the mismatched one timed only at the gate's length-only deadline, and G3l
likewise constructs no `ContentVerifierBridge` or other pnp4 bridge, no fence, no raw-input acceptance
and no advice-freedom claim, so it too is no P-vs-NP mainline progress. Part A G3m then executes the one
before *that*, **H5** — the structural one-cell origin shift into the pair origin alignment — inside a
single composed 184-state, 552-row machine, `FixedPairOriginShiftBootstrap.machine.seq` the G3l
composite, once again with **no new table row** and no new combinator: the bootstrap phase too has
exactly two absorbing states, so the landed `UniformTM.seq` routes both. Its live accept list is as
narrow as one can be — **one** row, the fetch state `4` on `none`, the probe that finds the block
exhausted, proved by `accept_rows_unique` the only row targeting the phase's accept once the accept's
own absorbing three are excluded, routed to index `7` keeping its written `none` and its `.stay`, so
H5 clamps on neither budget, while the phase's own last right move, at source time `clock - 2`, clamps
exactly when `B = 0`, an equivalence the landed `clamps` proves. Its reject side is proved an
**equivalence**, not just exhaustive: over all seven states and all three symbols, once **both**
verdicts' own absorbing rows are excluded, a row of the table targets its reject **iff** the symbol is
a Boolean and the state is one of `1`, `2`, `3`, six rows in all, each routed to the composed reject,
and none is ever taken out of this slice's start. Because the phase's strict first arrival was already
landed hypothesis-free in the shape `seq` consumes, `handoff_exact` here again takes **no hypothesis at
all** and additionally pins strict left-block confinement. This switch time, `4 * a + 3 * m + 5`, is
linear and far below G3l's quadratic one, but it still reads the two split lengths apart — `clock_pins`
exhibits `11`, `12` and `13` at `N = 2` — and it is **not** the smallest in the chain, the length-only
`N + 3` and `3 * N + 7` being smaller at the tagged fixture, so the composed clock stays quadratic in
`a` and budget domination is still **not** proved. **Thirteen** of the seventeen handoffs were therefore
then performed by a finite table; the **four** earlier ones remained proof-level identifications, the
composed accept is still the countdown's phase-local `qDone`, G3m's two inherited rejecting branches are
forward-direction only with the mismatched one timed only at the gate's length-only deadline, and G3m
likewise constructs no `ContentVerifierBridge` or other pnp4 bridge, no fence, no raw-input acceptance
and no advice-freedom claim, so it too is no P-vs-NP mainline progress.

**Part A G3t — Infrastructure: generic fenced raw execution through H17.**
`FixedGammaSuffixFootprint` and `FixedRawLengthFenceSuffix` extend the actual raw
execution of the unchanged 256-state `FixedRawLengthFence.prefixed` through
countdown entry, global state **245**, for arbitrary dependent words `x/w`, every
`B ≥ 2*R+2`, matching tag, decoded gamma width `zeros ≥ 2`, and the actual strict
dispatcher arrival `C/q`. Here `R=2*a+1+m` and `L=a+m`; the physical tape domain
remains `Fin (R+B+1)` throughout. The whole endpoint is
`fencedDecrementConfig`: head `L+1+zeros-borrow x w zeros`, complete `decTape`,
and the existing false fence at `P=3*R+2`. No transition, initializer, encoding,
allocation, or interpreter changes.

The trace proves `head ≤ 3*L < P` after installation through H17, preservation
of the literal false fence, and exclusion of both verdicts at every such time.
The cell theorem exposes every register digit, both adjacent blanks, and the
blank lane up to the fence. The exact clock is installation plus G3s's
`contentClock` plus `h17SuffixClock`; `h17_clock_bound` bounds it by
`h17Deadline R = 32*(R+1)^2`. `raw_fenced_h17_allocated` existentially produces
the actual dispatcher `C/q` at the unchanged `B=16*(R+1)^2`. This is a polynomial
prefix bound on the stated valid branch, not a whole-machine halting bound.

`ContentRawFencedDecrementBridge.raw_fenced_h17_parsed_target` fixes
`treeCircuitWitnessCodec (thresholdPoly k)` and the **same dependent `pr`** from
`contentInput?`. For `3 ≤ pr.2.n` and the explicit matching tag, it identifies
actual raw endpoint digits with `pr.2.n.testBit (zeros-j)`, including zero high
bits. It neither executes the parser nor supplies a different parsed witness.
Named full-proposition surfaces and direct axiom roots cover all public results.
The raw regressions derive the existing 2335-step overflow H17 endpoint via the
new generic theorem and cover width-two physical-zero, virtual, and positive
pending paths, including a strictly larger allocation.

**Part A G3v — Infrastructure: raw execution of the first truth-table bit.**

`FixedRawFencedTableFirstBit.machine` is exactly G3u's 256-state
`FixedRawLengthFence.prefixed.seq` the new fixed 11-state suffix: 267 states,
accept 265, reject 266. The suffix has 33 symbol-driven rows. Its control reads
no input function, address, width, target, parse, clock, dispatcher witness or
advice. The old tables, raw encoding, initializer, allocation and interpreter
are unchanged.

Here `machine.accept` (state 265) is the first-bit suffix's `qDone` embedded
in the composed machine. Under the stated hypotheses, the raw run reaches
this absorbing state with the specified full tape. This certifies completion
of the first-bit operation; it does not establish content-verifier correctness
or characterize acceptance of the intended language.

Write `L=a+m`, `R=2*a+1+m`, `P=3*R+2`, `F=P-(L+3+z)`, `E=9+2*z`, and
`H=min L E`. The raw success theorem assumes the matching tag, decoded gamma
width `z>=2`, `B>=2*R+2`, the actual strict dispatcher witness, low and high
register-bit identification with `v`, `v<=F`, and **`9+z<L`**. It executes from
`initialConfig` through the actual fenced countdown, then copies exactly the
first table bit to `L+1`. The complete result is the countdown success tape
with only that cell replaced by `some (padRead content E)`; the head is `L+1`.
The low `finishTape`, separator, exact `v` tally and false fence are preserved.
The register is no longer entirely zero when the copied bit is true.

The handoff is justified by strict first arrival, proved from the actual
fenced raw predecessor: state 253 at `T0-1`, separator head, restored tape.
Absorption excludes both earlier verdicts. The suffix reaches `qRead` at
`z+6+(L-H)` and finishes at `z+8+2*(L-H)`. These steps add to G3u's exact
success clock. With the bounded dispatcher, the raw clock is at most
`144*(R+1)^2`; allocation stays `16*(R+1)^2`. Strict overflow routes directly
to composed reject 266 with G3u's full rejecting tape/head and clock; it
requires no positive-payload premise. Equality with capacity is success.

`ContentRawFencedTableFirstBitBridge.lean` supplies
`contentInput?_x_apply_canonical`, the source-field equality, and
`raw_first_table_bit_parsed_target`, the conditional full raw execution
theorem described here.

`raw_first_table_bit_parsed_target` uses the **same dependent `pr`** supplied
by `contentInput?`. Its caller premises are successful parse, explicit matching
tag, `3<=pr.2.n`, positive physical payload
`9+(gammaLen pr.2.n-1)/2<L`, and `pr.2.n<=F` at that width. It constructs the
allocation, dispatcher and register identifications, and proves the full raw
configuration at `144*(R+1)^2+s`, for every persistence padding `s`, with
output **`pr.2.x 0`**, exact tally **`pr.2.n`**, and `pr.2.n=pr.1`.
Only the chosen deadline is polynomially bounded; arbitrary `s` is not.
The canonical field-recovery theorem follows from the coupled gamma/slice
parse witness; it is a source-field equality, not execution by itself.
All claims are forward implications, with no acceptance converse.

Coverage includes physical false/true, `E=L-1`, boundary `E=L`, and virtual
first bits after a partially physical gamma payload, including the minimal
trail `z=2,L=12`. The strict positive-payload premise is essential. At
`z=2,L=11` the wholly virtual payload leaves no erased trail: a finite probe
remains in the left-scan state at head zero after 200 steps. This is neither
coverage nor rejection of that branch. Full-tape raw probes also check before,
at and after handoff/copy, minimal and larger allocation at exact capacity,
`F+1`, the G3s overflow word, and a closed deadline. The materialized test
runner is proved equal to `UniformTM.run`; evaluation supplies no proof axiom.

Still open: all remaining table bits and other parsed fields, exact full
consumption, widths zero/one and the wholly virtual payload for this continuation,
malformed/failed-check rejection completeness, all-input resources, dependent
GN construction/serialization/initialization, witness checks, final acceptance
equivalence, and the V1 Option-Bool/raw-pair to legacy Boolean-TM simulation.
There is no `ContentVerifierBridge` instance, NP membership result, Part A
completion, or reduction of either mainline lower-bound source obligation.
Frozen TMVerifier remains unchanged. On 2026-10-02, after the Lane B owner
exited, the serialized `pnp2-lake lane-a build` passed all four integration
targets: `Tests.UniformV1FixedRawFencedTableFirstBitSurfaceTests`,
`Pnp4.Tests.AlgorithmsToLowerBoundsSurfaceTests`, `Tests.AxiomsAudit`, and
`Pnp4.Tests.AxiomsAudit`. This validates staged integration tree
`3afb3510a15976f1e999fc758dd95c927d595c5d` on main parent
`88b17c754e3d9792bcc865080cef806191dccc0e`; the subsequent validation-record
update changes no Lean source. The six full-tape success probes, closed
deadline, exact-capacity/overflow probes and excluded-branch observation
all ran successfully. All 52 added direct audit roots (33 production) use
only `propext`, `Classical.choice`, and `Quot.sound` where needed. Of the 23
executable-definition roots, 19 have no axioms; `machine`, `sourceBit` and
`outputTape` use `propext`/`Quot.sound`, and `deadline` uses `propext`.
None of those executable roots uses `Classical.choice`. The frozen-tree
checker also passed. Evidence is recorded in
`/root/reports/g3v-current-main-targeted-report-2.md` and its external logs.
The global full check remains outstanding and was omitted by the explicit
slice instruction; no full-gate or independent-review result is claimed.

The following G3u record is historical; G3v adds strict success handoff and
one first-table-bit operation on the qualifying branch.

**Part A G3u — Infrastructure: generic raw fenced countdown.**

On the unchanged 256-state `FixedRawLengthFence.prefixed`, the actual raw H17
predecessor now executes the full countdown. Write `L = a+m`, `R = pairLength a m`,
`P = 3*R+2`, `F = P-(L+3+z)`, and let
`d = FixedGammaTargetRegisterDecrement.borrow x w z` be the decrement phase's
borrow length.
For a matching tag, decoded width `z >= 2`,
sufficient allocation, actual dispatcher witness, and value `v` identified with
the decremented register (including its high-bit bound):

- `v <= F` reaches state 254 on the separator with a zero register, exactly `v`
  tally marks, retained H17 low content, and the installed false fence.
- `F < v` literally rejects in state 255 at `P`, with register `v-F-1`, exactly
  `F` marks, and the same false fence. Equality belongs to success.

Both public theorems are full raw `UniformTM.run` configuration equalities with
persistence. The suffix clocks are `d+2+v*v+v*(2*z+6)+2*z+5` for success and
`d+2+F*F+F*(2*z+6)+2*z+F+6` for rejection; each adds G3t's actual H17 clock.
The old round proofs now expose checkpoints/head bounds, discharging fence
avoidance before the rejecting read. No unfenced execution replaces a raw run.
The branch deadlines are at most `128*(R+1)^2` with a bounded actual dispatcher;
allocation remains `16*(R+1)^2`. Time and allocation are separate parameters.

The pnp4 theorem retains the **same** dependent `pr` from `contentInput?`, with
`pr.2.n = pr.1`, and executes this dichotomy for `v = pr.2.n`. Its success tape
exposes the zero register, separator, exact tally, low content and false fence.
Raw executable/full-tape regressions cover `F-1`, `F`, `F+1`, and the G3s word.

Countdown phase acceptance is not content-verifier correctness. Frozen
TMVerifier paths and transition tables are unchanged.

Remaining parser fields, GN program/serialization/start configuration and
witness checks, malformed-input rejection completeness, acceptance equivalence,
whole-verifier length-only resource domination, and operational advice freedom
remain open. The V1 Option-Bool/raw-pair model still needs its initialization,
alphabet/encoding, clock and verdict simulation into the legacy exact-step
Boolean `TM.accepts` model. `ContentVerifierBridge` is unconstructed; Part A is
unfinished. No `SearchMCSPWeakLowerBound`, `VerifiedNPDAGLowerBoundSource`, or
`NP_not_subset_PpolyDAG` obligation is reduced. This is Infrastructure, not
P-vs-NP mainline progress.

The preceding G3t and following G3s records are historical. G3t and G3u
together close G3s's first listed obligation.

**Part A G3s — Infrastructure: generic fenced H1–H7 and one raw overflow rejection.**
The machine is unchanged: `FixedRawLengthFence.prefixed`, **256 states / 768 rows**,
start 0, accept 254, reject 255. No transition or runtime interpreter is added.
The generic and concrete results have different scopes.

`UniformTM.run_update_of_unvisited` proves locality for one unscanned tape cell.
`FixedRawLengthFenceContent` discharges its avoidance premise using all seven
existing phase footprints: every head through H7 is at most `R+1`, below the
installed fence `P=3*R+2`, where `R=pairLength a m=2*a+1+m`.
For arbitrary dependent words x/w and **every** `2*R+2 ≤ B`,
`raw_fenced_content_exact` starts from literal raw `initialConfig` and reaches
state 109, head `a+m`, the entire `fencedContentTape B x w`, at
`installClock R + contentClock a m`, with
`contentClock a m = 11*a*a+10*a*m+36*a+13*m+23`.
The tape has x followed by w, blanks elsewhere, and the installed false fence.
`raw_fenced_content_trace` preserves that fence and excludes both verdicts
through H7. Empty pairs are included (their raw encoding has length one).
`content_prefix_resources` discharges room and this prefix clock at the existing
`allocation R=16*(R+1)^2`; it is not a whole-machine resource theorem.

`FixedRawLengthFenceOverflowWitness` supplies the separate closed witness
`x=1`, `w=011001000000111111`, raw `011011001000000111111`, with
`a=1,m=18,N=19,R=21,B=45`: 67 allocated cells, false fence at 65, width 5.
The decremented register is 62; therefore the pre-H17 copied value is 63
(an arithmetic inference from the borrow-free decrement).
`overflow_values` proves the matching tag, gamma width, original dispatcher's
strict first terminal at C=21 in `qHasOne`, borrow zero and the actual digit
identities. This is not identification with a returned `contentInput?` object.
H11 executes the existing merged dispatcher, retaining its actual routing.

Installation ends at 1517; H1–H7 end at
1560/1564/1565/1573/1636/1979/2001. The concrete fenced H8–H17 boundaries are
2065/2071/2086/2107/2129/2166/2197/2209/2314/2335.
`overflow_h17_exact` proves state 245, head 25, whole `overflowTape 62 0`.
Countdown enters `qLoop` at 2337, completes 38 rounds at 4389 with register 24,
then decrements to **23** before scanning the fence. `overflow_prereject_exact`
proves state 251, head 65, whole `overflowTape 23 38` at 4442.
`overflow_reject_row` is the existing false-symbol write/stay row to reject 255;
`overflow_reject_exact s` proves the complete literal rejecting configuration
from raw `initialConfig` at **4443+s**, with persistence by `run_reject`.
`overflow_fence_trace` keeps the false fence and head at most 65 throughout
1517–4443. The final tape has tag cells 0–7, false zeros 8–12, blanks 13–17,
true terminator 18, blank 19, register `010111` at 20–25, blank 26,
exactly 38 true marks 27–64, false fence 65 and blank 66.

The finite proofs reduce segments of at most 64 suffix steps and 91 countdown
steps; the 105-step payload loop is split into 31/31/31/12. Whole configurations
are composed with `run_add` and existing `seq_run_right` embeddings, retaining
raw-length indices throughout. No monolithic 4443-step kernel reduction is used.
Surface probes separately check an empty raw pair, a theorem-derived mixed pair,
and phase-local last-mark/exhaustion/overflow boundaries. Those boundary probes
supply countdown configurations and are not additional raw-input capstones.
The intended generic boundary is strict: `v ≤ F` fits and `F < v` overflows.
That universal theorem is still open; the phase-local probes check its last-step
cases only. The raw overflow witness has F=38. Since **4443>B=45**, this is exact
execution, not `RejectsWithin ... 45`. Inherited left clamps remain; the suffix
is not claimed clamp-free. The unfenced drain theorem is never substituted for
a run on the installed fence.

At the G3s snapshot, the following obligations remained open. G3t and G3u later
together close item 1, and G3u identifies the executed countdown target with
`pr.2.n`; the remaining fields in item 2 and items 3–6 stay open.

1. Generic fenced H8–H17 preservation and generic countdown success/overflow
   from the actual predecessor configuration; G3s proves only the stated raw witness.
2. Identify every field and dependent length of the **same** `pr` returned by
   `contentInput? codec z`: `pr.2.tag`, `.n`, `.x`, `.i`, `.p`, `.padBits`, `.pad`,
   with `codec := treeCircuitWitnessCodec (thresholdPoly k)` and `z := Fin.append x w`.
   `pr.2.n = pr.1` alone does not identify the executed register.
3. Build the dependent `GNProgram`, serialization and physical starting configuration
   from those fields and `contentWitness codec z pr.2.n`; complete gate/witness
   verification. Frozen GN work and GN-E2-4b donor-only status are unchanged.
4. Connect V1 Option Bool/pair execution to legacy Boolean/`concatBitstring`
   `TM.runConfig`, accounting for initialization, time, space and verdicts.
5. Prove whole-machine length-only polynomial allocation and clock, domination
   on every branch and operational advice freedom. Only the installed H1–H7 prefix
   has the new polynomial resource guarantee.
6. Prove the final acceptance equation for `contentSemanticAccepts`, including
   malformed-input rejection completeness and failed witness checks; timeout is not rejection.

`ContentVerifierBridge`, canonical NP witnesses, Part A completion,
`SearchMCSPWeakLowerBound` and `VerifiedNPDAGLowerBoundSource` remain open.
No pnp4 bridge or semantic acceptance theorem is added; its accepted-content
bridge remains at G3e. This is Infrastructure, not P-vs-NP mainline progress.

The following G3r record is historical; its then-open fence obligations are narrowed above.

**Part A G3r — Infrastructure: executed raw-length false fence and exact G3q handoff.**
`FixedRawLengthFence.machine` is a fixed **48-state / 144-row** three-symbol table,
start 0, accept 2, reject 3. For raw length R, it reads every bit, uses an origin
hole and a temporary tally, restores the input, erases the tally and accepts at head
zero with exactly one nonblank cell beyond the input: `some false` at `3*R+2`.
The endpoint has blank cells R and R+1, including R=0. The installation clock is
4 for R=0 and `3*R*R+9*R+5` otherwise. For every `2*R+2 ≤ B`,
`install_exact` proves complete configuration equality from literal raw
`initialConfig`; `install_trace` proves strict first terminal arrival, head
at most `3*R+2`, and no attempted boundary clamping. `installed_cells` states
the executed restoration and unique suffix marker. Insufficient-room probes
can clamp and accept with a misplaced marker; no all-budget result is claimed.

`allocation R = 16*(R+1)^2` supplies both room and a polynomial installation
deadline. No transition takes R, B, a parser result, target, proof or advice.
`prefixed = machine.seq G3q.machine` has **256 states / 768 rows**, start 0,
accept 254, reject 255. `raw_fence_handoff_exact` runs from literal raw input
at that allocation: at `installClock R+s` its whole configuration equals
G3q's actual s-step run from state 0, head zero and the installed fenced tape,
embedded at offset 48. At s=0 the composite is in state 48, neither verdict.
The raw `[true,false,true]` witness has R=3, B=256, time 59 and marker 11;
the full tape contains only cells 0=true, 1=false, 2=true and 11=false.

Review hypothesis freeze: `install_exact`, `install_trace`, `installed_cells`
and `fence_handoff_exact` require exactly `2*R+2 ≤ B`; the raw capstones
supply that inequality using `allocation R` and take no propositional premise.
Their execution is V1 `UniformTM.run`, not legacy `TM.runConfig`. The suffix
time `s` is arbitrary, with no suffix verdict or runtime bound asserted.
G3q's eight drain premises recorded below still concern its unfenced entry;
none supplies the missing fenced-entry preservation theorem.

At G3r the following obligations were open; G3s above narrows the first and the prefix resources:

1. Preserve the fence through H1–H17 and prove fenced countdown success and
   literal overflow rejection from the actual predecessor configuration.
   The existing G3q whole-tape drain theorem ends in an unfenced `loopTape`
   and cannot be substituted for this missing proof.
2. Identify every field of the **same** `pr` returned by `contentInput? codec z`,
   with `codec := treeCircuitWitnessCodec (thresholdPoly k)` and `z := Fin.append x w`:
   `pr.2.tag`, `.n`, `.x`, `.i`, `.p`, `.padBits`, `.pad`, and dependent lengths.
   The semantic fact `pr.2.n = pr.1` does not identify the executed register.
3. Build the actual dependent `GNProgram`, serialization and physical starting
   configuration from those fields and `contentWitness codec z pr.2.n`;
   complete gate/witness verification. An already encoded GN input supplies
   neither bridge. Frozen GN work and GN-E2-4b donor-only status are unchanged.
4. Connect V1 Option Bool/pair execution to legacy Boolean/`concatBitstring`
   `TM.runConfig`, including initialization, time, space and verdicts.
5. Prove explicit whole-machine length-only polynomial allocation and clock,
   domination on every branch and operational advice freedom. G3r's resource
   theorem covers installation alone, not the unbounded suffix time s.
6. Prove the final exact-step acceptance equation for `contentSemanticAccepts`,
   including malformed input and failed witness checks; timeout is not rejection.
`ContentVerifierBridge`, canonical NP witnesses, Part A completion,
`SearchMCSPWeakLowerBound` and `VerifiedNPDAGLowerBoundSource` remain open.
This is Infrastructure, not P-vs-NP mainline progress. The pnp4 accepted-content
bridge remains at G3e; no bridge instance or acceptance theorem is added.

The following G3q record concerns its original unfenced raw entry.

**Part A G3q — Infrastructure: executed sentinel → unchanged G3p handoff H1.**
`FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine` is exactly
`FixedPairConcatSentinel.machine.seq
FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine`:
**208 states / 624 rows**, start 0, accept 206, reject 207, G3p entry 7.
All seventeen **named operational handoffs** are now executed in this chain.
This closes H1 execution, not the semantic verifier or either P-vs-NP source obligation.

`raw_suffix` and `handoff_exact` start from literal raw `initialConfig` on every
raw word and every allocation budget B, including zero. With raw length
`R = pairLength a m = 2*a+1+m` and content length `L = a+m`, H1 executes at
`S0 = 2*R+1`, strictly confined to the five sentinel work controls before S0.
The complete successor has state 7, literal head zero and `sentinelTape`.
Raw cell R is blank; phase-local cell R is `some true`, even at B=0.
The three live H1 rows on arbitrary raw words are start/blank, back-false/blank,
and back-true/blank. Only the latter two occur on encoded pairs: they restore
the saved first **raw** bit by a write/stay transition. The three dead
accept-source rows are not additional live handoffs. The old verdict copies
5/6 are neither the start nor transition targets. Sentinel steps before H1
are clamp-free; the inherited removal-origin left clamp is retained.

H2 follows at `S0 + 2*a+2`, in state 12, head `2*a`, with the whole sentinel
tape unchanged. The pre-H2 row is state 9/nonblank → state 12/same bit/left,
from positive address `2*a+1`. H3/H4/H5/H6/H7 states are 15/24/31/57/61;
full suffix transport preserves the physical allocation `Config 208 R B`
through compaction and countdown. Time through H2 is `6*a+2*m+5 ≤ 3*R+2`.
Malformed syntax rejection is proved at `3*R+3+s` for every s, retaining
head `R+1` and the entire sentinel tape, under exactly `decodePair raw = none`
and **B>0**. A literal B=0 counterexample prevents dropping that restriction.
Both inherited content rejection implications persist at all later deadlines.

`raw_countdown_drained` retains exactly eight G3p premises: matching tag;
gamma width for `Fin.append x w`; dispatcher `StrictFirstTerminalAt B x w C q`;
`2 ≤ zeros`; `v ≤ F`; `zeros+2+F ≤ a+B`; identification of every register bit
with `decBit x w zeros (borrow x w zeros)`; and zero high bits of v.
It executes from raw input at `S0 + G3p.cursorChainClock C a m zeros d v`,
where `d = borrow x w zeros`, to literal accept 206, head `L+2+zeros`, the
whole `loopTape B x w zeros 0 v`, full configuration equality and persistence.
C/q/v/F are theorem-side run/value descriptions; no transition takes them.
The dispatcher q retains its dispatcher-control type and strict exclusion of
all earlier terminals; no successful-q premise is added. F is only a room
bound, and the bit premises do not supply a length-only polynomial cap.
The closed literal witness discharges all eight premises at
`a=8,m=9,B=22,zeros=4,C=18,q=qHasOne,d=0,v=F=24` and runs for
**3044 = 53+2991 steps**, accept 206, head 23, all 49 tape cells pinned.
Its H1–H7 times are 53/71/72/178/242/1832/1852; H5 head 27, H7 head 17,
and the removal-origin clamp occurs at 176. Register cells 18–22 are false,
23 blank, marks 24–47 true, and 48 blank. This is execution nonvacuity,
not `ContentAccepts` nonvacuity or first arrival of composed accept.

Explicitly open: runtime-enforced fence/cap and overflow rejection; full parser
fields, parser→GN encoding/configuration bridge, and gate/witness verification
(the frozen GN track remains separate); identification of the executed register
with the same authoritative dependent parser field `pr.2.n`; whole-machine
length-only polynomial runtime, budget domination, externally fixed polynomial
allocation, and operational advice freedom; V1 Option Bool/pair-encoded
`UniformTM` to legacy Boolean/`concatBitstring` `TM.runConfig` conversion with
time/space/acceptance accounting; content acceptance equivalence and rejection
completeness (timeout/nonacceptance is not rejection); `ContentVerifierBridge`,
canonical NP witnesses, `SearchMCSPWeakLowerBound`, and
`VerifiedNPDAGLowerBoundSource`. Since 3044>B=22, allocation is visibly not a
runtime deadline. The accepted-content pnp4 bridge remains at G3e; no new
pnp4 bridge instance is supplied. This is Infrastructure, not P-vs-NP mainline progress.

The following G3p record is historical (sixteen executed, H1 then remaining).

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

The following G3o record is historical (fifteen executed, two remaining at that stage).

Part A G3o executed **H3**, separator-hole into unchanged G3n, in a
196-state, 588-row `UniformTM`: **fifteen** executed handoffs, **two** remaining
(H1–H2). The unconditional strict whole-configuration handoff costs one step;
the drain retains exactly eight G3n premises. Its theorem-derived 2973-step
fixture uses hand-supplied `v=24`, accept 194, head 23 and the complete drained
tape with persistence, witnessing execution premises only. H4–H7 have controls
12/19/45/49 at the inherited times plus one. Rejections remain forward guarantees.
At that stage, still open: executing H1–H2 to connect raw input, later parser fields, model
conversion, runtime fence, budget domination, and a verifier bridge. No first
arrival of composed accept, language acceptance or runtime selection of `C/q/v`
is proved. The pnp4 accepted-content bridge still starts at G3e; neither
mainline lower-bound source obligation is reduced.

This is Infrastructure only. Wrapper-level `L'`
padding invariance and formal runtime/advice enforcement also remain open; complete-word
`ContentAccepts` padding invariance does not close either item. The original length-gated
`NP_not_subset_PpolyDAG_treePoly` / `PrefixExtensionNPWitness` capstone remains compiled and audited
as a compatibility route. See `pnp4/Pnp4/Frontier/ContractExpansion/README.md` for the full
proved-vs-open breakdown.

## Non-Goals Right Now

- Do not claim full unconditionality.
- Do not add wrappers that hide the false support-bounds source.
- Do not present the public zero-argument/provider API as assumption-free.
- Do not reopen the literal fixed-slice support-half branch as the main route.
- Do not treat Lean formalization alone as capable of closing the missing
  MCSP/Ppoly lower-bound mathematics.

## Practical Work Items

1. Keep `FormulaSupportBoundsFalsifiabilityProbe.lean` as the authoritative
   audit module for support-bounds falsifiability.
2. Keep `pnp3/Magnification/UnconditionalResearchGap.lean` as the single-file
   frontier **for the pnp3 route**: a pnp3-side unconditional closure should prove
   `ResearchGapWitness` there and then expose `P_ne_NP_unconditional` from that same
   file.  A pnp4-side closure (Target 4) need not be re-expressed as
   `ResearchGapWitness` — its endpoint already produces
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`, which is exactly
   `ResearchGapWitness.dagSeparation` — though routing it through that witness remains
   an option.  See `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
3. If a new support/provenance contract is proposed, first add a falsifiability
   audit before wiring it into final theorems.
4. If a new route depends on exact MCSP thresholds, Shannon slack, or small
   simulation overheads, first prove a separate fine-grained simulation
   adequacy theorem.
5. If a new algebraic/spectral/SOS/finite-field route cannot produce
   combinatorial support or accepted-family certificates, integrate it directly
   at `ResearchGapWitness` rather than forcing it through AC0/locality plumbing.
6. Optionally finish independent verifier/formalization milestones such as the
   polynomial-time MCSP verifier, but do not present them as closing `P != NP`.
7. Keep `LowerBounds.AC0_GapMCSP` as a deprecated compatibility quarantine.
   The canonical audit theorem is
   `false_of_smallAC0Params_and_easyFamilyData`; it records that the enriched
   parameter/easy-family assumptions imply `False` without solver correctness.
   Do not present the historical `in_AC0` / `not_in_AC0` names as a standard
   circuit-class result, a publishable AC0 lower bound, or a closure route.
