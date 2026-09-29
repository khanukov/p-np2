# TODO / Roadmap (current)

Updated: 2026-09-24

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
- `./scripts/check.sh` passes.
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

The following obligations remain open, in order:
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
