import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The content tag gate, the gamma terminator, the gamma anchor, the payload dispatcher, the scratch
bootstrap, the first payload digit, the second payload digit, the loop markers, the payload loop, the
decrement and the countdown as one machine (Part A G3j)

**No new table row.**  `machine` is `FixedContentTagGate.machine.seq
FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`:
G1's fixed 15-state, 45-row content tag gate on the left block `[0, 15)` and the whole landed G3i
132-state composite on the right block `[15, 147)`, one closed 147-state, 441-row table whose every
row is a row of one of those eleven tables with its target routed.  Write `N = a + m` and
`d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Ten executed handoffs.**  H8 — G1's content tag gate into G2's gamma terminator — is the newly
executed one, and it has exactly **one** live routed row: the last tag state `12` on `some false`,
the gate's only row targeting its accept outside the accept's own absorbing three
(`accept_row_unique`), which `seq` retargets to the right block's start `tailStart` at index `15`,
writing `some false` and moving **right**, in that same transition and at no cost.  Unlike the
terminator's and the anchor's, the gate's reject is the target of *many* live rows — the mismatch
exits of the eight tag positions and the rewind's defensive rows — and `reject_rows_routed` sends
every one of them to the composed reject `146`.  The left copies of the two gate verdicts are dead:
no composed row targets either (`table_and_resource_pins`).  H9 (`15 → 18`, the terminator's `qScan`
on `some true`), H10
(`21 → 24`, the anchor's `qReturn` on `some true`) and H11 (six rows inside `[24, 52)`, all into
`52`) to H17 (`133 → 136`) are inherited from G3i, its indices shifted by fifteen and located by
`(inTail q).val = 15 + q.val` with the universal right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The gate has exactly two
absorbing states, `qAccept` and `qReject` — its raw states `13` and `14`, three rows each — so the
landed `seq` routes both and no `mergeAccept` is needed, as for H9 and H10 and unlike H11.  Its
strict first arrival was *not* exported in the shape `seq` consumes: the landed
`exact_terminal_contract` gives the strictness but names a private endpoint configuration, so
`gate_first_arrival` assembles the `state = accept` form from it and from the landed `run_deadline`,
with no room premise.  On a matching tag the gate is in neither verdict before
`switchTime N = 3 * N + 7` and in `finalConfig` at it, and that time **is** its own length-only
deadline — `gate_first_arrival` pins that identity, so the composed machine loses nothing by not
being able to wait for a deadline.  Its endpoint is compatible with the right block's start by
construction: G2's `startConfig` retags the gate's `finalConfig` itself,
which `run_deadline` shows *is* the gate's run at `switchTime N` for every input, so the switch hands
over exactly the head and tape the right block's own `startConfig` carries — the unchanged content
tape, on the gamma cell `8`.  The switch time is length-only, neither width- nor path-dependent: it
adds a linear prefix to the composed clock and no new room premise.

**The composed run.**  `handoff_exact` takes the matching tag — **one** hypothesis, no width, no
room, no budget: the run out of `startConfig` is in neither composed verdict at any time up to and
including `3 * N + 7` (at the switch time itself the control is `tailStart`, so the bound is `≤`),
is G1's own run routed at every such time, at exactly `3 * N + 7` **is** G3i's landed
`startConfig B x w` re-embedded, and every later step is a G3i step.  `handoff_endpoint_pins` reads
that switch configuration back as G2's own `startConfig` projections — the control as `tailStart`,
the head and the whole tape as G2's own — and records that the head is the gamma cell `8`, that the
tape is the unchanged `contentTape`, and that cell `7` still carries the tag's own last bit
`some false` there.  `tagged_inherited_switch` locates the inherited H9 at `3 * N + 7 + (zeros + 1)`
inside this machine, `tagged_inherited_anchor_switch` the inherited H10 at
`3 * N + 7 + (zeros + 1 + (2 * zeros + 5))`, and the drained theorem lands the composed accept `145`
at exactly `gateChainClock C N zeros d v = 3 * N + 7 + terminatorChainClock C N zeros d v` under
G3i's eight hypotheses unchanged.  Two rejecting branches are proved, and the second is new to the
chain.  On a matching tag whose physical suffix holds **no** gamma terminator the gate hands over,
the terminator rejects at exactly its deadline `N - 7` and not before, and
`malformed_reject_handoff` lands the composed reject `146` from `3 * N + 7 + (N - 7)` on.  On a
**mismatched** tag — the first statement in this chain that assumes the tag does *not* match —
`mismatched_tag_reject_handoff` lands the composed reject `146` from `3 * N + 7` on, the right block
never running.  Both are forward direction only.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
seven handoffs before H8 remain proof-level identifications (G1's `startConfig` retags the actual
marker-erase `finalConfig`, which `handoff_pins` records hypothesis-free), no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  The mismatched
branch is **not** timed exactly: the gate first rejects at its mismatch index, and the phase's
public API exposes that index only through `finalConfig.head`, whose defining `badIndex` is private,
so only the length-only deadline `3 * N + 7` is claimed and no "and not before" accompanies it.  No
**first arrival** of the composed accept (the arrivals proved are the gate's and, as a hypothesis,
the dispatcher's, each inside its own block); the **fence** (all eleven tables are uncapped); every
**converse**, so neither composed reject implies anything about the input; a **footprint** theorem;
and the pnp4 bridge, not built here, the standalone phases' pnp4 semantics being unchanged.  The
composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior
endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or `ContentVerifierBridge` is stated.  The table is fixed and complete
but not claimed state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros? terminalIndex)
open FixedContentGammaAnchor (successTime markedTape)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (terminatorChainClock
    terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained)

/-- The composed machine: G1's content tag gate, then G3i's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedContentTagGate.machine.seq
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- A tag-gate state in the composed control, at its own index. -/
def inGate (q : Fin FixedContentTagGate.stateCount) : Fin machine.stateCount :=
  FixedContentTagGate.machine.seqLeft
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- A G3i state in the composed control, shifted past the fifteen tag-gate states. -/
def inTail
    (q : Fin
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedContentTagGate.machine.seqRight
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- The routed target of a tag-gate row: `qAccept` becomes G3i's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedContentTagGate.stateCount) : Fin machine.stateCount :=
  FixedContentTagGate.machine.seqRoute
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- G3i's start in the composed control, index `15`: the target of the one live routed row. -/
def tailStart : Fin machine.stateCount :=
  inTail
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start

/-- G1's own `startConfig` — the retagged *actual* marker-erase endpoint — routed into the composed
control.  Still a phase-local retag, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedContentTagGate.machine.seqEmbedRouted
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedContentTagGate.startConfig B x w)

/-- The tag gate's strict first arrival, and its own length-only deadline: three steps per physical
cell to rewind, then the seven tag cells and the step that leaves the eighth. -/
def switchTime (N : Nat) : Nat := 3 * N + 7

/-- Exact cost of the tag-gate phase followed by the whole of G3i: the gate's length-only first
arrival `3 * N + 7`, plus the terminator's width-only `zeros + 1`, plus the anchor's width-only
`2 * zeros + 5`, plus the dispatcher's input-dependent `C`, plus G3e's `bootChainClock`.  All four
handoffs cost nothing. -/
def gateChainClock (C N zeros d v : Nat) : Nat :=
  switchTime N + terminatorChainClock C N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the state and row counts, the gate's start and verdicts, the
distinguished states with their indices, the block injections with their offsets and disjointness,
`tailStart` at `15`, the routing cases, every left row as the routed gate row, every right row as
the G3i row, the public step against the composed raw table, the one live routed row — the last tag
state `12` on `some false`, moving right — the two dead verdict copies' three rows each, and that no
**left-block** row targets either dead copy, which together with the right-block row equation and
`inGate p ≠ inTail q`, both conjuncts above, is every composed row.  Inherited rows are not
restated: the right-block row equation transports every G3i row verbatim. -/
theorem table_and_resource_pins :
    machine.stateCount = 147 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 441 ∧
      FixedContentTagGate.machine.start.val = 0 ∧
      FixedContentTagGate.machine.accept.val = 13 ∧
      FixedContentTagGate.machine.reject.val = 14 ∧
      machine.start = route FixedContentTagGate.machine.start ∧
      machine.start = inGate FixedContentTagGate.machine.start ∧
      machine.accept =
        inTail
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inTail
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 145 ∧ machine.reject.val = 146 ∧
      (∀ q, (inGate q).val = q.val) ∧ (∀ q, (inGate q).val < 15) ∧
      (∀ q, (inTail q).val = 15 + q.val) ∧ (∀ q, 15 ≤ (inTail q).val) ∧
      Function.Injective inGate ∧ Function.Injective inTail ∧
      (∀ p q, inGate p ≠ inTail q) ∧
      tailStart =
        inTail
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      tailStart.val = 15 ∧ route FixedContentTagGate.machine.accept = tailStart ∧
      route FixedContentTagGate.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedContentTagGate.machine.accept → q ≠ FixedContentTagGate.machine.reject →
        route q = inGate q) ∧
      (∀ q s, machine.step (inGate q) s =
        (route (FixedContentTagGate.machine.step q s).1,
          (FixedContentTagGate.machine.step q s).2.1,
          (FixedContentTagGate.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail
            (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inGate ⟨12, by decide⟩) (some false) = (tailStart, some false, .right) ∧
      (∀ s, machine.step (inGate FixedContentTagGate.machine.accept) s = (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inGate FixedContentTagGate.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inGate q) s).1 ≠ inGate FixedContentTagGate.machine.accept ∧
        (machine.step (inGate q) s).1 ≠ inGate FixedContentTagGate.machine.reject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedContentTagGate.machine.seq_pins
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, by decide, by decide, by decide,
    fun _ => rfl, fun q => q.isLt, fun _ => rfl, fun _ => Nat.le_add_right _ _,
    hli, hri, hne, rfl, by decide, hra, hrr, hrw,
    fun q s => FixedContentTagGate.machine.seq_step_left
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentTagGate.machine.seq_step_right
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentTagGate.machine.seq_step_eq_rawStep
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    by decide, ?_, ?_, ?_⟩
  · exact hrw FixedContentTagGate.machine.start (by decide) (by decide)
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · decide

/-- **The tag gate has exactly one live row targeting its accept.**  Over all fifteen states and all
three symbols, with the accept's own absorbing three excluded, a target of
`FixedContentTagGate.machine.accept` forces the last tag state `12` on `some false`.  So H8 has
exactly one live routed row.  This quantifies over the gate's rows alone and says nothing about the
composed table as a whole: the inherited right block keeps its own rows, and the excluded rows are
the dead left copies' own, which `seq` routes to `tailStart` and to the composed reject and no
composed row ever enters. -/
theorem accept_row_unique (q : Fin FixedContentTagGate.stateCount) (s : Option Bool)
    (hq : q ≠ FixedContentTagGate.machine.accept)
    (h : (FixedContentTagGate.machine.rawStep q s).1 = FixedContentTagGate.machine.accept) :
    q.val = 12 ∧ s = some false := by
  revert h
  revert hq
  revert s
  revert q
  decide

/-- **Every live row targeting the gate's reject is routed to the composed reject `146`.**  Unlike
the terminator's and the anchor's, the gate's reject is the target of many live rows — the mismatch
exits of the eight tag positions and the rewind's defensive rows — so no uniqueness holds and none is
claimed; what holds is that `seq` sends all of them to the composed reject, with the symbol written
and the move unchanged.  No count is claimed either.  The two verdicts' own rows are excluded: both
of their left copies are dead. -/
theorem reject_rows_routed (q : Fin FixedContentTagGate.stateCount) (s : Option Bool)
    (ha : q ≠ FixedContentTagGate.machine.accept)
    (hq : q ≠ FixedContentTagGate.machine.reject)
    (h : (FixedContentTagGate.machine.rawStep q s).1 = FixedContentTagGate.machine.reject) :
    machine.step (inGate q) s =
      (machine.reject, (FixedContentTagGate.machine.rawStep q s).2.1,
        (FixedContentTagGate.machine.rawStep q s).2.2) := by
  have hstep : FixedContentTagGate.machine.step q s = FixedContentTagGate.machine.rawStep q s :=
    FixedContentTagGate.machine.step_of_ne ha hq s
  have hleft : machine.step (inGate q) s =
      (route (FixedContentTagGate.machine.step q s).1,
        (FixedContentTagGate.machine.step q s).2.1,
        (FixedContentTagGate.machine.step q s).2.2) :=
    FixedContentTagGate.machine.seq_step_left
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s
  rw [hleft, hstep, h]
  rfl

/-- **The start is the retagged actual marker-erase endpoint, not a raw input, and this needs no
hypothesis.**  The marker-erase phase's run at its own clock `N + 3` is its `finalConfig`, on the
boundary cell `N` over the content tape; G1's `startConfig` is that configuration retagged; and this
slice's `startConfig` is *that* one routed into the composed control — the same head and tape, the
composed start `0` as control.  This is handoff **H7**, recorded as an identification and not
executed by this table.  No `initialConfig` and no raw pair input appears, and neither retag costs a
step. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairContentMarkerErase.machine.run (FixedPairContentMarkerErase.clock a m)
      (FixedPairContentMarkerErase.startConfig B x w)
    let p := FixedContentTagGate.startConfig B x w
    let c := startConfig B x w
    g = FixedPairContentMarkerErase.finalConfig B x w ∧
      p.state = FixedContentTagGate.machine.start ∧ p.head = g.head ∧ p.tape = g.tape ∧
      c =
        FixedContentTagGate.machine.seqEmbedRouted
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          p ∧
      c.state = machine.start ∧ c.state = inGate FixedContentTagGate.machine.start ∧
      c.head = g.head ∧ c.tape = g.tape ∧ c.head.val = a + m ∧
      c.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hfin, -, hstate, hhead, htape⟩ := FixedContentTagGate.handoff_exact (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedContentTagGate.machine.seq_pins
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨hfin, hstate, hhead, htape, rfl, rfl,
    hrw FixedContentTagGate.machine.start (by decide) (by decide), hhead, htape, ?_, ?_⟩
  · rw [show (startConfig B x w).head = _ from hhead, hfin]
    rfl
  · rw [show (startConfig B x w).tape = _ from htape, hfin]
    rfl

/-- The chained clock, pinned: G3i's sum prefixed by the gate's length-only first arrival
`3 * N + 7`, that arrival identified with the gate's own deadline, the two width-only arrivals G3i
and G3h contribute, and on `2 ≤ zeros` its full expansion.  `C` has no closed form in `N`. -/
theorem clock_pins (C N zeros d v : Nat) :
    gateChainClock C N zeros d v = switchTime N + terminatorChainClock C N zeros d v ∧
      switchTime N = 3 * N + 7 ∧
      (∀ a m : Nat, switchTime (a + m) = FixedContentTagGate.deadline a m) ∧
      (∀ z : Nat,
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          z = z + 1) ∧
      (∀ z : Nat, successTime z = 2 * z + 5) ∧
      gateChainClock C N zeros d v =
        3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + (C + bootChainClock N zeros d v))) ∧
      (2 ≤ zeros → gateChainClock C N zeros d v =
        3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + (C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))))))) := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun hz => ?_⟩
  show switchTime N + terminatorChainClock C N zeros d v = _
  rw [(FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    C N zeros d v).2.2 hz]
  rfl

/-! ### The tag gate's arrivals, in the shape the composition consumes -/

/-- **The tag gate's strict first successful arrival.**  On a matching tag it is in neither verdict
at every time before `switchTime N = 3 * N + 7`, at that time its run **is** its `finalConfig` and
its control its accept, that time **equals** its own length-only deadline, and the matching tag
forces `8 ≤ N`.  Derived from the landed `exact_terminal_contract`, whose endpoint configuration is
private, and the landed `run_deadline`; no room premise. -/
theorem gate_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ t, t < switchTime (a + m) →
        (FixedContentTagGate.machine.run t (FixedContentTagGate.startConfig B x w)).state ≠
            FixedContentTagGate.machine.accept ∧
        (FixedContentTagGate.machine.run t (FixedContentTagGate.startConfig B x w)).state ≠
            FixedContentTagGate.machine.reject) ∧
      FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w ∧
      (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).state = FixedContentTagGate.machine.accept ∧
      switchTime (a + m) = FixedContentTagGate.deadline a m ∧ 8 ≤ a + m := by
  obtain ⟨-, -, -, -, -, -, -, -, hiff, hlen⟩ :=
    FixedContentTagGate.tag_contract (Fin.append x w)
  obtain ⟨-, -, -, hgood⟩ := FixedContentTagGate.exact_terminal_contract (B := B) x w
  obtain ⟨hno, -⟩ := hgood (hiff.mp htag)
  have hrun : FixedContentTagGate.machine.run (switchTime (a + m))
      (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w :=
    FixedContentTagGate.run_deadline (B := B) x w
  refine ⟨hno, hrun, ?_, rfl, ?_⟩
  · rw [hrun]
    simp [FixedContentTagGate.finalConfig, FixedContentTagGate.machine, htag]
  · simpa using hlen htag

/-- **The tag gate's rejecting arrival, at its length-only deadline.**  On a mismatched tag its run
at `switchTime N` **is** its `finalConfig` and its control its reject.  There is deliberately no
"and not before": the gate first rejects at its mismatch index, which its public API exposes only
through `finalConfig.head`, whose defining `badIndex` is private. -/
theorem gate_reject_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    FixedContentTagGate.machine.run (switchTime (a + m))
        (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w ∧
      (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).state = FixedContentTagGate.machine.reject := by
  have hrun : FixedContentTagGate.machine.run (switchTime (a + m))
      (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w :=
    FixedContentTagGate.run_deadline (B := B) x w
  refine ⟨hrun, ?_⟩
  rw [hrun]
  simp [FixedContentTagGate.finalConfig, FixedContentTagGate.machine, htag]

/-- G2's `startConfig` is the tag gate's run at `switchTime N`, retagged — and this holds for
**every** input, matching tag or not, because the gate's `run_deadline` is unconditional.  This is
the semantic dependency H8 has to respect; it executes nothing.  Only the *handoff* needs the
matching tag, since only then is that run the gate's accept. -/
theorem terminator_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    FixedContentGammaTerminator.startConfig B x w =
      FixedContentGammaTerminator.retag
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)) := by
  unfold FixedContentGammaTerminator.startConfig
  rw [show FixedContentTagGate.machine.run (switchTime (a + m))
      (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w from
    FixedContentTagGate.run_deadline (B := B) x w]

/-! ### The executed handoff -/

/-- **H8 fires when the tag gate leaves the last tag cell, and it costs nothing.**  On a matching
tag — **one** hypothesis, no width and no room premise — the run out of `startConfig` is in neither
composed verdict at any time up to and including `3 * N + 7` (at the switch time itself the control
is `tailStart`, so the bound is `≤`), is G1's own run routed at every such time — same head and
whole tape — at exactly `3 * N + 7` **is** G3i's landed `startConfig B x w` re-embedded, and runs
G3i on from there. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let c := startConfig B x w
    (∀ t, t ≤ switchTime (a + m) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime (a + m) → machine.run t c =
        FixedContentTagGate.machine.seqEmbedRouted
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentTagGate.machine.run t (FixedContentTagGate.startConfig B x w))) ∧
      machine.run (switchTime (a + m)) c =
        FixedContentTagGate.machine.seqEmbedRight
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (switchTime (a + m) + s) c =
        FixedContentTagGate.machine.seqEmbedRight
          FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) := by
  intro c
  obtain ⟨hno, hend, hacc, -, -⟩ := gate_first_arrival (B := B) x w htag
  have hwork : ∀ t, t < switchTime (a + m) →
      (FixedContentTagGate.machine.run t (FixedContentTagGate.startConfig B x w)).state ≠
        FixedContentTagGate.machine.accept := fun t ht => (hno t ht).1
  have hcfg :
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
        B x w =
      ⟨FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).head,
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).tape⟩ := by
    rw [hend]
    exact Config.ext_parts rfl rfl rfl
  have hleft :=
    FixedContentTagGate.machine.seq_run_left
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentTagGate.startConfig B x w) hwork
  have hsuffix : ∀ s, machine.run (switchTime (a + m) + s) c =
      FixedContentTagGate.machine.seqEmbedRight
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          s
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) := by
    intro s
    rw [hcfg]
    exact FixedContentTagGate.machine.seq_handoff
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentTagGate.startConfig B x w) hwork hacc s
  have hC : machine.run (switchTime (a + m)) c =
      FixedContentTagGate.machine.seqEmbedRight
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          B x w) := hsuffix 0
  have hCs : (machine.run (switchTime (a + m)) c).state = tailStart := by
    rw [hC]; rfl
  have hCa : (machine.run (switchTime (a + m)) c).state ≠ machine.accept := by
    rw [hCs]; decide
  have hCr : (machine.run (switchTime (a + m)) c).state ≠ machine.reject := by
    rw [hCs]; decide
  exact ⟨UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩

/-- **What the switch hands over is exactly what G2 reads.**  At the gate's first arrival
`3 * N + 7`: the composed control is G3i's start `15`, the composed head and whole tape are *the
same* projections G2's own `startConfig` carries, the head is the gamma cell `8`, the tape is the
unchanged `contentTape`, and cell `7` still carries the tag's own last bit `some false` there. -/
theorem handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let e := machine.run (switchTime (a + m)) (startConfig B x w)
    let p := FixedContentGammaTerminator.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = some false) := by
  obtain ⟨-, -, hC, -⟩ := handoff_exact x w htag
  obtain ⟨-, -, -, -, h8N⟩ := gate_first_arrival (B := B) x w htag
  obtain ⟨-, -, -, -, -, -, -, he7, hiff, -⟩ :=
    FixedContentTagGate.tag_contract (Fin.append x w)
  obtain ⟨-, -, -, -, -, -, -, h8, htp⟩ :=
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_pins
      (B := B) x w htag
  have hhead : (machine.run (switchTime (a + m)) (startConfig B x w)).head =
      (FixedContentGammaTerminator.startConfig B x w).head := congrArg Config.head hC
  have htape : (machine.run (switchTime (a + m)) (startConfig B x w)).tape =
      (FixedContentGammaTerminator.startConfig B x w).tape := congrArg Config.tape hC
  have hheadval : (machine.run (switchTime (a + m)) (startConfig B x w)).head.val = 8 := by
    rw [hhead]; exact h8
  have htapeval : (machine.run (switchTime (a + m)) (startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w := by rw [htape]; exact htp
  refine ⟨congrArg Config.state hC, hhead, htape, hheadval, htapeval, fun i hi => ?_⟩
  have hcell : FixedPairContentMarkerErase.contentTape B x w i =
      FixedContentTagGate.physicalSymbol (Fin.append x w) i.val := by
    unfold FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
    rfl
  rw [htapeval, hcell, hi, hiff.mp htag ⟨7, by decide⟩, he7]

/-! ### The inherited switches and the composed run -/

/-- **The inherited H9 fires inside this machine at `3 * N + 7 + (zeros + 1)`.**  The gate's own
steps counted first, the composed control is G2a's gamma-anchor start at index `18` — G3i's `3`
shifted by the fifteen gate states — on exactly the head and tape G2a's landed `startConfig`
carries, that tape still being the unmarked `contentTape` with cell `7` not yet blank. -/
theorem tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (zeros + 1)) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state.val = 18 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag
  obtain ⟨hs, hhead, htape, hhv, htv, hseven⟩ :=
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      (B := B) x w htag hg
  have hz :
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        zeros = zeros + 1 := rfl
  rw [hz] at hs hhead htape hhv htv hseven
  have hrun := hsuffix (zeros + 1)
  have hstate : (machine.run (switchTime (a + m) + (zeros + 1)) (startConfig B x w)).state =
      inTail
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (zeros + 1)
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)).state := by
    rw [hrun]; rfl
  refine ⟨by rw [hstate, hs]; decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; exact hhead
  · rw [hrun]; exact htape
  · rw [hrun]; exact hhv
  · rw [hrun]; exact htv
  · rw [hrun]; exact hseven

/-- **The inherited H10 fires inside this machine at
`3 * N + 7 + (zeros + 1 + (2 * zeros + 5))`.**  The composed control is G2k's payload-dispatcher
start at index `24` — G3i's `9` shifted by the fifteen gate states — on exactly the head and tape
G2k's landed `startConfig` carries, that tape being the anchor's `markedTape` with cell `7` now
blank: the marker the anchor writes with the composed table's own row. -/
theorem tagged_inherited_anchor_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (zeros + 1 + successTime zeros)) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 24 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag
  obtain ⟨hs, hhead, htape, hhv, htv, hseven⟩ :=
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_switch
      (B := B) x w htag hg
  have hz :
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        zeros = zeros + 1 := rfl
  rw [hz] at hs hhead htape hhv htv hseven
  have hrun := hsuffix (zeros + 1 + successTime zeros)
  have hval : (machine.run (switchTime (a + m) + (zeros + 1 + successTime zeros))
      (startConfig B x w)).state.val =
      15 +
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (zeros + 1 + successTime zeros)
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨by rw [hval, hs], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; exact hhead
  · rw [hrun]; exact htape
  · rw [hrun]; exact hhv
  · rw [hrun]; exact htv
  · rw [hrun]; exact hseven

/-- **The inherited H11 fires inside this machine at
`3 * N + 7 + (zeros + 1 + (2 * zeros + 5) + C)`.**  There is a strict first dispatcher arrival `C`
at or below G2m's deadline, in one of the two success endpoints, and at that time the composed
control is G2p-a's start at index `52`, on exactly the head and tape G2p-a's landed `startConfig`
carries.  `C` is produced, not chosen. -/
theorem tagged_inherited_dispatcher_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ FixedGammaPayloadDispatcherDeadline.deadline (a + m) ∧
      StrictFirstTerminalAt B x w C q ∧
      (q = FixedGammaPayloadDispatcher.qAllZero ∨ q = FixedGammaPayloadDispatcher.qHasOne) ∧
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).state.val = 52 ∧
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag
  obtain ⟨C, q, hle, hfirst, hq, hstate, hhead, htape⟩ :=
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_dispatcher_switch
      (B := B) x w htag hg
  have hz :
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        zeros = zeros + 1 := rfl
  rw [hz] at hstate hhead htape
  have hrun := hsuffix (zeros + 1 + (successTime zeros + C))
  have hval : (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
      (startConfig B x w)).state.val =
      15 +
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (zeros + 1 + (successTime zeros + C))
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨C, q, hle, hfirst, hq, ?_, ?_, ?_⟩
  · rw [hval, hstate]
  · rw [hrun]; exact hhead
  · rw [hrun]; exact htape

/-- **The concrete exact run: the content tag gate, H8, the gamma terminator, H9, the gamma anchor,
H10, the payload dispatcher, H11, the scratch bootstrap, H12, the first and second payload digits,
H13 and H14, the markers, H15, the loop, H16, the decrement, H17 and the countdown, one machine.**
Under G3i's **eight** hypotheses unchanged, after exactly `gateChainClock C (a+m) zeros d v` steps
the composed machine is in its accept, the countdown's `qDone`, on the separator blank `a+m+2+zeros`
with tape `loopTape B x w zeros 0 v`, persisting.  `v` is universally quantified and unsupplied;
persistence is not first arrival of the composed accept. -/
theorem tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := gateChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag
  obtain ⟨he1, he2, he3, -⟩ :=
    terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (gateChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedContentTagGate.machine.seqEmbedRight
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (terminatorChainClock C (a + m) zeros (borrow x w zeros) v)
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) :=
    hsuffix (terminatorChainClock C (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (gateChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, show _ = _ from he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = gateChainClock C (a + m) zeros (borrow x w zeros) v +
      (t - gateChainClock C (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject on a matching tag with no gamma terminator.**  The gate hands over at
`3 * N + 7`, the composed run is in neither verdict before `3 * N + 7 + (N - 7)`, and from that time
on it is in the composed reject — index `146`, not G1's `qReject` at `14` nor G2's at `17` — on the
blank boundary cell `a + m`, over the unchanged content tape: the anchor never runs.  **Not** a
converse; it characterises no parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime (a + m) + FixedContentGammaTerminator.deadline a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime (a + m) + FixedContentGammaTerminator.deadline a m ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) := by
  intro c
  obtain ⟨hnoPre, hleft, -, hsuffix⟩ := handoff_exact x w htag
  obtain ⟨hno, hpost⟩ :=
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.malformed_reject_handoff
      (B := B) x w htag hg
  have hshift : ∀ s,
      (machine.run (switchTime (a + m) + s) c).state =
        inTail
          (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w)).state := by
    intro s; rw [hsuffix s]; rfl
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · by_cases hle : t ≤ switchTime (a + m)
    · exact hnoPre t hle
    · have hgt : switchTime (a + m) ≤ t := Nat.le_of_lt (Nat.lt_of_not_le hle)
      have hlt : t - switchTime (a + m) < FixedContentGammaTerminator.deadline a m := by omega
      obtain ⟨ha, hr⟩ := hno (t - switchTime (a + m)) hlt
      have hst := hshift (t - switchTime (a + m))
      rw [show switchTime (a + m) + (t - switchTime (a + m)) = t by omega] at hst
      refine ⟨fun hcon => ha ?_, fun hcon => hr ?_⟩
      · exact (Function.Injective.eq_iff
          ((FixedContentTagGate.machine.seq_pins
            FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine).2.2.2.2.2.2.2.1)).mp
          (hst.symm.trans hcon)
      · exact (Function.Injective.eq_iff
          ((FixedContentTagGate.machine.seq_pins
            FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine).2.2.2.2.2.2.2.1)).mp
          (hst.symm.trans hcon)
  · obtain ⟨hrj, hhd, htp⟩ := hpost (s - switchTime (a + m)) (by omega)
    have hrun := hsuffix (s - switchTime (a + m))
    rw [show switchTime (a + m) + (s - switchTime (a + m)) = s by omega] at hrun
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
    · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
    · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

/-- **The routed reject on a mismatched tag: the first statement of this chain that assumes the tag
does not match.**  From the gate's length-only deadline `3 * N + 7` on, the composed run is in the
composed reject `146`, on the gate's own `finalConfig` head — its mismatch index, clamped — over the
unchanged content tape; the right block never runs.  Forward direction only, and **not** timed
exactly: the gate first rejects at that mismatch index, which its public API exposes only through
`finalConfig.head`.  **Not** a converse either. -/
theorem mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime (a + m) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w := by
  intro s hs
  obtain ⟨hend, hrej⟩ := gate_reject_arrival (B := B) x w htag
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).head,
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).tape⟩ := by
    have h := FixedContentTagGate.machine.seq_reject_handoff
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentTagGate.startConfig B x w) hrej (s - switchTime (a + m))
    rw [show switchTime (a + m) + (s - switchTime (a + m)) = s by omega] at h
    exact h
  rw [hrun, hend]
  exact ⟨rfl, rfl, rfl⟩

end
  Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
