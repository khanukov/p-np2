import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The trailing content-marker erasure, the content tag gate, the gamma terminator, the gamma anchor,
the payload dispatcher, the scratch bootstrap, the first payload digit, the second payload digit, the
loop markers, the payload loop, the decrement and the countdown as one machine (Part A G3k)

**No new table row.**  `machine` is `FixedPairContentMarkerErase.machine.seq` the whole landed G3j
composite: the marker-erase phase's fixed 4-state, 12-row scan-and-erase on `[0, 4)` and G3j's 147
states on `[4, 151)`, one closed 151-state, 453-row table whose every row is a row of one of those
twelve tables with its target routed.  Write `N = a + m` and `d = borrow x w zeros`.
`pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Eleven executed handoffs.**  H7 — the marker-erase phase into G1's content tag gate — is the newly
executed one, and it has exactly **one** live routed row: `qErase` on `some true`, the marker-erase
table's only row targeting its accept outside the accept's own absorbing three
(`accept_row_unique`), which `seq` retargets to the right block's start `tailStart` at index `4`,
writing `none` and **staying**, in that same transition and at no cost.  That written `none` *is* the
erasure of the trailing content marker: this routed row does not rewrite the symbol it read but
blanks it, so the composed table performs that mutation itself, in the very transition that hands
over.  On the reject side the marker-erase table has exactly **two** rows
targeting its reject — `qErase` on `some false` and on `none`, the malformed-candidate exits —
`reject_rows_unique` proves those two the only ones over all four states and all three symbols once
both verdicts' own absorbing rows are excluded, and
`reject_rows_routed` sends each to the composed reject `150` with the symbol written and the move
unchanged.  Neither is *taken* out of this `startConfig`: `erase_first_arrival` proves the left block
never enters its reject there at any time, so the composed reject is reachable only through the right
block.  The left copies of the two marker-erase verdicts are dead: no composed row targets either
(`table_and_resource_pins`).  H8 (`16 → 19`, the last tag state on `some false`), H9 (`19 → 22`), H10
(`25 → 28`) and H11 (six rows inside `[28, 56)`, all into `56`) to H17 (`137 → 140`) are inherited
from G3j, its indices shifted by four and located by `(inTail q).val = 4 + q.val` with the universal
right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The marker-erase phase has
exactly two absorbing states, `qAccept` and `qReject` — its raw states `2` and `3`, three rows each —
so the landed `seq` routes both and no `mergeAccept` is needed, as for H8, H9 and H10 and unlike H11.
Its strict first arrival *was* already exported in the shape `UniformTM.seq_handoff` consumes: the
landed `strict_first_terminal` gives both halves against the phase's `qAccept` and `qReject`, which
its own landed `table_and_resource_pins` identifies with `machine.accept` and
`machine.reject`, and it takes **no hypothesis at all**, so `erase_first_arrival` only repackages it
at `switchTime N = N + 3` and adds that this time is the phase's own landed `clock`, together with
the never-rejects consequence.  The endpoint is compatible with the right block's start by
construction: G1's `startConfig` is built field-for-field out of the marker-erase `finalConfig`,
which `run_exact` shows *is* the marker-erase run at `switchTime N` for every input, and
`gate_start_at_first_arrival` records that hypothesis-free.  So the switch hands over exactly the head
and tape the right block's own `startConfig` carries — the erased `contentTape`, on the boundary cell
`N`.  The switch time is length-only, neither width- nor path-dependent: it adds a linear prefix to
the composed clock and no new room premise.

**The composed run.**  `handoff_exact` takes **no hypothesis** — the first executed handoff of this
chain that takes none, no tag, no width, no room, no budget: the run out of `startConfig` is in
neither composed verdict at any time up to and including `N + 3` (at the switch time itself the
control is `tailStart`, so the bound is `≤`), is the marker-erase phase's own run routed at every
such time as whole-`Config` equality, at exactly `N + 3` **is** G3j's landed `startConfig B x w`
re-embedded, and every later step is a G3j step.  `handoff_endpoint_pins` reads that switch
configuration back as G1's own `startConfig` projections — the control as `tailStart`, the head and
the whole tape as G1's own — and records that the head is the boundary cell `N`, that the tape is the
`contentTape`, and that every allocated cell from `N` on is blank there, the trailing marker
included.
`tagged_inherited_switch` locates the inherited H8 at `N + 3 + (3 * N + 7)`,
`tagged_inherited_terminator_switch` the inherited H9 at `N + 3 + (3 * N + 7 + (zeros + 1))`,
`tagged_inherited_anchor_switch` the inherited H10 at
`N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5)))`, `tagged_inherited_dispatcher_switch` the
inherited H11 with its `C` produced rather than chosen, and the drained theorem lands the composed
accept `149` at exactly `eraseChainClock C N zeros d v = N + 3 + gateChainClock C N zeros d v` under
G3j's eight hypotheses unchanged.  Two rejecting branches are inherited, both forward direction only.
On a matching tag whose physical suffix holds **no** gamma terminator the whole prefix hands over and
`malformed_reject_handoff` lands the composed reject `150` from `N + 3 + (3 * N + 7 + (N - 7))` on.
On a **mismatched** tag `mismatched_tag_reject_handoff` lands it from `N + 3 + (3 * N + 7)` on, the
gamma blocks never running; that branch is deliberately **not** timed exactly, for the reason G3j
records — on a nonempty content the gate's own first rejection is at `3 * N + j` for its mismatch
cell `j`, which this chain does not derive from `tagMatches (Fin.append x w) = false`, the value of
`FixedContentTagGate.finalConfig`'s head being the only public trace of the `badIndex` that defines
it — and the composed run may already be in the composed reject before the time stated.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the six
handoffs before H7 remain proof-level identifications (the marker-erase `startConfig` retags the
actual origin-alignment `finalConfig`, which `handoff_pins` records hypothesis-free), no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  No **first
arrival** of the composed accept: the arrivals proved are the marker-erase phase's and, as a
hypothesis, the dispatcher's, each inside its own block.  The **fence** (all twelve tables are
uncapped); every **converse**, so neither composed reject implies anything about the input; a
**footprint** theorem; and the pnp4 bridge, not built here, the standalone phases' pnp4 semantics
being unchanged, nor is it proved that the cubic budget still dominates the composed clock.  The
composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior
endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or `ContentVerifierBridge` is stated.  The table is fixed and complete but
not claimed state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedContentGammaAnchor (successTime markedTape)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (gateChainClock)

/-- The right block: the machine of the landed G3j composite, named once so that the statements below
stay readable.  An `abbrev`, hence reducible, so every pin below is a pin on that machine itself;
`table_and_resource_pins` spells the identification out. -/
abbrev tailMachine : UniformTM :=
  FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- The right block's own start configuration: G3j's landed `startConfig`, named once.  Also an
`abbrev`; `gate_start_at_first_arrival` identifies it with what this switch hands over. -/
abbrev tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
    B x w

/-- The composed machine: the marker-erase phase, then G3j's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM := FixedPairContentMarkerErase.machine.seq tailMachine

/-- A marker-erase state in the composed control, at its own index. -/
def inErase (q : Fin FixedPairContentMarkerErase.eraseStateCount) : Fin machine.stateCount :=
  FixedPairContentMarkerErase.machine.seqLeft tailMachine q

/-- A G3j state in the composed control, shifted past the four marker-erase states. -/
def inTail (q : Fin tailMachine.stateCount) : Fin machine.stateCount :=
  FixedPairContentMarkerErase.machine.seqRight tailMachine q

/-- The routed target of a marker-erase row: `qAccept` becomes G3j's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedPairContentMarkerErase.eraseStateCount) : Fin machine.stateCount :=
  FixedPairContentMarkerErase.machine.seqRoute tailMachine q

/-- G3j's start in the composed control, index `4`: the target of the one live routed row. -/
def tailStart : Fin machine.stateCount := inTail tailMachine.start

/-- The marker-erase phase's own `startConfig` — the retagged *actual* origin-alignment endpoint —
routed into the composed control.  Still a phase-local retag, not `initialConfig` on a raw pair
input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedPairContentMarkerErase.machine.seqEmbedRouted tailMachine
    (FixedPairContentMarkerErase.startConfig B x w)

/-- The marker-erase phase's strict first arrival, for every input: `N + 1` rightward steps to walk
the content and its trailing marker and stop on the first physical blank, one step left back onto the
marker, and one more to check it is `some true`, erase it and accept. -/
def switchTime (N : Nat) : Nat := N + 3

/-- Exact cost of the marker-erase phase followed by the whole of G3j: the phase's length-only first
arrival `N + 3`, plus the tag gate's length-only `3 * N + 7`, plus the terminator's width-only
`zeros + 1`, plus the anchor's width-only `2 * zeros + 5`, plus the dispatcher's input-dependent `C`,
plus G3e's `bootChainClock`.  All five handoffs cost nothing. -/
def eraseChainClock (C N zeros d v : Nat) : Nat := switchTime N + gateChainClock C N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the composition itself spelled out, the state and row counts of both
blocks and of the whole, the marker-erase start and verdicts with their indices, G3j's three
distinguished states with theirs, the composed distinguished states with theirs, the block injections
with their offsets and disjointness, `tailStart` at `4`, the three routing cases, every left row as
the routed marker-erase row, every right row as the G3j row, the public step against the composed raw
table, the one live routed row — `qErase` on `some true`, writing `none` and staying — the two dead
verdict copies' three rows each, and that no **left-block** row targets either dead copy.  The two
injective, disjoint block maps have domain sizes `4` and `147`, summing to the composed state count
`151`, so they cover every state.  Thus the two block equations account for every composed row, and
block disjointness excludes right-block targets from the dead left copies as well.  The right-block
equation transports every G3j row.  Deciding rows of a table this deep unfolds the whole
twelve-block composition, so the kernel needs a raised recursion budget here. -/
theorem table_and_resource_pins :
    machine =
        FixedPairContentMarkerErase.machine.seq
          FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      tailMachine =
        FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      machine.stateCount = 151 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 453 ∧
      FixedPairContentMarkerErase.machine.stateCount = 4 ∧ tailMachine.stateCount = 147 ∧
      FixedPairContentMarkerErase.machine.start.val = 0 ∧
      FixedPairContentMarkerErase.machine.accept.val = 2 ∧
      FixedPairContentMarkerErase.machine.reject.val = 3 ∧
      FixedPairContentMarkerErase.qErase.val = 1 ∧
      tailMachine.start.val = 0 ∧ tailMachine.accept.val = 145 ∧ tailMachine.reject.val = 146 ∧
      machine.start = route FixedPairContentMarkerErase.machine.start ∧
      machine.start = inErase FixedPairContentMarkerErase.machine.start ∧
      machine.accept = inTail tailMachine.accept ∧ machine.reject = inTail tailMachine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 149 ∧ machine.reject.val = 150 ∧
      (∀ q, (inErase q).val = q.val) ∧ (∀ q, (inErase q).val < 4) ∧
      (∀ q, (inTail q).val = 4 + q.val) ∧ (∀ q, 4 ≤ (inTail q).val) ∧
      Function.Injective inErase ∧ Function.Injective inTail ∧
      (∀ p q, inErase p ≠ inTail q) ∧
      tailStart = inTail tailMachine.start ∧ tailStart.val = 4 ∧
      route FixedPairContentMarkerErase.machine.accept = tailStart ∧
      route FixedPairContentMarkerErase.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedPairContentMarkerErase.machine.accept →
        q ≠ FixedPairContentMarkerErase.machine.reject → route q = inErase q) ∧
      (∀ q s, machine.step (inErase q) s =
        (route (FixedPairContentMarkerErase.machine.step q s).1,
          (FixedPairContentMarkerErase.machine.step q s).2.1,
          (FixedPairContentMarkerErase.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1, (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inErase FixedPairContentMarkerErase.qErase) (some true) =
        (tailStart, none, .stay) ∧
      (∀ s, machine.step (inErase FixedPairContentMarkerErase.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inErase FixedPairContentMarkerErase.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inErase q) s).1 ≠
          inErase FixedPairContentMarkerErase.machine.accept ∧
        (machine.step (inErase q) s).1 ≠
          inErase FixedPairContentMarkerErase.machine.reject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedPairContentMarkerErase.machine.seq_pins tailMachine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_, rfl,
    rfl, by decide, by decide, by decide, fun _ => rfl, fun q => q.isLt, fun _ => rfl,
    fun _ => Nat.le_add_right _ _, hli, hri, hne, rfl, by decide, hra, hrr, hrw,
    fun q s => FixedPairContentMarkerErase.machine.seq_step_left tailMachine q s,
    fun q s => FixedPairContentMarkerErase.machine.seq_step_right tailMachine q s,
    fun q s => FixedPairContentMarkerErase.machine.seq_step_eq_rawStep tailMachine q s,
    by decide, ?_, ?_, by decide⟩
  · exact hrw FixedPairContentMarkerErase.machine.start (by decide) (by decide)
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide

/-- **The marker-erase table has exactly one row targeting its accept.**  Over all four states and
all three symbols, with the accept's own absorbing three excluded, a target of
`FixedPairContentMarkerErase.machine.accept` forces `qErase` on `some true`.  So H7 has exactly one
live routed row.  This quantifies over the marker-erase rows alone and says nothing about the
composed table as a whole: the inherited right block keeps its own rows, and the only rows this
excludes are the dead left accept copy's own three — the reject copy's are *not* excluded here —
which `seq` routes to `tailStart` and no composed row ever enters. -/
theorem accept_row_unique (q : Fin FixedPairContentMarkerErase.eraseStateCount) (s : Option Bool)
    (hq : q ≠ FixedPairContentMarkerErase.machine.accept)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.accept) :
    q = FixedPairContentMarkerErase.qErase ∧ q.val = 1 ∧ s = some true := by
  revert h
  revert hq
  revert s
  revert q
  decide

/-- **The marker-erase table has exactly two rows targeting its reject.**  Over all four states and
all three symbols, with both verdicts' own absorbing rows excluded, a target of
`FixedPairContentMarkerErase.machine.reject` forces `qErase` on `some false` or on `none` — the two
malformed-candidate exits.  Unlike the tag gate's reject, whose live rows G3j could only quantify
over, these two are the whole list, and unlike the terminator's single one they are two.  This is a
statement about the fixed table, not about reachability: `erase_first_arrival` proves neither row is
ever taken out of this slice's `startConfig`. -/
theorem reject_rows_unique (q : Fin FixedPairContentMarkerErase.eraseStateCount) (s : Option Bool)
    (ha : q ≠ FixedPairContentMarkerErase.machine.accept)
    (hq : q ≠ FixedPairContentMarkerErase.machine.reject)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.reject) :
    q = FixedPairContentMarkerErase.qErase ∧ q.val = 1 ∧ (s = some false ∨ s = none) := by
  revert h
  revert hq
  revert ha
  revert s
  revert q
  decide

/-- **Every row targeting the marker-erase reject is routed to the composed reject `150`.**  `seq`
sends each of the two to the composed reject, with the symbol written and the move unchanged.  The
two verdicts' own rows are excluded: both of their left copies are dead. -/
theorem reject_rows_routed (q : Fin FixedPairContentMarkerErase.eraseStateCount) (s : Option Bool)
    (ha : q ≠ FixedPairContentMarkerErase.machine.accept)
    (hq : q ≠ FixedPairContentMarkerErase.machine.reject)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.reject) :
    machine.step (inErase q) s =
      (machine.reject, (FixedPairContentMarkerErase.machine.rawStep q s).2.1,
        (FixedPairContentMarkerErase.machine.rawStep q s).2.2) := by
  have hstep : FixedPairContentMarkerErase.machine.step q s =
      FixedPairContentMarkerErase.machine.rawStep q s :=
    FixedPairContentMarkerErase.machine.step_of_ne ha hq s
  have hleft : machine.step (inErase q) s =
      (route (FixedPairContentMarkerErase.machine.step q s).1,
        (FixedPairContentMarkerErase.machine.step q s).2.1,
        (FixedPairContentMarkerErase.machine.step q s).2.2) :=
    FixedPairContentMarkerErase.machine.seq_step_left tailMachine q s
  rw [hleft, hstep, h]
  rfl

/-- **The start is the retagged actual origin-alignment endpoint, not a raw input, and this needs no
hypothesis.**  The origin-alignment phase's run at its own clock is its `finalConfig`, on the origin
cell `0` over the aligned tape; the marker-erase `startConfig` is that configuration retagged; and
this slice's `startConfig` is *that* one routed into the composed control — the same head and tape,
the composed start `0` as control.  This is handoff **H6**, recorded as an identification and not
executed by this table.  No `initialConfig` and no raw pair input appears, and neither retag costs a
step. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginAlignment.machine.run (FixedPairOriginAlignment.clock a m)
      (FixedPairOriginAlignment.startConfig B x w)
    let p := FixedPairContentMarkerErase.startConfig B x w
    let c := startConfig B x w
    g = FixedPairOriginAlignment.finalConfig B x w ∧
      g.state = FixedPairOriginAlignment.qAccept ∧ p = FixedPairContentMarkerErase.retag g ∧
      p.state = FixedPairContentMarkerErase.machine.start ∧ p.head = g.head ∧ p.tape = g.tape ∧
      c = FixedPairContentMarkerErase.machine.seqEmbedRouted tailMachine p ∧
      c.state = machine.start ∧ c.state = inErase FixedPairContentMarkerErase.machine.start ∧
      c.head = g.head ∧ c.tape = g.tape ∧ c.head.val = 0 ∧
      c.tape = FixedPairOriginAlignment.alignedTape B x w := by
  obtain ⟨hfin, hst, hretag, -, hhead, htape⟩ :=
    FixedPairContentMarkerErase.handoff_exact (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedPairContentMarkerErase.machine.seq_pins tailMachine
  refine ⟨hfin, hst, hretag, rfl, hhead, htape, rfl, rfl,
    hrw FixedPairContentMarkerErase.machine.start (by decide) (by decide), hhead, htape, ?_, ?_⟩
  · rw [show (startConfig B x w).head = _ from hhead, hfin]
    rfl
  · rw [show (startConfig B x w).tape = _ from htape, hfin]
    rfl

/-- The chained clock, pinned: G3j's sum prefixed by the marker-erase phase's length-only first
arrival `N + 3`, that arrival identified with the phase's own landed `clock`, the tag gate's
length-only arrival and its own deadline, the two width-only arrivals G3i and G3h contribute, and on
`2 ≤ zeros` its full expansion.  `C` has no closed form in `N`. -/
theorem clock_pins (C N zeros d v : Nat) :
    eraseChainClock C N zeros d v = switchTime N + gateChainClock C N zeros d v ∧
      switchTime N = N + 3 ∧
      (∀ a m : Nat, switchTime (a + m) = FixedPairContentMarkerErase.clock a m) ∧
      (∀ z : Nat,
        FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          z = 3 * z + 7) ∧
      (∀ a m : Nat, FixedContentTagGate.deadline a m = 3 * (a + m) + 7) ∧
      (∀ z : Nat,
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          z = z + 1) ∧
      (∀ z : Nat, successTime z = 2 * z + 5) ∧
      eraseChainClock C N zeros d v =
        N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + (C + bootChainClock N zeros d v)))) ∧
      (2 ≤ zeros → eraseChainClock C N zeros d v =
        N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + (C + (2 * N - 11 - zeros +
          (2 * N + zeros - 6 + (2 * N - 7 + (zeros + 7 +
            (totalClock N zeros + composedClock N zeros d v)))))))))) := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl,
    fun hz => ?_⟩
  show switchTime N + gateChainClock C N zeros d v = _
  rw [(FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    C N zeros d v).2.2.2.2.2.2 hz]
  rfl

/-! ### The marker-erase phase's arrival, in the shape the composition consumes -/

/-- **The marker-erase phase's strict first arrival, for every input and with no hypothesis.**  It is
in neither verdict at every time before `switchTime N = N + 3`, at that time its run **is** its
`finalConfig` and its control its accept, that time **equals** its own landed `clock`, and it is
never in its reject at any time at all.  The first three conjuncts repackage the landed
`strict_first_terminal` and `run_exact`, which state the two verdicts as the phase's own `qAccept`
and `qReject` — its landed `table_and_resource_pins` identifies those with `machine.accept` and
`machine.reject`; the last adds the landed `post_clock_absorption`, which keeps the accepting
endpoint unchanged from the clock on. -/
theorem erase_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime (a + m) →
        (FixedPairContentMarkerErase.machine.run t
            (FixedPairContentMarkerErase.startConfig B x w)).state ≠
          FixedPairContentMarkerErase.machine.accept ∧
        (FixedPairContentMarkerErase.machine.run t
            (FixedPairContentMarkerErase.startConfig B x w)).state ≠
          FixedPairContentMarkerErase.machine.reject) ∧
      FixedPairContentMarkerErase.machine.run (switchTime (a + m))
          (FixedPairContentMarkerErase.startConfig B x w) =
        FixedPairContentMarkerErase.finalConfig B x w ∧
      (FixedPairContentMarkerErase.machine.run (switchTime (a + m))
          (FixedPairContentMarkerErase.startConfig B x w)).state =
        FixedPairContentMarkerErase.machine.accept ∧
      switchTime (a + m) = FixedPairContentMarkerErase.clock a m ∧
      (∀ t, (FixedPairContentMarkerErase.machine.run t
          (FixedPairContentMarkerErase.startConfig B x w)).state ≠
        FixedPairContentMarkerErase.machine.reject) := by
  obtain ⟨hno, hacc⟩ := FixedPairContentMarkerErase.strict_first_terminal (B := B) x w
  have hrun : FixedPairContentMarkerErase.machine.run (switchTime (a + m))
      (FixedPairContentMarkerErase.startConfig B x w) =
      FixedPairContentMarkerErase.finalConfig B x w :=
    FixedPairContentMarkerErase.run_exact B x w
  refine ⟨hno, hrun, hacc, rfl, fun t => ?_⟩
  by_cases ht : t < switchTime (a + m)
  · exact (hno t ht).2
  · have hnlt : ¬ t < a + m + 3 := ht
    have hle : FixedPairContentMarkerErase.clock a m ≤ t := by
      simp only [FixedPairContentMarkerErase.clock]
      omega
    rw [show t = FixedPairContentMarkerErase.clock a m +
        (t - FixedPairContentMarkerErase.clock a m) by omega,
      FixedPairContentMarkerErase.post_clock_absorption x w]
    exact FixedPairContentMarkerErase.machine.accept_ne_reject

/-- G1's `startConfig` is the marker-erase run at `switchTime N`, field for field — and this holds for
**every** input, because the phase's `run_exact` is unconditional.  This is the semantic dependency H7
has to respect; it executes nothing.  The last conjunct is the form `UniformTM.seq_handoff` consumes:
the right block's start configuration *is* G3j's start on the head and tape the marker-erase phase
leaves. -/
theorem gate_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairContentMarkerErase.machine.run (switchTime (a + m))
      (FixedPairContentMarkerErase.startConfig B x w)
    g = FixedPairContentMarkerErase.finalConfig B x w ∧
      (FixedContentTagGate.startConfig B x w).state = FixedContentTagGate.machine.start ∧
      (FixedContentTagGate.startConfig B x w).head = g.head ∧
      (FixedContentTagGate.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show FixedPairContentMarkerErase.machine.run (switchTime (a + m))
      (FixedPairContentMarkerErase.startConfig B x w) =
      FixedPairContentMarkerErase.finalConfig B x w from
    FixedPairContentMarkerErase.run_exact B x w]
  exact ⟨rfl, rfl, rfl, rfl, Config.ext_parts rfl rfl rfl⟩

/-! ### The executed handoff -/

/-- **H7 fires when the marker-erase phase erases the trailing marker, and it costs nothing.**  With
**no hypothesis** — no tag, no width, no room, no budget — the run out of `startConfig` is in neither
composed verdict at any time up to and including `N + 3` (at the switch time itself the control is
`tailStart`, so the bound is `≤`), is the marker-erase phase's own run routed at every such time —
same head and whole tape — at exactly `N + 3` **is** G3j's landed `startConfig B x w` re-embedded, and
runs G3j on from there. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := startConfig B x w
    (∀ t, t ≤ switchTime (a + m) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime (a + m) → machine.run t c =
        FixedPairContentMarkerErase.machine.seqEmbedRouted tailMachine
          (FixedPairContentMarkerErase.machine.run t
            (FixedPairContentMarkerErase.startConfig B x w))) ∧
      machine.run (switchTime (a + m)) c =
        FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
      (∀ s, machine.run (switchTime (a + m) + s) c =
        FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine
          (tailMachine.run s (tailStartConfig B x w))) := by
  intro c
  obtain ⟨hno, hend, hacc, -, -⟩ := erase_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, hcfg⟩ := gate_start_at_first_arrival (B := B) x w
  have hwork : ∀ t, t < switchTime (a + m) →
      (FixedPairContentMarkerErase.machine.run t
        (FixedPairContentMarkerErase.startConfig B x w)).state ≠
        FixedPairContentMarkerErase.machine.accept := fun t ht => (hno t ht).1
  have hleft :=
    FixedPairContentMarkerErase.machine.seq_run_left tailMachine
      (FixedPairContentMarkerErase.startConfig B x w) hwork
  have hsuffix : ∀ s, machine.run (switchTime (a + m) + s) c =
      FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedPairContentMarkerErase.machine.seq_handoff tailMachine
      (FixedPairContentMarkerErase.startConfig B x w) hwork hacc s
  have hC : machine.run (switchTime (a + m)) c =
      FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine (tailStartConfig B x w) :=
    hsuffix 0
  have hCs : (machine.run (switchTime (a + m)) c).state = tailStart := by
    rw [hC]; rfl
  have hCa : (machine.run (switchTime (a + m)) c).state ≠ machine.accept := by
    rw [hCs]; decide
  have hCr : (machine.run (switchTime (a + m)) c).state ≠ machine.reject := by
    rw [hCs]; decide
  exact ⟨UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩

/-- **What the switch hands over is exactly what G1 reads.**  At the marker-erase phase's first
arrival `N + 3`: the composed control is G3j's start `4`, the composed head and whole tape are *the
same* projections G3j's own `startConfig` carries and, field for field, the ones G1's own
`startConfig` carries; the head is the boundary cell `N`; the tape is the `contentTape`; and every
allocated cell from `N` on is blank there, so the trailing content marker really is gone — erased by
the routed row itself. -/
theorem handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (a + m)) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedContentTagGate.startConfig B x w).head ∧
      e.tape = (FixedContentTagGate.startConfig B x w).tape ∧
      e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m ≤ i.val → e.tape i = none) := by
  obtain ⟨-, -, hC, -⟩ := handoff_exact (B := B) x w
  obtain ⟨-, -, -, -, -, htp, -, -, -, hblank⟩ :=
    FixedPairContentMarkerErase.final_fields_and_layout (B := B) x w
  rw [htp] at hblank
  have hhead : (machine.run (switchTime (a + m)) (startConfig B x w)).head =
      (tailStartConfig B x w).head := congrArg Config.head hC
  have htape : (machine.run (switchTime (a + m)) (startConfig B x w)).tape =
      (tailStartConfig B x w).tape := congrArg Config.tape hC
  refine ⟨congrArg Config.state hC, hhead, htape, hhead, htape, ?_, ?_, fun i hi => ?_⟩
  · rw [hhead]; rfl
  · rw [htape]; rfl
  · rw [htape]; exact hblank i hi

/-! ### The inherited switches and the composed run -/

-- G3j's own start index, reduced once here so that the four inherited-switch theorems below can
-- shift it by four without each paying for the reduction.
private theorem tail_start_val : FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailStart.val = 15 := by decide


/-- **The inherited H8 fires inside this machine at `N + 3 + (3 * N + 7)`.**  The marker-erase
phase's own steps counted first, the composed control is G2's gamma-terminator start at index `19` —
G3j's `15` shifted by the four marker-erase states — on exactly the head and tape G2's landed
`startConfig` carries, that tape still being the `contentTape` with the tag's own last bit
`some false` on cell `7`. -/
theorem tagged_inherited_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7)) (startConfig B x w)
    let p := FixedContentGammaTerminator.startConfig B x w
    e.state.val = 19 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = some false) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hs, hhead, htape, hhv, htv, hseven⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      (B := B) x w htag
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  rw [hz] at hs hhead htape hhv htv hseven
  have hrun := hsuffix (3 * (a + m) + 7)
  have hsv : (tailMachine.run (3 * (a + m) + 7) (tailStartConfig B x w)).state.val = 15 := by
    rw [hs]
    exact tail_start_val
  have hval : (machine.run (switchTime (a + m) + (3 * (a + m) + 7)) (startConfig B x w)).state.val =
      4 + (tailMachine.run (3 * (a + m) + 7) (tailStartConfig B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨by rw [hval, hsv], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_head, hhead]
  · rw [hrun, UniformTM.seqEmbedRight_tape, htape]
  · rw [hrun, UniformTM.seqEmbedRight_head, hhv]
  · rw [hrun, UniformTM.seqEmbedRight_tape, htv]
  · intro i hi
    rw [hrun, UniformTM.seqEmbedRight_tape, hseven i hi]

/-- **The inherited H9 fires inside this machine at `N + 3 + (3 * N + 7 + (zeros + 1))`.**  The
composed control is G2a's gamma-anchor start at index `22` — G3j's `18` shifted by the four
marker-erase states — on exactly the head and tape G2a's landed `startConfig` carries, that tape
still being the unmarked `contentTape` with cell `7` not yet blank. -/
theorem tagged_inherited_terminator_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7 + (zeros + 1))) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state.val = 22 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hs, hhead, htape, hhv, htv, hseven⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_switch
      (B := B) x w htag hg
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  rw [hz] at hs hhead htape hhv htv hseven
  have hrun := hsuffix (3 * (a + m) + 7 + (zeros + 1))
  have hval : (machine.run (switchTime (a + m) + (3 * (a + m) + 7 + (zeros + 1)))
      (startConfig B x w)).state.val =
      4 + (tailMachine.run (3 * (a + m) + 7 + (zeros + 1)) (tailStartConfig B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨by rw [hval, hs], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhead
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htape
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhv
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htv
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact hseven

/-- **The inherited H10 fires inside this machine at
`N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5)))`.**  The composed control is G2k's
payload-dispatcher start at index `28` — G3j's `24` shifted by the four marker-erase states — on
exactly the head and tape G2k's landed `startConfig` carries, that tape being the anchor's
`markedTape` with cell `7` now blank: the marker the anchor writes with the composed table's own
row. -/
theorem tagged_inherited_anchor_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7 + (zeros + 1 + successTime zeros)))
      (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 28 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hs, hhead, htape, hhv, htv, hseven⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_anchor_switch
      (B := B) x w htag hg
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  rw [hz] at hs hhead htape hhv htv hseven
  have hrun := hsuffix (3 * (a + m) + 7 + (zeros + 1 + successTime zeros))
  have hval : (machine.run (switchTime (a + m) +
      (3 * (a + m) + 7 + (zeros + 1 + successTime zeros))) (startConfig B x w)).state.val =
      4 + (tailMachine.run (3 * (a + m) + 7 + (zeros + 1 + successTime zeros))
        (tailStartConfig B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨by rw [hval, hs], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhead
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htape
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhv
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htv
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact hseven

/-- **The inherited H11 fires inside this machine at
`N + 3 + (3 * N + 7 + (zeros + 1 + (2 * zeros + 5 + C)))`.**  There is a strict first dispatcher
arrival `C` at or below G2m's deadline, in one of the two success endpoints, and at that time the
composed control is G2p-a's start at index `56` — G3j's `52` shifted by the four marker-erase states
— on exactly the head and tape G2p-a's landed `startConfig` carries.  `C` is produced, not
chosen. -/
theorem tagged_inherited_dispatcher_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ FixedGammaPayloadDispatcherDeadline.deadline (a + m) ∧
      StrictFirstTerminalAt B x w C q ∧
      (q = FixedGammaPayloadDispatcher.qAllZero ∨ q = FixedGammaPayloadDispatcher.qHasOne) ∧
      (machine.run (switchTime (a + m) +
          (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C))))
        (startConfig B x w)).state.val = 56 ∧
      (machine.run (switchTime (a + m) +
          (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C))))
        (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (switchTime (a + m) +
          (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C))))
        (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨C, q, hle, hfirst, hq, hstate, hhead, htape⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_dispatcher_switch
      (B := B) x w htag hg
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  rw [hz] at hstate hhead htape
  have hrun := hsuffix (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C)))
  have hval : (machine.run (switchTime (a + m) +
      (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C))))
      (startConfig B x w)).state.val =
      4 + (tailMachine.run (3 * (a + m) + 7 + (zeros + 1 + (successTime zeros + C)))
        (tailStartConfig B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨C, q, hle, hfirst, hq, ?_, ?_, ?_⟩
  · rw [hval, hstate]
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhead
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htape

/-- **The concrete exact run: the marker erasure, H7, the content tag gate, H8, the gamma terminator,
H9, the gamma anchor, H10, the payload dispatcher, H11, the scratch bootstrap, H12, the first and
second payload digits, H13 and H14, the markers, H15, the loop, H16, the decrement, H17 and the
countdown, one machine.**  Under G3j's **eight** hypotheses unchanged, after exactly
`eraseChainClock C (a+m) zeros d v` steps the composed machine is in its accept, the countdown's
`qDone`, on the separator blank `a+m+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting.  `v`
is universally quantified and unsupplied; persistence is not first arrival of the composed
accept. -/
theorem marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := eraseChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (eraseChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine
        (tailMachine.run (gateChainClock C (a + m) zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) :=
    hsuffix (gateChainClock C (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (eraseChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = eraseChainClock C (a + m) zeros (borrow x w zeros) v +
      (t - eraseChainClock C (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject on a matching tag with no gamma terminator.**  The marker-erase phase hands
over at `N + 3` and the gate at `3 * N + 7` after that, the composed run is in neither verdict before
`N + 3 + (3 * N + 7 + (N - 7))`, and from that time on it is in the composed reject — index `150`, not
the marker-erase `qReject` at `3`, nor G1's at `18`, nor G2's at `21` — on the blank boundary cell
`a + m`, over the `contentTape`: the anchor never runs.  **Not** a converse; it characterises no
parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime (a + m) +
          (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime (a + m) + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) := by
  intro c
  obtain ⟨hnoPre, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hno, hpost⟩ :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.malformed_reject_handoff
      (B := B) x w htag hg
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  rw [hz] at hno hpost
  have hshift : ∀ s, (machine.run (switchTime (a + m) + s) c).state =
      inTail (tailMachine.run s (tailStartConfig B x w)).state := by
    intro s; rw [hsuffix s]; rfl
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · by_cases hle : t ≤ switchTime (a + m)
    · exact hnoPre t hle
    · have hgt : switchTime (a + m) ≤ t := Nat.le_of_lt (Nat.lt_of_not_le hle)
      have hlt : t - switchTime (a + m) <
          3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m := by omega
      obtain ⟨ha, hr⟩ := hno (t - switchTime (a + m)) hlt
      have hst := hshift (t - switchTime (a + m))
      rw [show switchTime (a + m) + (t - switchTime (a + m)) = t by omega] at hst
      refine ⟨fun hcon => ha ?_, fun hcon => hr ?_⟩
      · exact (Function.Injective.eq_iff
          ((FixedPairContentMarkerErase.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
      · exact (Function.Injective.eq_iff
          ((FixedPairContentMarkerErase.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
  · obtain ⟨hrj, hhd, htp⟩ := hpost (s - switchTime (a + m)) (by omega)
    have hrun := hsuffix (s - switchTime (a + m))
    rw [show switchTime (a + m) + (s - switchTime (a + m)) = s by omega] at hrun
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
    · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
    · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

/-- **The routed reject on a mismatched tag.**  From `N + 3 + (3 * N + 7)` on — the marker-erase
phase's arrival plus the gate's length-only deadline — the composed run is in the composed reject
`150`, on the gate's own `finalConfig` head, its mismatch cell clamped to `N`, over the `contentTape`;
the gamma blocks never run.  Forward direction only, and **not** timed exactly: this time is the
gate's deadline, not its first rejection, so the composed run may already be in the composed reject
strictly earlier, and nothing here says when.  On a nonempty content the gate first rejects at
`3 * N + j` for its mismatch cell `j`, which this slice does not derive from
`tagMatches (Fin.append x w) = false`; `FixedContentTagGate.finalConfig`'s head is the only public
trace of the `badIndex` that defines it.  **Not** a converse either. -/
theorem mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime (a + m) + (3 * (a + m) + 7) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w := by
  intro s hs
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  have hz :
      FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
        (a + m) = 3 * (a + m) + 7 := rfl
  have htail :=
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.mismatched_tag_reject_handoff
      (B := B) x w htag
  rw [hz] at htail
  obtain ⟨hrj, hhd, htp⟩ := htail (s - switchTime (a + m)) (by omega)
  have hrun := hsuffix (s - switchTime (a + m))
  rw [show switchTime (a + m) + (s - switchTime (a + m)) = s by omega] at hrun
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

end
  Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
