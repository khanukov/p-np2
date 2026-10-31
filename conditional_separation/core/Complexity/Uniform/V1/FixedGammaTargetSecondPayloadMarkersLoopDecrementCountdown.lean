import Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown

/-!
# The second payload digit, the loop markers, the payload loop, the decrement and the countdown as
one machine (Part A G3a)

**No new table row.**  `machine` is `FixedGammaTargetSecondPayload.machine.seq
FixedGammaTargetMarkersLoopDecrementCountdown.machine`: G2p-c's 14-state, 42-row second-payload
table on the left block `[0, 14)` and the whole landed G2z 54-state composite on the right block
`[14, 68)` — inside it G2p-d's marker preamble at `[14, 28)`, G2p-d's payload round at `[28, 50)`,
G2q's decrement at `[50, 57)` and G2s-a's countdown at `[57, 68)` — one closed 68-state, 204-row
table whose every row is a row of one of those five tables with its target routed.  Write
`N = a + m` and `d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Four executed handoffs.**  H14 is the newly executed one, and unlike H15 it has exactly **one**
live routed row: `qScanLeft` on `none` is the only row out of a *working* second-payload state that
targets that machine's own absorbing `qDone`, and `seq` routes it to the tail's start — G2z's
composed start at index `14` — in that same transition, on that cell, with the tape G2p-c leaves, at
no cost.  The three `qDone` self-rows are routed too, but that state stays dead: no routed row and
no start targets it.  H15 (four routed rows into `28`, of which `2 ≤ zeros` reaches only `qClearB`
at `23` and `qBackB` at `24`), H16 (`47 → 50`) and H17 (`54 → 57`) are inherited unchanged from G2z,
located here by composed index and carried by the universal right-block row equation, which
transports every G2z row verbatim.  Until now H14 was a proof-level retag at its
length-only deadline `deadline N = 2 * N`; a running composed machine switches at G2p-c's **first
arrival**, so `handoff_exact` rests on `second_payload_strict`.

No new first-arrival theorem is needed: G2p-c already carries arrival (`second_payload_exact`),
minimality (`second_payload_strict`) and the deadline cover (`exactClock_le_deadline`) at every
decoded width, and `UniformTM.run_accept_of_le` identifies the run at the first arrival with the run
at `deadline N` — the very run G2p-d's marker `startConfig`, and through it G2z's, retags.

**Every decoded width.**  `handoff_exact` is the `2 ≤ zeros` branch, whose first arrival is
`exactClock N zeros = 2 * N - 7`; that is the only branch an *accepted parsed target* can reach,
since `3 ≤ pr.2.n` forces `2 ≤ gammaZeros pr.2.n`, and inside it G2p-c's endpoint is extensional in
its three source shapes — physical source `10 + zeros < N`, source address on the boundary blank
`10 + zeros = N`, first payload cell already on the boundary `9 + zeros = N` — so all three hand the
same configuration over.  The two degenerate widths are outside any accepted target but not outside
this table: `zero_width_handoff` (first arrival `3`) and `width_one_handoff` (first arrival `5`,
G2p-b's weaker room) state the same switch on the tape G2p-c leaves unchanged there, and nothing
downstream is claimed for them.

`handoff_exact`: out of `startConfig` — G2p-c's own, hence still the retagged *actual* G2p-b
first-payload endpoint — the composed run is G2p-c's run up to
`T = FixedGammaTargetSecondPayload.exactClock N zeros`, is in neither composed verdict before `T`,
at exactly `T` **is** G2z's landed `startConfig B x w` re-embedded (its head and whole tape), and
every later step is a G2z step.  Its room premise is G2p-c's own
`a + m + 3 < tapeLength (pairLength a m) B`, which is `room_iff`'s `2 ≤ a + B` on both sides of the
switch, so it simulates the tail even where the tail would later lack room.
`second_payload_markers_loop_decrement_countdown_drained`: at exactly
`secondChainClock N zeros d v = FixedGammaTargetSecondPayload.exactClock N zeros +
markersChainClock N zeros d v` the composed machine is in its accept — the countdown's `qDone` — on
the separator blank `N + 2 + zeros` with the register cleared, `v` marks laid and blanks beyond,
persisting.  Its **seven** hypotheses are exactly G2u's, G2y's and G2z's; G2p-c's room is *derived*
inside the proof.  `malformed_reject_handoff` transports G2p-c's own exact malformed endpoint: a
matching tag with no decoded width rejects in one step and the composed control is the composed
reject — index `67` — from then on.  It is stated in the forward direction only; nothing says the
composed reject implies a malformed gamma, and it characterises no parsed target.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
thirteen handoffs before H14 remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `secondChainClock` is the first time it is entered, since G2s-a and G2u prove
no first arrival for `qDone`; the first arrival proved here is *G2p-c's*, inside the left block.
The **fence**: all five tables are uncapped, hence so is this one; an oversized register runs
`qRunEnd` off the tape and sticks, a timeout and neither verdict.  Every **converse**, a
**footprint** theorem — so every room premise is sufficient and used, never shown necessary — and
the pnp4 bridge (taken in
`ContentFixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownBridge`).  The composed `accept`
is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior endpoint is
neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin`
or `UniformP` is stated.  The table is fixed and complete but not claimed state-minimal. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

/-- The composed machine: G2p-c's second-payload table, then G2z's whole marker-loop composite, as
one closed table.  No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTargetSecondPayload.machine.seq
    FixedGammaTargetMarkersLoopDecrementCountdown.machine

/-- A second-payload state in the composed control, at its own index. -/
def inSecond (q : Fin FixedGammaTargetSecondPayload.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetSecondPayload.machine.seqLeft
    FixedGammaTargetMarkersLoopDecrementCountdown.machine q

/-- A G2z state in the composed control, shifted past the fourteen second-payload states. -/
def inChain (q : Fin FixedGammaTargetMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTargetSecondPayload.machine.seqRight
    FixedGammaTargetMarkersLoopDecrementCountdown.machine q

/-- The routed target of a second-payload row: `qDone` becomes G2z's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedGammaTargetSecondPayload.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetSecondPayload.machine.seqRoute
    FixedGammaTargetMarkersLoopDecrementCountdown.machine q

/-- G2p-c's own `startConfig` — the retagged *actual* G2p-b first-payload endpoint — in the composed
control.  Still a phase-local retag of an earlier run, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTargetSecondPayload.machine.seqEmbedRouted
    FixedGammaTargetMarkersLoopDecrementCountdown.machine
    (FixedGammaTargetSecondPayload.startConfig B x w)

/-- Exact cost of the second-payload phase followed by the whole of G2z: G2p-c's first arrival plus
G2z's `markersChainClock`.  The handoff between them costs nothing. -/
def secondChainClock (N zeros d v : Nat) : Nat :=
  FixedGammaTargetSecondPayload.exactClock N zeros +
    FixedGammaTargetMarkersLoopDecrementCountdown.markersChainClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: sixty-eight states, two hundred and four rows, the distinguished
states with their indices, the two block injections with their disjointness, the two nested
sub-blocks of G2z and their indices, the routing cases, every left row as the routed second-payload
row, every right row as the G2z row, the public step against the composed raw table everywhere, the
**single** live routed row into `qDone` with the state indices it connects, and the composed indices
of the four inherited handoff states.  This module pins the one *routed* row that is new to this
composition — `qScanLeft` on `none`, its target re-routed to `14` — and not a new table row; the
inherited rows are not restated, because the universal right-block row equation above transports
every G2z row — `qClearB`/`qBackB` into `28`, `qFin` into `50`, `qBorrow` into `57` — verbatim from
G2z's own audited pins, and the surface tests reduce H14, H15's `qClearB` row, H16 and H17 out of an
actual configuration. -/
theorem table_and_resource_pins :
    machine.stateCount = 68 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 204 ∧
      machine.start = route FixedGammaTargetSecondPayload.qStart ∧
      machine.start = inSecond FixedGammaTargetSecondPayload.qStart ∧
      machine.accept =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 66 ∧ machine.reject.val = 67 ∧
      (∀ q, (inSecond q).val = q.val) ∧ (∀ q, (inSecond q).val < 14) ∧
      (∀ q, (inChain q).val = 14 + q.val) ∧ (∀ q, 14 ≤ (inChain q).val) ∧
      (∀ q, (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers q)).val
        = 14 + q.val) ∧
      (∀ q, (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail q)).val
        = 28 + q.val) ∧
      Function.Injective inSecond ∧ Function.Injective inChain ∧
      (∀ p q, inSecond p ≠ inChain q) ∧
      route FixedGammaTargetSecondPayload.qDone =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetSecondPayload.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetSecondPayload.qDone →
        q ≠ FixedGammaTargetSecondPayload.qReject → route q = inSecond q) ∧
      (∀ q s, machine.step (inSecond q) s =
        (route (FixedGammaTargetSecondPayload.machine.step q s).1,
          (FixedGammaTargetSecondPayload.machine.step q s).2.1,
          (FixedGammaTargetSecondPayload.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inSecond FixedGammaTargetSecondPayload.qScanLeft).val = 11 ∧
      (inSecond FixedGammaTargetSecondPayload.qDone).val = 12 ∧
      (inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start).val = 14 ∧
      machine.step (inSecond FixedGammaTargetSecondPayload.qScanLeft) none =
        (inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start, some false,
          .stay) ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers
        FixedGammaTargetPayloadLoopFoundation.qClearB)).val = 23 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers
        FixedGammaTargetPayloadLoopFoundation.qBackB)).val = 24 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        FixedGammaTargetLoopDecrementCountdown.machine.start)).val = 28 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inLoop
          FixedGammaTargetPayloadRound.qFin))).val = 47 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          FixedGammaTargetDecrementCountdown.machine.start))).val = 50 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inDecrement
            FixedGammaTargetRegisterDecrement.qBorrow)))).val = 54 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inCountdown
            FixedGammaTargetUnaryCountdown.qStart)))).val = 57 := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTargetSecondPayload.machine.seq_pins
      FixedGammaTargetMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun q => q.isLt,
    fun _ => rfl, fun _ => Nat.le_add_right _ _, fun _ => rfl, fun q => ?_, hli, hri, hne, hra,
    hrr, hrw,
    fun q s => FixedGammaTargetSecondPayload.machine.seq_step_left
      FixedGammaTargetMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTargetSecondPayload.machine.seq_step_right
      FixedGammaTargetMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTargetSecondPayload.machine.seq_step_eq_rawStep
      FixedGammaTargetMarkersLoopDecrementCountdown.machine q s,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h : (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail q)).val =
    14 + (14 + q.val) := rfl
  omega

/-- The start, pinned: G2p-c's `startConfig` routed into the composed control — the same head and
tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetSecondPayload.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetSecondPayload.machine.seqEmbedRouted
        FixedGammaTargetMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The chained clock, pinned: G2z's sum prefixed by G2p-c's first arrival, and — on the `2 ≤ zeros`
branch only, since `FixedGammaTargetSecondPayload.exactClock` dispatches on the width — its full
expansion into the second payload digit, the marker preamble, the payload loop and G2x. -/
theorem clock_pins (N zeros d v : Nat) :
    secondChainClock N zeros d v =
        FixedGammaTargetSecondPayload.exactClock N zeros +
          FixedGammaTargetMarkersLoopDecrementCountdown.markersChainClock N zeros d v ∧
      (2 ≤ zeros → secondChainClock N zeros d v =
        2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))) := by
  refine ⟨rfl, fun hz => ?_⟩
  show FixedGammaTargetSecondPayload.exactClock N zeros +
    FixedGammaTargetMarkersLoopDecrementCountdown.markersChainClock N zeros d v = _
  rw [(FixedGammaTargetSecondPayload.exactClock_pins).2.2 N zeros hz,
    (FixedGammaTargetMarkersLoopDecrementCountdown.clock_pins N zeros d v).2]

/-! ### The executed handoff -/

/-- **H14 fires at whatever time G2p-c first accepts, and it costs nothing.**  The width-free core:
given that the second-payload run is in its `qDone` at `T`, in neither terminal before `T`, and that
`T` is at or below G2p-c's length-only deadline `deadline N = 2 * N`, the composed run out of
`startConfig` is in neither composed verdict before `T`, is G2p-c's own run routed up to and
including `T`, at exactly `T` **is** G2z's landed `startConfig B x w` re-embedded, and takes G2z
steps afterwards.  The deadline premise is what identifies G2p-c's configuration at the first
arrival with its configuration at the deadline that G2p-d's marker `startConfig`, and through it
G2z's, retags; it is used in that direction only.  `T` occurs in the statement only; no row of any
of the five tables mentions it. -/
private theorem handoff_of_arrival {a m B : Nat} {x : Bitstring a} {w : Bitstring m} {T : Nat}
    (hdq : (FixedGammaTargetSecondPayload.machine.run T
      (FixedGammaTargetSecondPayload.startConfig B x w)).state =
      FixedGammaTargetSecondPayload.machine.accept)
    (hwork : ∀ t, t < T → (FixedGammaTargetSecondPayload.machine.run t
      (FixedGammaTargetSecondPayload.startConfig B x w)).state ≠
      FixedGammaTargetSecondPayload.machine.accept)
    (hle : T ≤ FixedGammaTargetSecondPayload.deadline (a + m)) :
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRouted
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayload.machine.run t
            (FixedGammaTargetSecondPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) := by
  intro c
  have hstart : FixedGammaTargetSecondPayload.machine.run
      (FixedGammaTargetSecondPayload.deadline (a + m))
      (FixedGammaTargetSecondPayload.startConfig B x w) =
      FixedGammaTargetSecondPayload.machine.run T
        (FixedGammaTargetSecondPayload.startConfig B x w) :=
    FixedGammaTargetSecondPayload.machine.run_accept_of_le _ hdq hle
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTargetSecondPayload.machine.seqEmbedRouted
        FixedGammaTargetMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetSecondPayload.machine.run t
          (FixedGammaTargetSecondPayload.startConfig B x w)) :=
    FixedGammaTargetSecondPayload.machine.seq_run_left
      FixedGammaTargetMarkersLoopDecrementCountdown.machine _ hwork
  have hcfg : FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w =
      ⟨FixedGammaTargetMarkersLoopDecrementCountdown.machine.start,
        (FixedGammaTargetSecondPayload.machine.run T
          (FixedGammaTargetSecondPayload.startConfig B x w)).head,
        (FixedGammaTargetSecondPayload.machine.run T
          (FixedGammaTargetSecondPayload.startConfig B x w)).tape⟩ := by
    rw [← hstart]
    rfl
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTargetSecondPayload.machine.seqEmbedRight
        FixedGammaTargetMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedGammaTargetSecondPayload.machine.seq_handoff
      FixedGammaTargetMarkersLoopDecrementCountdown.machine _ hwork hdq s
  have hT : machine.run T c =
      FixedGammaTargetSecondPayload.machine.seqEmbedRight
        FixedGammaTargetMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) := hsuffix 0
  have hTs : (machine.run T c).state =
      inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start := by
    rw [hT]; rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]; decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]; decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **H14 on the only width an accepted parsed target can reach.**  On a matching tag, a decoded
`2 ≤ zeros` and G2p-c's room, write `T = FixedGammaTargetSecondPayload.exactClock (a+m) zeros
= 2 * (a+m) - 7`.  Out of `startConfig`: before `T` the composed control is in neither verdict; up
to and including `T` the composed configuration is G2p-c's own, routed; at exactly `T` it **is**
G2z's landed `startConfig B x w`, re-embedded — the head and tape G2p-d's marker preamble retags at
G2p-c's length-only deadline `deadline (a+m) = 2*(a+m)`, identified through G2p-c's persistence from
`T` to that deadline; and every further step is a G2z step.  The last three conjuncts rest on
`second_payload_strict` — `qDone` is entered for the *first* time at `T`, so the routed edge fires
then and not earlier — which persistence alone would not give.  The conclusion is extensional in
G2p-c's three source shapes: whether the source `10 + zeros` is physical, is itself the boundary
blank, or is bypassed because `9 + zeros` already is, the same configuration is handed over.  The
fourth conjunct is a simulation equality and needs no marker, loop, decrement, countdown or budget
premise: it holds even where the budget leaves the tail unfinished. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRouted
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayload.machine.run t
            (FixedGammaTargetSecondPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) := by
  have hN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  exact handoff_of_arrival
    (FixedGammaTargetSecondPayload.second_payload_exact x w htag hg hzeros hroom _ le_rfl).1
    (fun t ht =>
      (FixedGammaTargetSecondPayload.second_payload_strict x w htag hg hzeros hroom t ht).1)
    (FixedGammaTargetSecondPayload.exactClock_le_deadline (by omega))

/-- **H14 at width zero.**  The same single routed row fires, at G2p-c's first arrival
`exactClock (a+m) 0 = 3`, with no room premise at all: width zero leaves no *net* write — the fixed
table still blanks the tag cell `7` and restores it in that routed transition, and what G2p-c
exports here is a tape equality with the incoming tape, not a footprint — so the tape G2z's
`startConfig` is handed is the incoming bootstrap scratch tape.  This width is outside every
accepted parsed target (`3 ≤ pr.2.n` forces `2 ≤ gammaZeros pr.2.n`) and nothing downstream is
claimed for it; the point is that the composed table performs the switch at every *decoded* width,
not only at the one the accepted surface uses. -/
theorem zero_width_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) 0
    let c := startConfig B x w
    T = 3 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) := by
  have hN := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 0 hg).1
  obtain ⟨h1, -, h3, h4⟩ := handoff_of_arrival (B := B)
    (FixedGammaTargetSecondPayload.zero_width_exact x w htag hg _ (le_of_eq rfl)).1
    (fun t ht => (FixedGammaTargetSecondPayload.zero_width_strict x w htag hg t ht).1)
    (by unfold FixedGammaTargetSecondPayload.deadline; omega)
  exact ⟨rfl, h1, h3, h4⟩

/-- **H14 at width one.**  The same single routed row fires, at G2p-c's first arrival
`exactClock (a+m) 1 = 5`, under G2p-b's *weaker* room `a + m + 2 < tapeLength (pairLength a m) B`,
which is what makes the incoming tape known at this width; width one leaves no net write either, in
the same sense — the anchor is blanked and restored, and the export is a tape equality, not a
footprint.  Like width zero this is outside every accepted parsed target, and nothing downstream is
claimed for it. -/
theorem width_one_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) 1
    let c := startConfig B x w
    T = 5 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) := by
  have hN := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 1 hg).1
  obtain ⟨h1, -, h3, h4⟩ := handoff_of_arrival
    (FixedGammaTargetSecondPayload.width_one_exact x w htag hg hroom _ (le_of_eq rfl)).1
    (fun t ht => (FixedGammaTargetSecondPayload.width_one_strict x w htag hg hroom t ht).1)
    (by unfold FixedGammaTargetSecondPayload.deadline; omega)
  exact ⟨rfl, h1, h3, h4⟩

/-- **The concrete exact run: the second payload digit, H14, the markers, H15, the loop, H16, the
decrement, H17, the countdown, one machine.**  Under G2u's, G2y's and G2z's **seven** hypotheses — a
matching tag, a decoded `2 ≤ zeros`, the lane cap `v ≤ F`, the room `zeros + 2 + F ≤ a + B`, and a
`v` whose digit `zeros - j` is G2q's decremented register digit `j` with no digit above `zeros` —
after exactly `secondChainClock (a+m) zeros d v` steps out of `startConfig` the composed machine is
in its accept (the countdown's `qDone`) on the separator blank `a+m+2+zeros` with tape
`loopTape B x w zeros 0 v`, persisting at every later time.  That one tape equality already
determines the cleared register, the `v` marks and the blanks beyond, which G2u and G2x state cell
by cell; no cell-by-cell conjunct is restated here.  The first
`FixedGammaTargetSecondPayload.exactClock (a+m) zeros` steps are G2p-c's, H14 fires at its first
arrival, and the remaining `markersChainClock (a+m) zeros d v` steps are G2z's out of the
configuration `handoff_exact` identifies.  No eighth hypothesis: G2p-c's room is derived here from
the drain's own room premise through `room_iff` and `2 ≤ zeros`, which together give `2 ≤ a + B`.
`v` is universally quantified and nothing in pnp3 supplies it; persistence is not first arrival of
the composed accept; `startConfig` still embeds every earlier phase as a retag; reaching the
composed accept is neither halting on a raw input nor language acceptance. -/
theorem second_payload_markers_loop_decrement_countdown_drained {a m B zeros v F : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := secondChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) := by
  have hroomS : a + m + 3 < tapeLength (pairLength a m) B :=
    (FixedGammaTargetSecondPayload.room_iff a m B).2 (by omega)
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg hzeros hroomS
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetMarkersLoopDecrementCountdown.markers_loop_decrement_countdown_drained x w
      htag hg hzeros hfence hroom hv hhigh
  have hE : machine.run (secondChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedGammaTargetSecondPayload.machine.seqEmbedRight
        FixedGammaTargetMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run
          (FixedGammaTargetMarkersLoopDecrementCountdown.markersChainClock (a + m) zeros
            (borrow x w zeros) v)
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w)) :=
    hsuffix (FixedGammaTargetMarkersLoopDecrementCountdown.markersChainClock (a + m) zeros
      (borrow x w zeros) v)
  have hstate : (machine.run (secondChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = secondChainClock (a + m) zeros (borrow x w zeros) v +
      (t - secondChainClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject, executed one block further left.**  A matching tag with no decoded width:
G2p-c rejects in one step — its own landed `malformed_exact`, whose first-arrival companion
`malformed_strict` is not needed, since both machines absorb a rejection — and the generic rejecting
handoff carries that verdict into the composed control, so from step one on the composed machine is
in the composed reject — index `67`, not G2p-c's own `qReject` at index `13` — at the boundary head
`a + m` on the unchanged content tape.  It needs no room premise.  It is **not** a converse —
nothing here says the composed reject implies a malformed gamma — it states no `RejectsAt`, and it
characterises no parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetSecondPayload.malformed_exact (B := B) x w htag hg 1 le_rfl
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedGammaTargetSecondPayload.machine.run 1
          (FixedGammaTargetSecondPayload.startConfig B x w)).head,
        (FixedGammaTargetSecondPayload.machine.run 1
          (FixedGammaTargetSecondPayload.startConfig B x w)).tape⟩ := by
    have h := FixedGammaTargetSecondPayload.machine.seq_reject_handoff
      FixedGammaTargetMarkersLoopDecrementCountdown.machine
      (FixedGammaTargetSecondPayload.startConfig B x w) (T := 1) hq (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]; exact hh
  · rw [hrun]; exact ht

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown
