import Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown

/-!
# The loop markers, the payload loop, the decrement and the countdown as one machine (Part A G2z)

**No new table row.**  `machine` is `FixedGammaTargetPayloadLoopFoundation.machine.seq
FixedGammaTargetLoopDecrementCountdown.machine`: G2p-d's 14-state, 42-row marker-preamble table on
the left block `[0, 14)`, G2y's landed 40-state composite on the right block `[14, 54)` — inside it
G2p-d's payload round at `[14, 36)`, G2q's decrement at `[36, 43)` and G2s-a's countdown at
`[43, 54)` — one closed 54-state, 162-row table whose every row is a row of one of those four
tables with its target routed.  Write `N = a + m` and `d = borrow x w zeros`.
`pnp3/Docs/UniformP_V1.md` carries the long-form notes.  Classification (AGENTS.md):
**Infrastructure**.

**Three executed handoffs.**  H15 is the newly executed one: a marker-preamble row into the
preamble's own absorbing `qDone`, routed to the tail's start — G2p-d's round `qLoop` at composed
index `14` — in that same transition, on that cell, with the tape the preamble leaves, at no cost.
Four rows out of *working* states target `qDone`, and all four are routed:
`qZeroA`/`some true`, `qClearB`/`some true`, `qBackB`/`some true` and `qFin`/`some false`.  The
table reaches the first two of those exits only through the width dispatch that `2 ≤ zeros`
excludes — `qZeroA`'s on a terminator already at cell `8` (width zero) and `qFin`'s on one at cell
`9` (width one) — so the fixtures below exercise `qClearB` and `qBackB`, which `qSrcB` selects by
reading the second payload source: a content symbol takes `qClearB` (write blank, move right), the
boundary blank takes `qBackB` (preserve `true`, stay).  No theorem here says which of the four rows
a given word takes.  The three `qDone` self-rows are routed too, but that state stays dead: no
routed row and no start targets it.  H16 is the payload round's `qFin`-on-`some false` row at
composed index `33 → 36` and H17 is G2x's `qBorrow`-on-`some true` row at `40 → 43`; both are
inherited unchanged from G2y and re-derived here through the right-block row equation.  Until now
H15 was a proof-level retag of the preamble's run at its length-only deadline `deadline N = N`; a
running composed machine switches at the preamble's **first arrival**
`exactClock zeros = zeros + 7`, so `handoff_exact` rests on `markers_strict`.

No new first-arrival theorem is needed: the foundation already carries arrival and persistence
(`markers_installed`), minimality (`markers_strict`) and the deadline cover
(`exactClock_le_deadline`), and `UniformTM.run_accept_of_le` identifies the run at the first arrival
with the run at `deadline N` — the very run G2p-d's round `startConfig`, and through it G2y's,
retags.

`handoff_exact`: out of `startConfig` — the preamble's own `startConfig`, hence still the retagged
*actual* G2p-c second-payload endpoint — the composed run is the preamble's run up to
`T = exactClock zeros`, is in neither composed verdict before `T`, at exactly `T` **is** G2y's
landed `startConfig B x w` re-embedded (its head and whole tape), and every later step is a G2y
step.  Its room premise is the *foundation's* weaker `a + m + 3 < tapeLength (pairLength a m) B`,
not G2y's loop room, so it simulates the tail even where the tail would later lack room.
`markers_loop_decrement_countdown_drained`: at exactly
`markersChainClock N zeros d v = exactClock zeros + chainClock N zeros d v` the composed machine is
in its accept — the countdown's `qDone` — on the separator blank `N + 2 + zeros` with the register
cleared, `v` marks laid and blanks beyond, persisting.  Its **seven** hypotheses are exactly G2u's
and G2y's; the foundation's room is *derived* inside the proof, not assumed.
`malformed_reject_handoff` is the first **routed reject** the chain composition exercises: a
matching tag with no decoded width rejects in one step and the composed control is the composed
reject from then on.  It is not a converse — nothing says the composed reject implies a malformed
gamma — and it characterises no parsed target.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
fourteen handoffs before H15 remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `markersChainClock` is the first time it is entered, since G2s-a and G2u prove
no first arrival for `qDone`; the first arrival proved here is the *marker preamble's*, inside the
left block.  The **fence**: all four tables are uncapped, hence so is this one; an oversized
register runs `qRunEnd` off the tape and sticks, a timeout and neither verdict.  Every **converse**,
a **footprint** theorem — so every room premise is sufficient and used, never shown necessary — and
the pnp4 bridge (taken in `ContentFixedGammaTargetMarkersLoopDecrementCountdownBridge`).  The
composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior
endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin` or `UniformP` is stated.  The table is fixed and complete but not claimed
state-minimal. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (exactClock)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

/-- The composed machine: G2p-d's marker preamble, then G2y's loop-decrement-countdown composite,
as one closed table.  No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTargetPayloadLoopFoundation.machine.seq FixedGammaTargetLoopDecrementCountdown.machine

/-- A marker-preamble state in the composed control, at its own index. -/
def inMarkers (q : Fin FixedGammaTargetPayloadLoopFoundation.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTargetPayloadLoopFoundation.machine.seqLeft
    FixedGammaTargetLoopDecrementCountdown.machine q

/-- A G2y state in the composed control, shifted past the fourteen preamble states. -/
def inTail (q : Fin FixedGammaTargetLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTargetPayloadLoopFoundation.machine.seqRight
    FixedGammaTargetLoopDecrementCountdown.machine q

/-- The routed target of a preamble row: `qDone` becomes G2y's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedGammaTargetPayloadLoopFoundation.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetPayloadLoopFoundation.machine.seqRoute
    FixedGammaTargetLoopDecrementCountdown.machine q

/-- The marker preamble's own `startConfig` — the retagged *actual* G2p-c second-payload endpoint —
in the composed control.  Still a phase-local retag of an earlier run, not `initialConfig` on a raw
pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
    FixedGammaTargetLoopDecrementCountdown.machine
    (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)

/-- Exact cost of the marker preamble followed by the whole of G2y: the preamble's first arrival
plus G2y's `chainClock`.  The handoff between them costs nothing. -/
def markersChainClock (N zeros d v : Nat) : Nat :=
  exactClock zeros + FixedGammaTargetLoopDecrementCountdown.chainClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: fifty-four states, one hundred and sixty-two rows, the
distinguished states with their indices, the two block injections with their disjointness, the two
nested sub-blocks of G2y and their indices, the routing cases, every left row as the routed
preamble row, every right row as the G2y row, the public step against the composed raw table
everywhere, all **four** routed rows into `qDone` with the state indices they connect, and both
inherited handoff rows. -/
theorem table_and_resource_pins :
    machine.stateCount = 54 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 162 ∧
      machine.start = route FixedGammaTargetPayloadLoopFoundation.qStart ∧
      machine.start = inMarkers FixedGammaTargetPayloadLoopFoundation.qStart ∧
      machine.accept = inTail FixedGammaTargetLoopDecrementCountdown.machine.accept ∧
      machine.reject = inTail FixedGammaTargetLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 52 ∧ machine.reject.val = 53 ∧
      (∀ q, (inMarkers q).val = q.val) ∧ (∀ q, (inMarkers q).val < 14) ∧
      (∀ q, (inTail q).val = 14 + q.val) ∧ (∀ q, 14 ≤ (inTail q).val) ∧
      (∀ q, (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop q)).val = 14 + q.val) ∧
      (∀ q, (inTail (FixedGammaTargetLoopDecrementCountdown.inTail q)).val = 36 + q.val) ∧
      Function.Injective inMarkers ∧ Function.Injective inTail ∧
      (∀ p q, inMarkers p ≠ inTail q) ∧
      route FixedGammaTargetPayloadLoopFoundation.qDone =
        inTail FixedGammaTargetLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetPayloadLoopFoundation.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetPayloadLoopFoundation.qDone →
        q ≠ FixedGammaTargetPayloadLoopFoundation.qReject → route q = inMarkers q) ∧
      (∀ q s, machine.step (inMarkers q) s =
        (route (FixedGammaTargetPayloadLoopFoundation.machine.step q s).1,
          (FixedGammaTargetPayloadLoopFoundation.machine.step q s).2.1,
          (FixedGammaTargetPayloadLoopFoundation.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (FixedGammaTargetLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qZeroA).val = 1 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qClearB).val = 9 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qBackB).val = 10 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qFin).val = 11 ∧
      (inTail FixedGammaTargetLoopDecrementCountdown.machine.start).val = 14 ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qZeroA) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some true, .left) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qClearB) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, none, .right) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qBackB) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some true, .stay) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qFin) (some false) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some false, .stay) ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop
        FixedGammaTargetPayloadRound.qFin)).val = 33 ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        FixedGammaTargetDecrementCountdown.machine.start)).val = 36 ∧
      machine.step (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop
          FixedGammaTargetPayloadRound.qFin)) (some false) =
        (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          FixedGammaTargetDecrementCountdown.machine.start), some false, .stay) ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        (FixedGammaTargetDecrementCountdown.inDecrement
          FixedGammaTargetRegisterDecrement.qBorrow))).val = 40 ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        (FixedGammaTargetDecrementCountdown.inCountdown
          FixedGammaTargetUnaryCountdown.qStart))).val = 43 ∧
      machine.step (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inDecrement
            FixedGammaTargetRegisterDecrement.qBorrow))) (some true) =
        (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inCountdown
            FixedGammaTargetUnaryCountdown.qStart)), some false, .stay) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTargetPayloadLoopFoundation.machine.seq_pins
      FixedGammaTargetLoopDecrementCountdown.machine
  have hright : ∀ q s, machine.step (inTail q) s =
      (inTail (FixedGammaTargetLoopDecrementCountdown.machine.step q s).1,
        (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.1,
        (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.2) :=
    fun q s => FixedGammaTargetPayloadLoopFoundation.machine.seq_step_right
      FixedGammaTargetLoopDecrementCountdown.machine q s
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun q => q.isLt,
    fun _ => rfl, fun _ => Nat.le_add_right _ _, fun _ => rfl, fun q => ?_, hli, hri, hne, hra,
    hrr, hrw,
    fun q s => FixedGammaTargetPayloadLoopFoundation.machine.seq_step_left
      FixedGammaTargetLoopDecrementCountdown.machine q s,
    hright,
    fun q s => FixedGammaTargetPayloadLoopFoundation.machine.seq_step_eq_rawStep
      FixedGammaTargetLoopDecrementCountdown.machine q s,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · have h : (inTail (FixedGammaTargetLoopDecrementCountdown.inTail q)).val =
      14 + (22 + q.val) := rfl
    omega
  · rw [hright]
    rfl
  · rw [hright]
    rfl

/-- The start, pinned: the marker preamble's `startConfig` routed into the composed control — the
same head and tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadLoopFoundation.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
        FixedGammaTargetLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The chained clock, pinned: G2y's sum prefixed by the preamble's first arrival, and its full
expansion into the preamble, the payload loop and G2x. -/
theorem clock_pins (N zeros d v : Nat) :
    markersChainClock N zeros d v =
        exactClock zeros + FixedGammaTargetLoopDecrementCountdown.chainClock N zeros d v ∧
      markersChainClock N zeros d v =
        zeros + 7 + (totalClock N zeros + composedClock N zeros d v) :=
  ⟨rfl, rfl⟩

/-! ### The executed handoff -/

/-- **H15 fires at the marker preamble's first arrival, and it costs nothing.**  On a matching tag,
a decoded `2 ≤ zeros` and the *foundation's* room, write `T = exactClock zeros = zeros + 7`.  Out of
`startConfig`: before `T` the composed control is in neither verdict; up to and including `T` the
composed configuration is the preamble's own, routed; at exactly `T` it **is** G2y's landed
`startConfig B x w`, re-embedded — the head and tape G2p-d's round retags at the preamble's
length-only deadline `deadline (a+m) = a+m`, identified through the preamble's persistence from `T`
to that deadline; and every further step is a G2y step.  The last three conjuncts rest on
`markers_strict` — `qDone` is entered for the *first* time at `T`, so the routed edge fires then and
not earlier — which persistence alone would not give.  The fourth conjunct is a simulation equality
and needs no loop, decrement, countdown or budget premise: it holds even where the budget leaves the
tail unfinished, since the room assumed here is the preamble's weaker one, not G2y's.  `T` occurs in
the statement only; no row of any of the four tables mentions it. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let T := exactClock zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetPayloadLoopFoundation.machine.run t
            (FixedGammaTargetPayloadLoopFoundation.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetLoopDecrementCountdown.machine.run s
            (FixedGammaTargetLoopDecrementCountdown.startConfig B x w))) := by
  intro T c
  have hN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  obtain ⟨hdq, -, -⟩ :=
    FixedGammaTargetPayloadLoopFoundation.markers_installed x w htag hg hzeros hroom T le_rfl
  have hstart : FixedGammaTargetPayloadLoopFoundation.machine.run
      (FixedGammaTargetPayloadLoopFoundation.deadline (a + m))
      (FixedGammaTargetPayloadLoopFoundation.startConfig B x w) =
      FixedGammaTargetPayloadLoopFoundation.machine.run T
        (FixedGammaTargetPayloadLoopFoundation.startConfig B x w) :=
    FixedGammaTargetPayloadLoopFoundation.machine.run_accept_of_le _ hdq
      (FixedGammaTargetPayloadLoopFoundation.exactClock_le_deadline hN)
  have hwork : ∀ t, t < T →
      (FixedGammaTargetPayloadLoopFoundation.machine.run t
        (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)).state ≠
        FixedGammaTargetPayloadLoopFoundation.machine.accept :=
    fun t ht =>
      (FixedGammaTargetPayloadLoopFoundation.markers_strict x w htag hg hzeros hroom t ht).1
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
        FixedGammaTargetLoopDecrementCountdown.machine
        (FixedGammaTargetPayloadLoopFoundation.machine.run t
          (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)) :=
    FixedGammaTargetPayloadLoopFoundation.machine.seq_run_left
      FixedGammaTargetLoopDecrementCountdown.machine _ hwork
  have hcfg : FixedGammaTargetLoopDecrementCountdown.startConfig B x w =
      ⟨FixedGammaTargetLoopDecrementCountdown.machine.start,
        (FixedGammaTargetPayloadLoopFoundation.machine.run T
          (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)).head,
        (FixedGammaTargetPayloadLoopFoundation.machine.run T
          (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)).tape⟩ := by
    rw [← hstart]
    rfl
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
        FixedGammaTargetLoopDecrementCountdown.machine
        (FixedGammaTargetLoopDecrementCountdown.machine.run s
          (FixedGammaTargetLoopDecrementCountdown.startConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedGammaTargetPayloadLoopFoundation.machine.seq_handoff
      FixedGammaTargetLoopDecrementCountdown.machine _ hwork hdq s
  have hT : machine.run T c =
      FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
        FixedGammaTargetLoopDecrementCountdown.machine
        (FixedGammaTargetLoopDecrementCountdown.startConfig B x w) := hsuffix 0
  have hTs : (machine.run T c).state =
      inTail FixedGammaTargetLoopDecrementCountdown.machine.start := by
    rw [hT]; rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]; decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]; decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **The concrete exact run: markers, H15, loop, H16, decrement, H17, countdown, one machine.**
Under G2u's and G2y's **seven** hypotheses — a matching tag, a decoded `2 ≤ zeros`, the lane cap
`v ≤ F`, the room `zeros + 2 + F ≤ a + B`, and a `v` whose digit `zeros - j` is G2q's decremented
register digit `j` with no digit above `zeros` — after exactly
`markersChainClock (a+m) zeros d v` steps out of `startConfig` the composed machine is in its accept
(the countdown's `qDone`) on the separator blank `a+m+2+zeros` with tape `loopTape B x w zeros 0 v`,
persisting at every later time.  That one tape equality already determines the cleared register, the
`v` marks and the blanks beyond, which G2u and G2x state cell by cell; no cell-by-cell conjunct is
restated here.  The first `exactClock zeros` steps are the marker preamble's, H15 fires at its first
arrival, and the remaining `chainClock (a+m) zeros d v` steps are G2y's out of the configuration
`handoff_exact` identifies.  No eighth hypothesis: the preamble's room is derived here from the
drain's own room premise through `room_iff` and `2 ≤ zeros`, which together give `2 ≤ a + B`.  `v`
is universally quantified and nothing in pnp3 supplies
it; persistence is not first arrival of the composed accept; `startConfig` still embeds every
earlier phase as a retag; reaching the composed accept is neither halting on a raw input nor
language acceptance. -/
theorem markers_loop_decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := markersChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) := by
  have hroomF : a + m + 3 < tapeLength (pairLength a m) B :=
    (FixedGammaTargetPayloadLoopFoundation.room_iff a m B).2 (by omega)
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg hzeros hroomF
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetLoopDecrementCountdown.loop_decrement_countdown_drained x w htag hg hzeros
      hfence hroom hv hhigh
  have hE : machine.run (markersChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
        FixedGammaTargetLoopDecrementCountdown.machine
        (FixedGammaTargetLoopDecrementCountdown.machine.run
          (FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros (borrow x w zeros) v)
          (FixedGammaTargetLoopDecrementCountdown.startConfig B x w)) :=
    hsuffix (FixedGammaTargetLoopDecrementCountdown.chainClock (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (markersChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = markersChainClock (a + m) zeros (borrow x w zeros) v +
      (t - markersChainClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject, executed.**  A matching tag with no decoded width: the preamble rejects in
one step, and the generic rejecting handoff carries that verdict into the composed control, so from
step one on the composed machine is in the composed reject — index `53` — at the boundary head
`a + m` on the unchanged content tape.  This is the first routed-reject row the chain composition
exercises.  It needs no room premise and no first-arrival hypothesis, since both machines absorb a
rejection.  It is **not** a converse — nothing here says the composed reject implies a malformed
gamma — and it characterises no parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetPayloadLoopFoundation.malformed_rejects (B := B) x w htag hg 1 le_rfl
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedGammaTargetPayloadLoopFoundation.machine.run 1
          (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)).head,
        (FixedGammaTargetPayloadLoopFoundation.machine.run 1
          (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)).tape⟩ := by
    have h := FixedGammaTargetPayloadLoopFoundation.machine.seq_reject_handoff
      FixedGammaTargetLoopDecrementCountdown.machine
      (FixedGammaTargetPayloadLoopFoundation.startConfig B x w) (T := 1) hq (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]; exact hh
  · rw [hrun]; exact ht

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown
