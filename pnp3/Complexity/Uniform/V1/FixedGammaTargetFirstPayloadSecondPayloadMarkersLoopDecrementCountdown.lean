import Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown

/-!
# The first payload digit, the second payload digit, the loop markers, the payload loop, the
decrement and the countdown as one machine (Part A G3c)

**No new table row.**  `machine` is `FixedGammaTargetFirstPayload.machine.seq
FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine`: G2p-b's 18-state, 54-row
first-payload table on the left block `[0, 18)` and the whole landed G3a 68-state composite on the
right block `[18, 86)` — inside it G2p-c's second payload at `[18, 32)`, G2p-d's marker preamble at
`[32, 46)`, G2p-d's payload round at `[46, 68)`, G2q's decrement at `[68, 75)` and G2s-a's countdown
at `[75, 86)` — one closed 86-state, 258-row table whose every row is a row of one of those six
tables with its target routed.  Write `N = a + m` and `d = borrow x w zeros`.
`pnp3/Docs/UniformP_V1.md` carries the long-form notes.  Classification (AGENTS.md):
**Infrastructure**.

**Five executed handoffs.**  H13 is the newly executed one, and like H14 it has exactly **one** live
routed row: `qSeekAnchor` on `none` is the only row out of a *working* first-payload state that
targets that machine's own absorbing `qDone`, and `seq` routes it to the tail's start — G3a's
composed start at index `18` — in that same transition, on that cell, writing `some false` and
staying, at no cost.  The three `qDone` self-rows are routed too, but that state stays dead: no
routed row and no start targets it.  H14 (`29 → 32`), H15 (four routed rows into `46`, of which
`2 ≤ zeros` reaches only `qClearB` at `41` and `qBackB` at `42`), H16 (`65 → 68`) and H17
(`72 → 75`) are inherited unchanged from G3a, located here by the two block-offset equations and
carried by the universal right-block row equation, which transports every G3a row verbatim.  Those
composed indices are the G3a indices shifted by eighteen.  Until now H13 was a
proof-level retag at G2p-b's length-only deadline `deadline N = 3 * N`; a running composed machine
switches at G2p-b's **first arrival**, so `handoff_exact` rests on `first_payload_strict`.

No new first-arrival theorem is needed: Part A G3b gave G2p-b arrival (`first_payload_exact`),
minimality (`first_payload_strict`) and the deadline cover (`exactClock_le_deadline`) at every
decoded width, and `UniformTM.run_accept_of_le` identifies the run at the first arrival with the run
at `deadline N` — the very run G2p-c's `startConfig`, and through it G3a's, retags.

**Every decoded width.**  `handoff_exact` is the whole positive branch `0 < zeros`, whose first
arrival is `FixedGammaTargetFirstPayload.exactClock N zeros = 2 * N + zeros - 6`; G2p-b splits its
widths as `0` against `0 < zeros` and not as G2p-c does, so no separate width-one statement exists
or is needed here.  An *accepted parsed target* reaches only `2 ≤ zeros`, since `3 ≤ pr.2.n` forces
`2 ≤ gammaZeros pr.2.n`, and that is a sub-case of this branch.  Inside it G2p-b's endpoint is
extensional in its two source shapes — physical payload cell `9 + zeros < N`, and payload cell on
the boundary blank `9 + zeros = N`, which copies the virtual zero — so both hand the same
configuration over.  The degenerate width zero is outside any accepted target but not outside this
table: `zero_width_handoff` (first arrival `6`) states the same switch on the incoming bootstrap
scratch tape, which G2p-b leaves with no net write at that width, and nothing downstream is claimed
for it.

`handoff_exact`: out of `startConfig` — G2p-b's own, hence still the retagged *actual* G2p-a
bootstrap endpoint — the composed run is G2p-b's run up to
`T = FixedGammaTargetFirstPayload.exactClock N zeros`, is in neither composed verdict before `T`, at
exactly `T` **is** G3a's landed `startConfig B x w` re-embedded (its head and whole tape), and every
later step is a G3a step.  Its room premise is G2p-b's own
`a + m + 2 < tapeLength (pairLength a m) B`, which is weaker than G2p-c's, so it simulates the tail
even where the tail would later lack room.
`first_payload_second_payload_markers_loop_decrement_countdown_drained`: at exactly
`firstChainClock N zeros d v = FixedGammaTargetFirstPayload.exactClock N zeros +
secondChainClock N zeros d v` the composed machine is in its accept — the countdown's `qDone` — on
the separator blank `N + 2 + zeros` with the register cleared, `v` marks laid and blanks beyond,
persisting.  Its **seven** hypotheses are exactly G2u's, G2y's, G2z's and G3a's; G2p-b's room is
*derived* inside the proof, by weakening G2p-c's, which `room_iff` reads off the drain's own room
premise together with `2 ≤ zeros`.
`malformed_reject_handoff` transports G2p-b's own exact malformed endpoint: a matching tag with no
decoded width rejects in one step and the composed control is the composed reject — index `85` —
from then on.  It is stated in the forward direction only; nothing says the composed reject implies
a malformed gamma, and it characterises no parsed target.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
twelve handoffs before H13 remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `firstChainClock` is the first time it is entered, since G2s-a and G2u prove no
first arrival for `qDone`; the first arrival proved here is *G2p-b's*, inside the left block.  The
**fence**: all six tables are uncapped, hence so is this one; an oversized register runs `qRunEnd`
off the tape and sticks, a timeout and neither verdict.  Every **converse**, a **footprint**
theorem — so every room premise is sufficient and used, never shown necessary — and the pnp4 bridge
(taken in `ContentFixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`).
The composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual
prior endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin` or `UniformP` is stated.  The table is fixed and complete but not claimed
state-minimal. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown (secondChainClock)

/-- The composed machine: G2p-b's first-payload table, then G3a's whole second-payload composite, as
one closed table.  No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTargetFirstPayload.machine.seq
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine

/-- A first-payload state in the composed control, at its own index. -/
def inFirst (q : Fin FixedGammaTargetFirstPayload.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetFirstPayload.machine.seqLeft
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- A G3a state in the composed control, shifted past the eighteen first-payload states. -/
def inChain (q : Fin FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTargetFirstPayload.machine.seqRight
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- The routed target of a first-payload row: `qDone` becomes G3a's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedGammaTargetFirstPayload.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetFirstPayload.machine.seqRoute
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- G2p-b's own `startConfig` — the retagged *actual* G2p-a bootstrap endpoint — in the composed
control.  Still a phase-local retag of an earlier run, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTargetFirstPayload.machine.seqEmbedRouted
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedGammaTargetFirstPayload.startConfig B x w)

/-- Exact cost of the first-payload phase followed by the whole of G3a: G2p-b's first arrival plus
G3a's `secondChainClock`.  The handoff between them costs nothing. -/
def firstChainClock (N zeros d v : Nat) : Nat :=
  FixedGammaTargetFirstPayload.exactClock N zeros + secondChainClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: eighty-six states, two hundred and fifty-eight rows, the
distinguished states with their indices, the two block injections with their disjointness, the two
nested sub-blocks of G3a and their indices, the routing cases, every left row as the routed
first-payload row, every right row as the G3a row, the public step against the composed raw table
everywhere, the **single** live routed row into `qDone` with the state indices it connects, and the
composed index of G3a's start.  This module pins the one *routed* row that is new to this
composition — `qSeekAnchor` on `none`, its target re-routed to `18` — and not a new table row; the
inherited rows are not restated, because the universal right-block row equation above transports
every G3a row verbatim from G3a's own audited pins, and the two block-offset equations locate them:
H14 at `29 → 32`, H15's `qClearB`/`qBackB` at `41`/`42` into `46`, H16 at `65 → 68` and H17 at
`72 → 75` are the G3a indices `11 → 14`, `23`/`24` into `28`, `47 → 50` and `54 → 57` shifted by
eighteen.  The surface tests reduce H13, H14, H15's `qClearB` row, H16 and H17 out of an actual
configuration. -/
theorem table_and_resource_pins :
    machine.stateCount = 86 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 258 ∧
      machine.start = route FixedGammaTargetFirstPayload.qStart ∧
      machine.start = inFirst FixedGammaTargetFirstPayload.qStart ∧
      machine.accept =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 84 ∧ machine.reject.val = 85 ∧
      (∀ q, (inFirst q).val = q.val) ∧ (∀ q, (inFirst q).val < 18) ∧
      (∀ q, (inChain q).val = 18 + q.val) ∧ (∀ q, 18 ≤ (inChain q).val) ∧
      (∀ q, (inChain (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inSecond q)).val
        = 18 + q.val) ∧
      (∀ q, (inChain (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inChain q)).val
        = 32 + q.val) ∧
      Function.Injective inFirst ∧ Function.Injective inChain ∧
      (∀ p q, inFirst p ≠ inChain q) ∧
      route FixedGammaTargetFirstPayload.qDone =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetFirstPayload.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetFirstPayload.qDone →
        q ≠ FixedGammaTargetFirstPayload.qReject → route q = inFirst q) ∧
      (∀ q s, machine.step (inFirst q) s =
        (route (FixedGammaTargetFirstPayload.machine.step q s).1,
          (FixedGammaTargetFirstPayload.machine.step q s).2.1,
          (FixedGammaTargetFirstPayload.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inFirst FixedGammaTargetFirstPayload.qSeekAnchor).val = 15 ∧
      (inFirst FixedGammaTargetFirstPayload.qDone).val = 16 ∧
      (inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start).val = 18 ∧
      machine.step (inFirst FixedGammaTargetFirstPayload.qSeekAnchor) none =
        (inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start,
          some false, .stay) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTargetFirstPayload.machine.seq_pins
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun q => q.isLt,
    fun _ => rfl, fun _ => Nat.le_add_right _ _, fun _ => rfl, fun q => ?_, hli, hri, hne, hra,
    hrr, hrw,
    fun q s => FixedGammaTargetFirstPayload.machine.seq_step_left
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTargetFirstPayload.machine.seq_step_right
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTargetFirstPayload.machine.seq_step_eq_rawStep
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    rfl, rfl, rfl, rfl⟩
  have h : (inChain
      (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inChain q)).val =
    18 + (14 + q.val) := rfl
  omega

/-- The start, pinned: G2p-b's `startConfig` routed into the composed control — the same head and
tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetFirstPayload.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetFirstPayload.machine.seqEmbedRouted
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The chained clock, pinned: G3a's sum prefixed by G2p-b's first arrival, its value on the
positive branch — `FixedGammaTargetFirstPayload.exactClock` dispatches on the width — and, on
`2 ≤ zeros`, its full expansion into the first payload digit, the second payload digit, the marker
preamble, the payload loop and G2x. -/
theorem clock_pins (N zeros d v : Nat) :
    firstChainClock N zeros d v =
        FixedGammaTargetFirstPayload.exactClock N zeros + secondChainClock N zeros d v ∧
      (0 < zeros → firstChainClock N zeros d v =
        2 * N + zeros - 6 + secondChainClock N zeros d v) ∧
      (2 ≤ zeros → firstChainClock N zeros d v =
        2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))) := by
  have hpos : ∀ z, 0 < z → firstChainClock N z d v =
      2 * N + z - 6 + secondChainClock N z d v := by
    intro z hz
    show FixedGammaTargetFirstPayload.exactClock N z + secondChainClock N z d v = _
    rw [(FixedGammaTargetFirstPayload.exactClock_pins).2.1 N z hz]
  refine ⟨rfl, hpos zeros, fun hz => ?_⟩
  rw [hpos zeros (by omega),
    (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.clock_pins N zeros d v).2 hz]

/-! ### The executed handoff -/

/-- **H13 fires at whatever time G2p-b first accepts, and it costs nothing.**  The width-free core:
given that the first-payload run is in its `qDone` at `T`, in neither terminal before `T`, and that
`T` is at or below G2p-b's length-only deadline `deadline N = 3 * N`, the composed run out of
`startConfig` is in neither composed verdict before `T`, is G2p-b's own run routed up to and
including `T`, at exactly `T` **is** G3a's landed `startConfig B x w` re-embedded, and takes G3a
steps afterwards.  The deadline premise is what identifies G2p-b's configuration at the first
arrival with its configuration at the deadline that G2p-c's `startConfig`, and through it G3a's,
retags; it is used in that direction only.  `T` occurs in the statement only; no row of any of the
six tables mentions it. -/
private theorem handoff_of_arrival {a m B : Nat} {x : Bitstring a} {w : Bitstring m} {T : Nat}
    (hdq : (FixedGammaTargetFirstPayload.machine.run T
      (FixedGammaTargetFirstPayload.startConfig B x w)).state =
      FixedGammaTargetFirstPayload.machine.accept)
    (hwork : ∀ t, t < T → (FixedGammaTargetFirstPayload.machine.run t
      (FixedGammaTargetFirstPayload.startConfig B x w)).state ≠
      FixedGammaTargetFirstPayload.machine.accept)
    (hle : T ≤ FixedGammaTargetFirstPayload.deadline (a + m)) :
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRouted
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayload.machine.run t
            (FixedGammaTargetFirstPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w))) := by
  intro c
  have hstart : FixedGammaTargetFirstPayload.machine.run
      (FixedGammaTargetFirstPayload.deadline (a + m))
      (FixedGammaTargetFirstPayload.startConfig B x w) =
      FixedGammaTargetFirstPayload.machine.run T
        (FixedGammaTargetFirstPayload.startConfig B x w) :=
    FixedGammaTargetFirstPayload.machine.run_accept_of_le _ hdq hle
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTargetFirstPayload.machine.seqEmbedRouted
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetFirstPayload.machine.run t
          (FixedGammaTargetFirstPayload.startConfig B x w)) :=
    FixedGammaTargetFirstPayload.machine.seq_run_left
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine _ hwork
  have hcfg : FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w =
      ⟨FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedGammaTargetFirstPayload.machine.run T
          (FixedGammaTargetFirstPayload.startConfig B x w)).head,
        (FixedGammaTargetFirstPayload.machine.run T
          (FixedGammaTargetFirstPayload.startConfig B x w)).tape⟩ := by
    rw [← hstart]
    rfl
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTargetFirstPayload.machine.seqEmbedRight
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedGammaTargetFirstPayload.machine.seq_handoff
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine _ hwork hdq s
  have hT : machine.run T c =
      FixedGammaTargetFirstPayload.machine.seqEmbedRight
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) :=
    hsuffix 0
  have hTs : (machine.run T c).state =
      inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start := by
    rw [hT]; rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]; decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]; decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **H13 at every positive decoded width.**  On a matching tag, a decoded `0 < zeros` and G2p-b's
room, write `T = FixedGammaTargetFirstPayload.exactClock (a+m) zeros = 2 * (a+m) + zeros - 6`.  Out
of `startConfig`: before `T` the composed control is in neither verdict; up to and including `T` the
composed configuration is G2p-b's own, routed; at exactly `T` it **is** G3a's landed
`startConfig B x w`, re-embedded — the head and tape G2p-c's second-payload phase retags at G2p-b's
length-only deadline `deadline (a+m) = 3*(a+m)`, identified through G2p-b's persistence from `T` to
that deadline; and every further step is a G3a step.  The last three conjuncts rest on
`first_payload_strict` — `qDone` is entered for the *first* time at `T`, so the routed edge fires
then and not earlier — which persistence alone would not give.  The conclusion is extensional in
G2p-b's two source shapes: whether the payload cell `9 + zeros` is physical or is itself the
boundary blank, the same configuration is handed over.  An accepted parsed target reaches only the
sub-case `2 ≤ zeros`.  The fourth conjunct is a simulation equality and needs no marker, loop,
decrement, countdown or budget premise: it holds even where the budget leaves the tail
unfinished. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetFirstPayload.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRouted
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayload.machine.run t
            (FixedGammaTargetFirstPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w))) := by
  have hN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  exact handoff_of_arrival
    (FixedGammaTargetFirstPayload.first_payload_exact x w htag hg hzeros hroom _ le_rfl).1
    (fun t ht =>
      (FixedGammaTargetFirstPayload.first_payload_strict x w htag hg hzeros hroom t ht).1)
    (FixedGammaTargetFirstPayload.exactClock_le_deadline hN)

/-- **H13 at width zero.**  The same single routed row fires, at G2p-b's first arrival
`exactClock (a+m) 0 = 6`, with no room premise at all: width zero leaves no *net* write — the fixed
table blanks the terminator at `8` and the anchor at `7` in flight and restores both, and what
G2p-b exports here is a tape equality with the incoming bootstrap scratch tape, not a footprint — so
the tape G3a's `startConfig` is handed is that scratch tape.  This width is outside every accepted
parsed target (`3 ≤ pr.2.n` forces `2 ≤ gammaZeros pr.2.n`) and nothing downstream is claimed for
it; the point is that the composed table performs the switch at every *decoded* width, not only at
the ones the accepted surface uses. -/
theorem zero_width_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let T := FixedGammaTargetFirstPayload.exactClock (a + m) 0
    let c := startConfig B x w
    T = 6 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w))) := by
  have hN := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 0 hg).1
  obtain ⟨h1, -, h3, h4⟩ := handoff_of_arrival (B := B)
    (FixedGammaTargetFirstPayload.zero_width_exact x w htag hg _ (le_of_eq rfl)).1
    (fun t ht => (FixedGammaTargetFirstPayload.zero_width_strict x w htag hg t ht).1)
    (FixedGammaTargetFirstPayload.exactClock_le_deadline (zeros := 0) (by omega))
  exact ⟨rfl, h1, h3, h4⟩

/-- **The concrete exact run: the first payload digit, H13, the second payload digit, H14, the
markers, H15, the loop, H16, the decrement, H17, the countdown, one machine.**  Under G2u's, G2y's,
G2z's and G3a's **seven** hypotheses — a matching tag, a decoded `2 ≤ zeros`, the lane cap `v ≤ F`,
the room `zeros + 2 + F ≤ a + B`, and a `v` whose digit `zeros - j` is G2q's decremented register
digit `j` with no digit above `zeros` — after exactly `firstChainClock (a+m) zeros d v` steps out of
`startConfig` the composed machine is in its accept (the countdown's `qDone`) on the separator blank
`a+m+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting at every later time.  That one tape
equality already determines the cleared register, the `v` marks and the blanks beyond, which G2u and
G2x state cell by cell; no cell-by-cell conjunct is restated here.  The first
`FixedGammaTargetFirstPayload.exactClock (a+m) zeros` steps are G2p-b's, H13 fires at its first
arrival, and the remaining `secondChainClock (a+m) zeros d v` steps are G3a's out of the
configuration `handoff_exact` identifies.  No eighth hypothesis: G2p-b's room is derived here from
G2p-c's, which G3a derives in turn from the drain's own room premise.  `v` is universally quantified
and nothing in pnp3 supplies it; persistence is not first arrival of the composed accept;
`startConfig` still embeds every earlier phase as a retag; reaching the composed accept is neither
halting on a raw input nor language acceptance. -/
theorem first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := firstChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) := by
  have hroomS : a + m + 3 < tapeLength (pairLength a m) B :=
    (FixedGammaTargetSecondPayload.room_iff a m B).2 (by omega)
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w htag hg (by omega) (by omega)
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.second_payload_markers_loop_decrement_countdown_drained
      x w htag hg hzeros hfence hroom hv hhigh
  have hE : machine.run (firstChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedGammaTargetFirstPayload.machine.seqEmbedRight
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (secondChainClock (a + m) zeros (borrow x w zeros) v)
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)) :=
    hsuffix (secondChainClock (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (firstChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = firstChainClock (a + m) zeros (borrow x w zeros) v +
      (t - firstChainClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject, executed one block further left.**  A matching tag with no decoded width:
G2p-b rejects in one step — its own landed `malformed_exact`, whose first-arrival companion
`malformed_strict` is not needed, since both machines absorb a rejection — and the generic rejecting
handoff carries that verdict into the composed control, so from step one on the composed machine is
in the composed reject — index `85`, not G2p-b's own `qReject` at index `17` — at the boundary head
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
    FixedGammaTargetFirstPayload.malformed_exact (B := B) x w htag hg 1 le_rfl
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedGammaTargetFirstPayload.machine.run 1
          (FixedGammaTargetFirstPayload.startConfig B x w)).head,
        (FixedGammaTargetFirstPayload.machine.run 1
          (FixedGammaTargetFirstPayload.startConfig B x w)).tape⟩ := by
    have h := FixedGammaTargetFirstPayload.machine.seq_reject_handoff
      FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedGammaTargetFirstPayload.startConfig B x w) (T := 1) hq (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]; exact hh
  · rw [hrun]; exact ht

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
