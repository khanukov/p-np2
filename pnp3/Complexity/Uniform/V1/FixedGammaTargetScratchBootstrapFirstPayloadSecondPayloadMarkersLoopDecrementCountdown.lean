import Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

/-!
# The scratch bootstrap, the first payload digit, the second payload digit, the loop markers, the
payload loop, the decrement and the countdown as one machine (Part A G3e)

**No new table row.**  `machine` is `FixedGammaTerminatorScratchBootstrap.machine.seq
FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`: G2p-a's 9-state,
27-row scratch-bootstrap table on the left block `[0, 9)` and the whole landed G3c 86-state
composite on the right block `[9, 95)` — inside it G2p-b's first payload at `[9, 27)`, G2p-c's
second payload at `[27, 41)`, G2p-d's marker preamble at `[41, 55)`, G2p-d's payload round at
`[55, 77)`, G2q's decrement at `[77, 84)` and G2s-a's countdown at `[84, 95)` — one closed 95-state,
285-row table whose every row is a row of one of those seven tables with its target routed.  Write
`N = a + m` and `d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
The label `G3d` is unused; the immediately preceding composite is G3c.  Classification
(AGENTS.md): **Infrastructure**.

**Six executed handoffs.**  H12 is the newly executed one, and like H13 and H14 it has exactly
**one** live routed row: `qScanLeft` on `none` is the only row out of a *working* bootstrap state
that targets that machine's own absorbing `qTerm`, and `seq` routes it to the tail's start — G3c's
composed start at index `9` — in that same transition, on that cell, writing `some true` (restoring
the gamma terminator the bootstrap blanked as its return marker) and staying, at no cost.  The
three `qTerm` self-rows are routed too, but that state stays dead: no routed row and no start
targets it.  H13 (`24 → 27`), H14 (`38 → 41`), H15 (four routed rows into `55`, of which
`2 ≤ zeros` reaches only `qClearB` at `50` and `qBackB` at `51`), H16 (`74 → 77`) and H17
(`81 → 84`) are inherited unchanged from G3c, located here by the four block-offset equations and
carried by the universal right-block row equation, which transports every G3c row verbatim.  Those
composed indices are the G3c indices shifted by nine.  Until now H12 was a proof-level retag at
G2p-a's length-only deadline `deadline N = 2 * N`; a running composed machine switches at G2p-a's
**first arrival**, so `handoff_exact` rests on `strict_first_terminal`.

No new first-arrival theorem is needed: G2p-a landed arrival, minimality *and* the deadline cover
in one statement — `strict_first_terminal` excludes both terminals strictly before
`exactClock N zeros = 2 * N - 11 - zeros` and lands `qTerm` there, and `exactClock_le_deadline`
holds for *all* `N` and `zeros` with no premise at all — and `UniformTM.run_accept_of_le`
identifies the run at the first arrival with the run at `deadline N`, the very run G2p-b's
`startConfig`, and through it G3c's, retags.

**Every decoded width, no room premise.**  `handoff_exact` takes only a matching tag and a decoded
width: G2p-a's clock does not split on the width (only its start head does, `7` at width zero
against `6` at a positive one, which its own trace absorbs) and its run needs no room, since the
scratch cell `N + 1` is allocated by `tapeLength` for every budget including `B = 0`.  So unlike
G3c, which needs a separate width-zero statement and G2p-b's room, one theorem covers `zeros = 0`
and `0 < zeros` alike.  An accepted parsed target reaches only `2 ≤ zeros`, since `3 ≤ pr.2.n`
forces `2 ≤ gammaZeros pr.2.n`, and that is a sub-case.

`handoff_exact`: out of `startConfig` — G2p-a's own, hence still the retagged *actual* G2m
dispatcher endpoint — the composed run is G2p-a's run up to
`T = FixedGammaTerminatorScratchBootstrap.exactClock N zeros`, is in neither composed verdict
before `T`, at exactly `T` **is** G3c's landed `startConfig B x w` re-embedded (its head and whole
tape), and every later step is a G3c step.
`handoff_endpoint_pins` reads that switch configuration back semantically: its head is the restored
terminator cell `8 + zeros` and its whole tape is G2p-a's `scratchTape`, and those are *the same
two projections* that G2p-b's own `startConfig` carries — so what the composed machine computes at
the switch is exactly what the next phase's specification assumes, with no reinterpretation.
`scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained`: at
exactly `bootChainClock N zeros d v = FixedGammaTerminatorScratchBootstrap.exactClock N zeros +
firstChainClock N zeros d v` the composed machine is in its accept — the countdown's `qDone` — on
the separator blank `N + 2 + zeros` with the register cleared, `v` marks laid and blanks beyond,
persisting.  Its **seven** hypotheses are exactly G2u's, G2y's, G2z's, G3a's and G3c's; G2p-a's
handoff adds none, because it has none to add.
`malformed_reject_handoff` transports G2p-a's own exact malformed endpoint: a matching tag with no
decoded width — the dispatcher stopped at the blank boundary cell `N` — rejects in one step and the
composed control is the composed reject, index `94`, from then on.  It is stated in the forward
direction only; nothing says the composed reject implies a malformed gamma, and it characterises no
parsed target.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
eleven handoffs before H12 remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `bootChainClock` is the first time it is entered, since G2s-a and G2u prove no
first arrival for `qDone`; the first arrival proved here is *G2p-a's*, inside the left block.  The
**fence**: all seven tables are uncapped, hence so is this one; an oversized register runs `qRunEnd`
off the tape and sticks, a timeout and neither verdict.  Every **converse**, a **footprint**
theorem for the composite — so every room premise of the tail is sufficient and used, never shown
necessary — and the pnp4 bridge (taken in
`ContentFixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`).
The composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual
prior endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin` or `UniformP` is stated.  The table is fixed and complete but not claimed
state-minimal. -/

namespace
  Pnp3.Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown (firstChainClock)

/-- The composed machine: G2p-a's scratch-bootstrap table, then G3c's whole first-payload
composite, as one closed table.  No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTerminatorScratchBootstrap.machine.seq
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- A bootstrap state in the composed control, at its own index. -/
def inBoot (q : Fin FixedGammaTerminatorScratchBootstrap.stateCount) : Fin machine.stateCount :=
  FixedGammaTerminatorScratchBootstrap.machine.seqLeft
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- A G3c state in the composed control, shifted past the nine bootstrap states. -/
def inChain
    (q : Fin
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTerminatorScratchBootstrap.machine.seqRight
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- The routed target of a bootstrap row: `qTerm` becomes G3c's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedGammaTerminatorScratchBootstrap.stateCount) : Fin machine.stateCount :=
  FixedGammaTerminatorScratchBootstrap.machine.seqRoute
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q

/-- G2p-a's own `startConfig` — the retagged *actual* G2m dispatcher endpoint — in the composed
control.  Still a phase-local retag of an earlier run, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedGammaTerminatorScratchBootstrap.startConfig B x w)

/-- Exact cost of the scratch-bootstrap phase followed by the whole of G3c: G2p-a's first arrival
plus G3c's `firstChainClock`.  The handoff between them costs nothing. -/
def bootChainClock (N zeros d v : Nat) : Nat :=
  FixedGammaTerminatorScratchBootstrap.exactClock N zeros + firstChainClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: ninety-five states, two hundred and eighty-five rows, the
distinguished states with their indices, the two block injections with their disjointness, the four
nested sub-blocks of G3c and their indices, the routing cases, every left row as the routed
bootstrap row, every right row as the G3c row, the public step against the composed raw table
everywhere, the **single** live routed row into `qTerm` with the state indices it connects, and the
composed index of G3c's start.  This module pins the one *routed* row that is new to this
composition — `qScanLeft` on `none`, its target re-routed to `9` — and not a new table row; the
inherited rows are not restated, because the universal right-block row equation above transports
every G3c row verbatim from G3c's own audited pins, and the four block-offset equations locate
them: H13 at `24 → 27`, H14 at `38 → 41`, H15's `qClearB`/`qBackB` at `50`/`51` into `55`, H16 at
`74 → 77` and H17 at `81 → 84` are the G3c indices `15 → 18`, `29 → 32`, `41`/`42` into `46`,
`65 → 68` and `72 → 75` shifted by nine.  The surface tests reduce H12, H13, H14, H15's `qClearB`
row, H16 and H17 out of an actual configuration. -/
theorem table_and_resource_pins :
    machine.stateCount = 95 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 285 ∧
      machine.start = route FixedGammaTerminatorScratchBootstrap.qStart ∧
      machine.start = inBoot FixedGammaTerminatorScratchBootstrap.qStart ∧
      machine.accept =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 93 ∧ machine.reject.val = 94 ∧
      (∀ q, (inBoot q).val = q.val) ∧ (∀ q, (inBoot q).val < 9) ∧
      (∀ q, (inChain q).val = 9 + q.val) ∧ (∀ q, 9 ≤ (inChain q).val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inFirst q)).val
        = 9 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain q)).val
        = 27 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inSecond q))).val
        = 27 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inChain q))).val
        = 41 + q.val) ∧
      Function.Injective inBoot ∧ Function.Injective inChain ∧
      (∀ p q, inBoot p ≠ inChain q) ∧
      route FixedGammaTerminatorScratchBootstrap.qTerm =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTerminatorScratchBootstrap.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTerminatorScratchBootstrap.qTerm →
        q ≠ FixedGammaTerminatorScratchBootstrap.qReject → route q = inBoot q) ∧
      (∀ q s, machine.step (inBoot q) s =
        (route (FixedGammaTerminatorScratchBootstrap.machine.step q s).1,
          (FixedGammaTerminatorScratchBootstrap.machine.step q s).2.1,
          (FixedGammaTerminatorScratchBootstrap.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain
            (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inBoot FixedGammaTerminatorScratchBootstrap.qScanLeft).val = 6 ∧
      (inBoot FixedGammaTerminatorScratchBootstrap.qTerm).val = 7 ∧
      (inChain
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start).val
        = 9 ∧
      machine.step (inBoot FixedGammaTerminatorScratchBootstrap.qScanLeft) none =
        (inChain
            FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
          some true, .stay) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTerminatorScratchBootstrap.machine.seq_pins
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun q => q.isLt,
    fun _ => rfl, fun _ => Nat.le_add_right _ _, fun _ => rfl, fun q => ?_, fun q => ?_,
    fun q => ?_, hli, hri, hne, hra, hrr, hrw,
    fun q s => FixedGammaTerminatorScratchBootstrap.machine.seq_step_left
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTerminatorScratchBootstrap.machine.seq_step_right
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    fun q s => FixedGammaTerminatorScratchBootstrap.machine.seq_step_eq_rawStep
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine q s,
    rfl, rfl, rfl, rfl⟩
  · show 9 + (18 + q.val) = 27 + q.val; omega
  · show 9 + (18 + q.val) = 27 + q.val; omega
  · show 9 + (18 + (14 + q.val)) = 41 + q.val; omega

/-- The start, pinned: G2p-a's `startConfig` routed into the composed control — the same head and
tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTerminatorScratchBootstrap.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The chained clock, pinned: G3c's sum prefixed by G2p-a's first arrival, its closed value — the
bootstrap clock needs no case split on the width — and, on `2 ≤ zeros`, its full expansion into the
bootstrap, the first payload digit, the second payload digit, the marker preamble, the payload loop
and G2x. -/
theorem clock_pins (N zeros d v : Nat) :
    bootChainClock N zeros d v =
        FixedGammaTerminatorScratchBootstrap.exactClock N zeros +
          firstChainClock N zeros d v ∧
      bootChainClock N zeros d v = 2 * N - 11 - zeros + firstChainClock N zeros d v ∧
      (2 ≤ zeros → bootChainClock N zeros d v =
        2 * N - 11 - zeros +
          (2 * N + zeros - 6 +
            (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))) := by
  refine ⟨rfl, rfl, fun hz => ?_⟩
  show 2 * N - 11 - zeros + firstChainClock N zeros d v = _
  rw [(FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    N zeros d v).2.2 hz]

/-! ### The executed handoff -/

/-- **H12 fires at whatever time G2p-a first accepts, and it costs nothing.**  The width-free core:
given that the bootstrap run is in its `qTerm` at `T`, in neither terminal before `T`, and that `T`
is at or below G2p-a's length-only deadline `deadline N = 2 * N`, the composed run out of
`startConfig` is in neither composed verdict before `T`, is G2p-a's own run routed up to and
including `T`, at exactly `T` **is** G3c's landed `startConfig B x w` re-embedded, and takes G3c
steps afterwards.  The deadline premise is what identifies G2p-a's configuration at the first
arrival with its configuration at the deadline that G2p-b's `startConfig`, and through it G3c's,
retags; it is used in that direction only.  `T` occurs in the statement only; no row of any of the
seven tables mentions it. -/
private theorem handoff_of_arrival {a m B : Nat} {x : Bitstring a} {w : Bitstring m} {T : Nat}
    (hdq : (FixedGammaTerminatorScratchBootstrap.machine.run T
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).state =
      FixedGammaTerminatorScratchBootstrap.machine.accept)
    (hwork : ∀ t, t < T → (FixedGammaTerminatorScratchBootstrap.machine.run t
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).state ≠
      FixedGammaTerminatorScratchBootstrap.machine.accept)
    (hle : T ≤ FixedGammaTerminatorScratchBootstrap.deadline (a + m)) :
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTerminatorScratchBootstrap.machine.run t
            (FixedGammaTerminatorScratchBootstrap.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) := by
  intro c
  have hstart : FixedGammaTerminatorScratchBootstrap.machine.run
      (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w) =
      FixedGammaTerminatorScratchBootstrap.machine.run T
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w) :=
    FixedGammaTerminatorScratchBootstrap.machine.run_accept_of_le _ hdq hle
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTerminatorScratchBootstrap.machine.run t
          (FixedGammaTerminatorScratchBootstrap.startConfig B x w)) :=
    FixedGammaTerminatorScratchBootstrap.machine.seq_run_left
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine _ hwork
  have hcfg :
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w =
      ⟨FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedGammaTerminatorScratchBootstrap.machine.run T
          (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).head,
        (FixedGammaTerminatorScratchBootstrap.machine.run T
          (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).tape⟩ := by
    rw [← hstart]
    rfl
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run s
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) := by
    intro s
    rw [hcfg]
    exact FixedGammaTerminatorScratchBootstrap.machine.seq_handoff
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine _ hwork hdq s
  have hT : machine.run T c =
      FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          B x w) :=
    hsuffix 0
  have hTs : (machine.run T c).state =
      inChain
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start := by
    rw [hT]; rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]; decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]; decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **H12 at every decoded width, with no room premise.**  On a matching tag and a decoded `zeros`,
write `T = FixedGammaTerminatorScratchBootstrap.exactClock (a+m) zeros = 2 * (a+m) - 11 - zeros`.
Out of `startConfig`: before `T` the composed control is in neither verdict; up to and including
`T` the composed configuration is G2p-a's own, routed; at exactly `T` it **is** G3c's landed
`startConfig B x w`, re-embedded — the head and tape G2p-b's first-payload phase retags at G2p-a's
length-only deadline `deadline (a+m) = 2*(a+m)`, identified through G2p-a's persistence from `T` to
that deadline; and every further step is a G3c step.  The final conjunct rests on
`strict_first_terminal` together with the no-early-accept premise — `qTerm` is entered for the
*first* time at `T`, so the routed edge fires then and not earlier — which persistence alone would
not give.  Width zero is **not** excluded: it
differs only in the incoming dispatcher head (`7` against `6`), which G2p-a's own trace absorbs, so
this one statement covers it; an accepted parsed target reaches only the sub-case `2 ≤ zeros`.  No
room premise appears, because G2p-a needs none: `tapeLength` allocates the scratch cell `a+m+1` at
every budget, including `B = 0`.  The fourth conjunct is a simulation equality and needs no marker,
loop, decrement, countdown or budget premise: it holds even where the budget leaves the tail
unfinished. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let T := FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTerminatorScratchBootstrap.machine.run t
            (FixedGammaTerminatorScratchBootstrap.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) :=
  handoff_of_arrival (FixedGammaTerminatorScratchBootstrap.strict_first_terminal x w htag hg).2
    (fun t ht =>
      ((FixedGammaTerminatorScratchBootstrap.strict_first_terminal x w htag hg).1 t ht).1)
    (FixedGammaTerminatorScratchBootstrap.exactClock_le_deadline _ _)

/-- **What the switch hands over is exactly what the next phase reads.**  At `T`, G2p-a's first
arrival, the composed configuration's head is the restored gamma terminator cell `8 + zeros` and
its whole tape is G2p-a's `scratchTape B x w` — `contentTape` with `true` at the scratch cell
`a+m+1` and nothing else changed — and those are *the same two projections* that G2p-b's own
`startConfig` carries, so the two are equal head and tape.  This is the semantic dependency H12
must preserve: no reinterpretation, no re-derived width, no second decoding.  It is a statement
about the two configurations only; it claims nothing about what G2p-b then computes. -/
theorem handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let T := FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros
    let e := machine.run T (startConfig B x w)
    let p := FixedGammaTargetFirstPayload.startConfig B x w
    e.head.val = 8 + zeros ∧
      e.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      p.head.val = 8 + zeros ∧
      p.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      e.head = p.head ∧ e.tape = p.tape := by
  obtain ⟨-, -, hT, -⟩ := handoff_exact (B := B) x w htag hg
  obtain ⟨-, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline (B := B) x w htag hg
  have hhe : (machine.run (FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros)
      (startConfig B x w)).head = (FixedGammaTargetFirstPayload.startConfig B x w).head := by
    rw [hT]; rfl
  have hte : (machine.run (FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros)
      (startConfig B x w)).tape = (FixedGammaTargetFirstPayload.startConfig B x w).tape := by
    rw [hT]; rfl
  exact ⟨by rw [hhe]; exact hh, by rw [hte]; exact ht, hh, ht, hhe, hte⟩

/-- **The concrete exact run: the scratch bootstrap, H12, the first payload digit, H13, the second
payload digit, H14, the markers, H15, the loop, H16, the decrement, H17, the countdown, one
machine.**  Under G2u's, G2y's, G2z's, G3a's and G3c's **seven** hypotheses — a matching tag, a
decoded `2 ≤ zeros`, the lane cap `v ≤ F`, the room `zeros + 2 + F ≤ a + B`, and a `v` whose digit
`zeros - j` is G2q's decremented register digit `j` with no digit above `zeros` — after exactly
`bootChainClock (a+m) zeros d v` steps out of `startConfig` the composed machine is in its accept
(the countdown's `qDone`) on the separator blank `a+m+2+zeros` with tape
`loopTape B x w zeros 0 v`, persisting at every later time.  That one tape equality already
determines the cleared register, the `v` marks and the blanks beyond, which G2u and G2x state cell
by cell; no cell-by-cell conjunct is restated here.  The first
`FixedGammaTerminatorScratchBootstrap.exactClock (a+m) zeros` steps are G2p-a's, H12 fires at its
first arrival, and the remaining `firstChainClock (a+m) zeros d v` steps are G3c's out of the
configuration `handoff_exact` identifies.  No eighth hypothesis: G2p-a's phase needs neither room
nor a width shape.  `v` is universally quantified and nothing in pnp3 supplies it; persistence is
not first arrival of the composed accept; `startConfig` still embeds every earlier phase as a
retag; reaching the composed accept is neither halting on a raw input nor language acceptance. -/
theorem scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := bootChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact (B := B) x w htag hg
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg hzeros hfence hroom hv hhigh
  have hE : machine.run (bootChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (firstChainClock (a + m) zeros (borrow x w zeros) v)
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) :=
    hsuffix (firstChainClock (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (bootChainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = bootChainClock (a + m) zeros (borrow x w zeros) v +
      (t - bootChainClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject, executed one block further left.**  A matching tag with no decoded width —
the G2m dispatcher stopped at the blank boundary cell `a + m`, so the bootstrap's first read is a
blank: G2p-a rejects in one step — its own landed `malformed_exact`, whose first-arrival companion
is not needed, since both machines absorb a rejection — and the generic rejecting handoff carries
that verdict into the composed control, so from step one on the composed machine is in the composed
reject — index `94`, not G2p-a's own `qReject` at index `8` — at the boundary head `a + m` on the
unchanged content tape.  It needs no room premise.  It is **not** a converse — nothing here says
the composed reject implies a malformed gamma — it states no `RejectsAt`, and it characterises no
parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTerminatorScratchBootstrap.malformed_exact (B := B) x w htag hg 1 le_rfl
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedGammaTerminatorScratchBootstrap.machine.run 1
          (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).head,
        (FixedGammaTerminatorScratchBootstrap.machine.run 1
          (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).tape⟩ := by
    have h := FixedGammaTerminatorScratchBootstrap.machine.seq_reject_handoff
      FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w) (T := 1) hq (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  exact ⟨by rw [hrun], by rw [hrun]; exact hh, by rw [hrun]; exact ht⟩

end
  Pnp3.Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
