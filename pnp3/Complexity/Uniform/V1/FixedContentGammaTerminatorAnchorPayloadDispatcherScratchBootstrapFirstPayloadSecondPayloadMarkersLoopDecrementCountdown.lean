import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The gamma terminator, the gamma anchor, the payload dispatcher, the scratch bootstrap, the first
payload digit, the second payload digit, the loop markers, the payload loop, the decrement and the
countdown as one machine (Part A G3i)

**No new table row.**  `machine` is `FixedContentGammaTerminator.machine.seq
FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`:
G2's fixed 3-state, 9-row gamma-terminator scan on the left block `[0, 3)` and the whole landed G3h
129-state composite on the right block `[3, 132)`, one closed 132-state, 396-row table whose every
row is a row of one of those ten tables with its target routed.  Write `N = a + m` and
`d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Nine executed handoffs.**  H9 — G2's gamma terminator into G2a's gamma anchor — is the newly
executed one, and it has exactly **one** live routed row: `qScan` on `some true`, the terminator's
only row targeting its accept outside the accept's own absorbing three (`verdict_rows_unique`), which
`seq` retargets to the right block's start `tailStart` at index `3`, writing `some true` and staying,
in that same transition and at no cost.  Outside the reject's own absorbing three, exactly one
further terminator row — `qScan` on the blank, also proved unique — routes to the composed reject
`131`, and the one remaining working row `qScan` on `some false` stays inside the left block.  The
left copies of the two terminator verdicts are dead: no composed row targets either
(`table_and_resource_pins`).  H10 (`6 → 9`, the anchor's `qReturn` on `some true`) and H11 (six rows
inside `[9, 37)`, all into `37`) to H17 (`118 → 121`) are inherited from G3h, its indices shifted by
three and located by `(inTail q).val = 3 + q.val` with the universal right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The terminator has exactly
two absorbing states, `qAccept` and `qReject` — its raw states `1` and `2`, three rows each — so the
landed `seq` routes both and no `mergeAccept` is needed, as for H10 and unlike H11.  Its strict
first arrival was *not* exported in the shape `seq` consumes, and `terminator_first_arrival` and
`terminator_reject_arrival` derive it here from the landed `exact_terminal_contract`, with no room
premise: on a matching tag with a decoded width the terminator is in neither verdict before
`switchTime zeros = zeros + 1` and in `finalConfig` at it, and on a matching tag with no decoded
width it is in neither verdict before its length-only deadline `N - 7` and in `finalConfig` — its
`qReject` — at it.  Its endpoint is compatible with the right block's start by construction: G2a's
`startConfig` retags the terminator's `finalConfig` itself, which `terminator_first_arrival` shows
*is* the terminator's run at `switchTime zeros`, so the switch hands over exactly the head and tape
the right block's own `startConfig` carries — the unmarked content tape, on the gamma terminator cell
`8 + zeros`.  The switch time is width-dependent but not path-dependent, and at most the
terminator's own length-only deadline `N - 7`: it adds a linear prefix to the composed clock and no
new room premise.

**The composed run.**  `handoff_exact` takes the matching tag and the decoded width — two
hypotheses, no room, no budget: the run out of `startConfig` is in neither composed verdict at any
time up to and including `zeros + 1` (at the switch time itself the control is `tailStart`, so the
bound is `≤`), is G2's own run routed at every such time, at exactly `zeros + 1` **is** G3h's landed
`startConfig B x w` re-embedded, and every later step is a G3h step.  `handoff_endpoint_pins` reads
that switch configuration back as G2a's own `startConfig` projections — the control as `tailStart`,
the head and the whole tape as G2a's own — and records that cell `7` is *not* yet blank there: the
anchor's recoverable marker is written later, inside the right block.  `tagged_inherited_switch` locates the inherited H10 at
`zeros + 1 + (2 * zeros + 5)` inside this machine, `tagged_inherited_dispatcher_switch` the
inherited H11 at `zeros + 1 + (2 * zeros + 5) + C`, and the drained theorem lands the composed
accept `130` at exactly
`terminatorChainClock C N zeros d v = zeros + 1 + anchorChainClock C N zeros d v` under G3h's eight
hypotheses unchanged.  On a matching tag whose physical suffix holds **no** gamma terminator the
terminator rejects at exactly its deadline `N - 7` and not before — the anchor never runs — and
`malformed_reject_handoff` lands the composed reject `131` from that deadline on, forward direction
only.  Unlike G3h's routed reject this one does carry the tag premise: every run theorem of the
terminator phase is tag-gated, because a mismatched tag leaves its `startConfig` retagging the tag
gate's *rejecting* endpoint, whose head this phase does not characterise.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
eight handoffs before H9 remain proof-level identifications (G2's `startConfig` retags the actual
tag-gate `finalConfig`, which `handoff_pins` records), no raw-input `initialConfig` is executed, and
no clock here counts a step of any earlier phase.  No **first arrival** of the composed accept (the
arrivals proved are the terminator's and, as a hypothesis, the dispatcher's, both inside their own
blocks); the **fence** (all ten tables are uncapped); every **converse**; a **footprint** theorem;
and the pnp4 bridge, not built here, the standalone phases' pnp4 semantics being unchanged.  The
composed `accept` is the countdown's phase-local `qDone`: reaching it out of a retagged actual prior
endpoint is neither halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or `ContentVerifierBridge` is stated.  The table is fixed and complete
but not claimed state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedContentGammaTerminator (qScan gammaZeros? terminalIndex)
open FixedContentGammaAnchor (successTime markedTape)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (dispatcherChainClock)
open FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (anchorChainClock
    anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained)

/-- The composed machine: G2's gamma terminator, then G3h's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedContentGammaTerminator.machine.seq
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- A terminator state in the composed control, at its own index. -/
def inTerminator (q : Fin FixedContentGammaTerminator.stateCount) : Fin machine.stateCount :=
  FixedContentGammaTerminator.machine.seqLeft
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- A G3h state in the composed control, shifted past the three terminator states. -/
def inTail
    (q : Fin
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedContentGammaTerminator.machine.seqRight
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- The routed target of a terminator row: `qAccept` becomes G3h's start, `qReject` the composed
reject, `qScan` itself. -/
def route (q : Fin FixedContentGammaTerminator.stateCount) : Fin machine.stateCount :=
  FixedContentGammaTerminator.machine.seqRoute
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- G3h's start in the composed control, index `3`: the target of the one live routed row. -/
def tailStart : Fin machine.stateCount :=
  inTail
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start

/-- G2's own `startConfig` — the retagged *actual* tag-gate endpoint — routed into the composed
control.  Still a phase-local retag, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedContentGammaTerminator.machine.seqEmbedRouted
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedContentGammaTerminator.startConfig B x w)

/-- The terminator's strict first arrival on a decoded width: one step per zero of the run, plus the
step that reads the terminator cell itself. -/
def switchTime (zeros : Nat) : Nat := zeros + 1

/-- Exact cost of the terminator phase followed by the whole of G3h: the terminator's width-only
first arrival `zeros + 1`, plus the anchor's width-only first arrival `2 * zeros + 5`, plus the
dispatcher's input-dependent first arrival `C`, plus G3e's `bootChainClock`.  All three handoffs
cost nothing. -/
def terminatorChainClock (C N zeros d v : Nat) : Nat :=
  switchTime zeros + anchorChainClock C N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the state and row counts, the terminator's start and verdicts, the
distinguished states with their indices, the block injections with their offsets and disjointness,
`tailStart` at `3`, the routing cases, every left row as the routed terminator row, every right row
as the G3h row, the public step against the composed raw table, **every** one of the terminator's
nine rows in the composed control — the one live routed row `qScan` on `some true`, the one routed
reject `qScan` on the blank, the one working row `qScan` on `some false` and the two dead verdict
copies, three rows each — and that no **left-block** row targets either dead copy, which together
with the right-block row equation and `inTerminator p ≠ inTail q`, both conjuncts above, is every
composed row.  Inherited rows are not restated: the right-block row equation transports every G3h
row verbatim. -/
theorem table_and_resource_pins :
    machine.stateCount = 132 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 396 ∧
      FixedContentGammaTerminator.machine.start = qScan ∧
      FixedContentGammaTerminator.machine.accept = FixedContentGammaTerminator.qAccept ∧
      FixedContentGammaTerminator.machine.reject = FixedContentGammaTerminator.qReject ∧
      machine.start = route qScan ∧ machine.start = inTerminator qScan ∧
      machine.accept =
        inTail
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inTail
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 130 ∧ machine.reject.val = 131 ∧
      (∀ q, (inTerminator q).val = q.val) ∧ (∀ q, (inTerminator q).val < 3) ∧
      (∀ q, (inTail q).val = 3 + q.val) ∧ (∀ q, 3 ≤ (inTail q).val) ∧
      Function.Injective inTerminator ∧ Function.Injective inTail ∧
      (∀ p q, inTerminator p ≠ inTail q) ∧
      tailStart =
        inTail
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      tailStart.val = 3 ∧ route FixedContentGammaTerminator.qAccept = tailStart ∧
      route FixedContentGammaTerminator.qReject = machine.reject ∧
      (∀ q, q ≠ FixedContentGammaTerminator.qAccept → q ≠ FixedContentGammaTerminator.qReject →
        route q = inTerminator q) ∧
      (∀ q s, machine.step (inTerminator q) s =
        (route (FixedContentGammaTerminator.machine.step q s).1,
          (FixedContentGammaTerminator.machine.step q s).2.1,
          (FixedContentGammaTerminator.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail
            (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inTerminator qScan) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inTerminator qScan) (some false) = (inTerminator qScan, some false, .right) ∧
      machine.step (inTerminator qScan) none = (machine.reject, none, .stay) ∧
      (∀ s, machine.step (inTerminator FixedContentGammaTerminator.qAccept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inTerminator FixedContentGammaTerminator.qReject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inTerminator q) s).1 ≠ inTerminator FixedContentGammaTerminator.qAccept ∧
        (machine.step (inTerminator q) s).1 ≠ inTerminator FixedContentGammaTerminator.qReject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedContentGammaTerminator.machine.seq_pins
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun q => q.isLt, fun _ => rfl, fun _ => Nat.le_add_right _ _,
    hli, hri, hne, rfl, rfl, hra, hrr, hrw,
    fun q s => FixedContentGammaTerminator.machine.seq_step_left
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentGammaTerminator.machine.seq_step_right
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentGammaTerminator.machine.seq_step_eq_rawStep
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · decide

/-- **The terminator has exactly one live row targeting each of its verdicts.**  Over all three
states and all three symbols, with the accept's own absorbing row excluded, a target of
`FixedContentGammaTerminator.machine.accept` forces `qScan` on `some true`; with the reject's own
absorbing row excluded, a target of `FixedContentGammaTerminator.machine.reject` forces `qScan` on
the blank.  So H9 has exactly one live routed row and the composed machine exactly one live routed
reject row.  The excluded rows are the dead left copies' own, which `seq` routes to `tailStart` and
to the composed reject and no composed row ever enters. -/
theorem verdict_rows_unique (q : Fin FixedContentGammaTerminator.stateCount) (s : Option Bool) :
    (q ≠ FixedContentGammaTerminator.qAccept →
      (FixedContentGammaTerminator.machine.rawStep q s).1 =
        FixedContentGammaTerminator.machine.accept → q = qScan ∧ s = some true) ∧
    (q ≠ FixedContentGammaTerminator.qReject →
      (FixedContentGammaTerminator.machine.rawStep q s).1 =
        FixedContentGammaTerminator.machine.reject → q = qScan ∧ s = none) := by
  revert s
  revert q
  decide

/-- **The start is the retagged actual tag-gate endpoint, not a raw input.**  On a matching tag the
tag gate's run at its own deadline `3N + 7` is its `finalConfig`, on cell `8` over the unchanged
`contentTape`; G2's `startConfig` is that configuration retagged; and this slice's `startConfig` is
*that* one routed into the composed control — the same head and tape, the composed start `0` as
control.  No `initialConfig` and no raw pair input appears, and neither retag costs a step. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let g := FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m)
      (FixedContentTagGate.startConfig B x w)
    let p := FixedContentGammaTerminator.startConfig B x w
    let c := startConfig B x w
    g = FixedContentTagGate.finalConfig B x w ∧
      p = FixedContentGammaTerminator.retag g ∧
      c =
        FixedContentGammaTerminator.machine.seqEmbedRouted
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          p ∧
      c.state = machine.start ∧ c.state = inTerminator qScan ∧
      c.head = g.head ∧ c.tape = g.tape ∧ c.head.val = 8 ∧
      c.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hfin, -, hhead, htape, hretag, -, hph, hpt⟩ :=
    FixedContentGammaTerminator.handoff_exact (B := B) x w htag
  have hh : (startConfig B x w).head =
      (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m)
        (FixedContentTagGate.startConfig B x w)).head := hph
  have ht : (startConfig B x w).tape =
      (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m)
        (FixedContentTagGate.startConfig B x w)).tape := hpt
  exact ⟨hfin, hretag, rfl, rfl, rfl, hh, ht, by rw [hh]; exact hhead, by rw [ht]; exact htape⟩

/-- The chained clock, pinned: G3h's sum prefixed by the terminator's width-only first arrival
`zeros + 1`, and on `2 ≤ zeros` its full expansion.  `C` has no closed form in `N`. -/
theorem clock_pins (C N zeros d v : Nat) :
    terminatorChainClock C N zeros d v = switchTime zeros + anchorChainClock C N zeros d v ∧
      terminatorChainClock C N zeros d v =
        zeros + 1 + (2 * zeros + 5 + (C + bootChainClock N zeros d v)) ∧
      (2 ≤ zeros → terminatorChainClock C N zeros d v =
        zeros + 1 + (2 * zeros + 5 + (C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))))))) := by
  refine ⟨rfl, rfl, fun hz => ?_⟩
  show switchTime zeros + anchorChainClock C N zeros d v = _
  rw [(FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    C N zeros d v).2.2 hz]
  rfl

/-! ### The terminator's arrivals, in the shape the composition consumes -/

/-- **The terminator's strict first successful arrival.**  On a matching tag with a decoded width it
is in neither verdict at every time before `switchTime zeros = zeros + 1`, at that time its run
**is** its `finalConfig` and its control its accept, and that time is at most its length-only
deadline `N - 7`.  Derived from the landed `exact_terminal_contract`, which does not carry the
`state = accept` form `UniformTM.seq_handoff` consumes; no room premise. -/
theorem terminator_first_arrival {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    (∀ t, t < switchTime zeros →
        (FixedContentGammaTerminator.machine.run t
          (FixedContentGammaTerminator.startConfig B x w)).state ≠
            FixedContentGammaTerminator.machine.accept ∧
        (FixedContentGammaTerminator.machine.run t
          (FixedContentGammaTerminator.startConfig B x w)).state ≠
            FixedContentGammaTerminator.machine.reject) ∧
      FixedContentGammaTerminator.machine.run (switchTime zeros)
        (FixedContentGammaTerminator.startConfig B x w) =
          FixedContentGammaTerminator.finalConfig B x w ∧
      (FixedContentGammaTerminator.machine.run (switchTime zeros)
        (FixedContentGammaTerminator.startConfig B x w)).state =
          FixedContentGammaTerminator.machine.accept ∧
      switchTime zeros ≤ FixedContentGammaTerminator.deadline a m := by
  unfold switchTime
  obtain ⟨hsome, -⟩ := FixedContentGammaTerminator.exact_terminal_contract (B := B) x w htag
  obtain ⟨hno, hend, hle⟩ := hsome zeros hg
  refine ⟨hno, hend, ?_, hle⟩
  rw [hend]
  simp [FixedContentGammaTerminator.finalConfig, FixedContentGammaTerminator.machine, hg]

/-- **The terminator's strict first rejecting arrival.**  On a matching tag whose physical suffix
holds no gamma terminator it is in neither verdict at every time before its length-only deadline
`N - 7`, and at that deadline its run **is** its `finalConfig` and its control its reject.  Derived
from the same landed contract; the rejection time is length-only, not width-dependent. -/
theorem terminator_reject_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    (∀ t, t < FixedContentGammaTerminator.deadline a m →
        (FixedContentGammaTerminator.machine.run t
          (FixedContentGammaTerminator.startConfig B x w)).state ≠
            FixedContentGammaTerminator.machine.accept ∧
        (FixedContentGammaTerminator.machine.run t
          (FixedContentGammaTerminator.startConfig B x w)).state ≠
            FixedContentGammaTerminator.machine.reject) ∧
      FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m)
        (FixedContentGammaTerminator.startConfig B x w) =
          FixedContentGammaTerminator.finalConfig B x w ∧
      (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m)
        (FixedContentGammaTerminator.startConfig B x w)).state =
          FixedContentGammaTerminator.machine.reject := by
  obtain ⟨-, hnone⟩ := FixedContentGammaTerminator.exact_terminal_contract (B := B) x w htag
  obtain ⟨hno, hend⟩ := hnone hg
  refine ⟨hno, hend, ?_⟩
  rw [hend]
  simp [FixedContentGammaTerminator.finalConfig, FixedContentGammaTerminator.machine, hg]

/-- G2a's `startConfig` is the terminator's run at its **first arrival**, retagged: the anchor
retags the terminator's `finalConfig`, which is that run.  This is the semantic dependency H9 has to
respect; it executes nothing. -/
theorem anchor_start_at_first_arrival {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    FixedContentGammaAnchor.startConfig B x w =
      FixedContentGammaAnchor.retag
        (FixedContentGammaTerminator.machine.run (switchTime zeros)
          (FixedContentGammaTerminator.startConfig B x w)) := by
  obtain ⟨-, hend, -, -⟩ := terminator_first_arrival (B := B) x w htag hg
  unfold FixedContentGammaAnchor.startConfig
  rw [hend]

/-! ### The executed handoff -/

/-- **H9 fires when the terminator first reads the gamma terminator cell, and it costs nothing.**
On a matching tag with a decoded width — two hypotheses, no room premise — the run out of
`startConfig` is in neither composed verdict at any time up to and including `zeros + 1` (at the
switch time itself the control is `tailStart`, so the bound is `≤`), is G2's own run routed at every
such time — same head and whole tape — at exactly `zeros + 1` **is** G3h's landed `startConfig
B x w` re-embedded, and runs G3h on from there. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let c := startConfig B x w
    (∀ t, t ≤ switchTime zeros →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime zeros → machine.run t c =
        FixedContentGammaTerminator.machine.seqEmbedRouted
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaTerminator.machine.run t
            (FixedContentGammaTerminator.startConfig B x w))) ∧
      machine.run (switchTime zeros) c =
        FixedContentGammaTerminator.machine.seqEmbedRight
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (switchTime zeros + s) c =
        FixedContentGammaTerminator.machine.seqEmbedRight
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) := by
  intro c
  obtain ⟨hno, hend, hacc, -⟩ := terminator_first_arrival (B := B) x w htag hg
  have hwork : ∀ t, t < switchTime zeros →
      (FixedContentGammaTerminator.machine.run t
        (FixedContentGammaTerminator.startConfig B x w)).state ≠
          FixedContentGammaTerminator.machine.accept := fun t ht => (hno t ht).1
  have hcfg :
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
        B x w =
      ⟨FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedContentGammaTerminator.machine.run (switchTime zeros)
          (FixedContentGammaTerminator.startConfig B x w)).head,
        (FixedContentGammaTerminator.machine.run (switchTime zeros)
          (FixedContentGammaTerminator.startConfig B x w)).tape⟩ := by
    exact Config.ext_parts rfl (congrArg Config.head hend).symm (congrArg Config.tape hend).symm
  have hleft :=
    FixedContentGammaTerminator.machine.seq_run_left
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaTerminator.startConfig B x w) hwork
  have hsuffix : ∀ s, machine.run (switchTime zeros + s) c =
      FixedContentGammaTerminator.machine.seqEmbedRight
        FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          s
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) := by
    intro s
    rw [hcfg]
    exact FixedContentGammaTerminator.machine.seq_handoff
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaTerminator.startConfig B x w) hwork hacc s
  have hC : machine.run (switchTime zeros) c =
      FixedContentGammaTerminator.machine.seqEmbedRight
        FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          B x w) := hsuffix 0
  have hCs : (machine.run (switchTime zeros) c).state = tailStart := by
    rw [hC]; rfl
  have hCa : (machine.run (switchTime zeros) c).state ≠ machine.accept := by
    rw [hCs]; decide
  have hCr : (machine.run (switchTime zeros) c).state ≠ machine.reject := by
    rw [hCs]; decide
  exact ⟨UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩

/-- **What the switch hands over is exactly what G2a reads.**  At the terminator's first arrival
`zeros + 1`: the composed control is G3h's start `3`, the composed head and whole tape are *the
same* projections G2a's own `startConfig` carries, the head is the gamma terminator cell
`8 + zeros`, the tape is the **unmarked** `contentTape`, and cell `7` is not blank there — the
anchor's recoverable marker is written later, inside the right block. -/
theorem handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime zeros) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) := by
  obtain ⟨-, -, hC, -⟩ := handoff_exact x w htag hg
  have hlt := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
  have hhead : (machine.run (switchTime zeros) (startConfig B x w)).head =
      (FixedContentGammaAnchor.startConfig B x w).head := congrArg Config.head hC
  have htape : (machine.run (switchTime zeros) (startConfig B x w)).tape =
      (FixedContentGammaAnchor.startConfig B x w).tape := congrArg Config.tape hC
  have hheadval : (machine.run (switchTime zeros) (startConfig B x w)).head.val = 8 + zeros := by
    rw [hhead]
    show min (terminalIndex (Fin.append x w)) (a + m) = 8 + zeros
    unfold FixedContentGammaTerminator.terminalIndex
    rw [hg]
    exact Nat.min_eq_left (Nat.le_of_lt hlt)
  have htapeval : (machine.run (switchTime zeros) (startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w := htape
  refine ⟨congrArg Config.state hC, hhead, htape, hheadval, htapeval, fun i hi => ?_⟩
  rw [htapeval]
  simp [FixedPairContentMarkerErase.contentTape, hi, show (7 : Nat) < a + m by omega]

/-! ### The inherited switches and the composed run -/

/-- **The inherited H10 fires inside this machine at `zeros + 1 + (2 * zeros + 5)`.**  The
terminator's own steps counted first, the composed control is G2k's payload-dispatcher start at
index `9` — G3h's `6` shifted by the three terminator states — on exactly the head and tape G2k's
landed `startConfig` carries, that tape being the anchor's `markedTape` with cell `7` now blank: the
marker the anchor writes with the composed table's own row. -/
theorem tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime zeros + successTime zeros) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 9 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg
  obtain ⟨hs, hhead, htape, hhv, htv, hseven, -⟩ :=
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      (B := B) x w htag hg
  have hrun := hsuffix (successTime zeros)
  have hstate : (machine.run (switchTime zeros + successTime zeros) (startConfig B x w)).state =
      inTail
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (successTime zeros)
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)).state := by
    rw [hrun]; rfl
  refine ⟨by rw [hstate, hs]; decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; exact hhead
  · rw [hrun]; exact htape
  · rw [hrun]; exact hhv
  · rw [hrun]; exact htv
  · rw [hrun]; exact hseven

/-- **The inherited H11 fires inside this machine at `zeros + 1 + (2 * zeros + 5) + C`.**  There is
a strict first dispatcher arrival `C` at or below G2m's deadline, in one of the two success
endpoints, and at that time the composed control is G2p-a's start at index `37`, on exactly the head
and tape G2p-a's landed `startConfig` carries.  `C` is produced, not chosen. -/
theorem tagged_inherited_dispatcher_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ FixedGammaPayloadDispatcherDeadline.deadline (a + m) ∧
      StrictFirstTerminalAt B x w C q ∧
      (q = FixedGammaPayloadDispatcher.qAllZero ∨ q = FixedGammaPayloadDispatcher.qHasOne) ∧
      (machine.run (switchTime zeros + (successTime zeros + C)) (startConfig B x w)).state.val =
          37 ∧
      (machine.run (switchTime zeros + (successTime zeros + C)) (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (switchTime zeros + (successTime zeros + C)) (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg
  obtain ⟨C, q, hle, hfirst, hq, hstate, hhead, htape⟩ :=
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tagged_inherited_switch
      (B := B) x w htag hg
  have hrun := hsuffix (successTime zeros + C)
  have hval : (machine.run (switchTime zeros + (successTime zeros + C))
      (startConfig B x w)).state.val =
      3 +
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (successTime zeros + C)
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)).state.val := by
    rw [hrun]; rfl
  refine ⟨C, q, hle, hfirst, hq, ?_, ?_, ?_⟩
  · rw [hval, hstate]
  · rw [hrun]; exact hhead
  · rw [hrun]; exact htape

/-- **The concrete exact run: the gamma terminator, H9, the gamma anchor, H10, the payload
dispatcher, H11, the scratch bootstrap, H12, the first and second payload digits, H13 and H14, the
markers, H15, the loop, H16, the decrement, H17 and the countdown, one machine.**  Under G3h's
**eight** hypotheses unchanged, after exactly `terminatorChainClock C (a+m) zeros d v` steps the
composed machine is in its accept, the countdown's `qDone`, on the separator blank `a+m+2+zeros`
with tape `loopTape B x w zeros 0 v`, persisting.  `v` is universally quantified and unsupplied;
persistence is not first arrival of the composed accept. -/
theorem terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := terminatorChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg
  obtain ⟨he1, he2, he3, -⟩ :=
    anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (terminatorChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedContentGammaTerminator.machine.seqEmbedRight
        FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (anchorChainClock C (a + m) zeros (borrow x w zeros) v)
          (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) :=
    hsuffix (anchorChainClock C (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (terminatorChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = terminatorChainClock C (a + m) zeros (borrow x w zeros) v +
      (t - terminatorChainClock C (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject.**  On a matching tag with no decoded width the composed run is in neither
verdict before the terminator's length-only deadline `N - 7`, and from that deadline on it is in the
composed reject — index `131`, not G2's `qReject` at `2` — on the blank boundary cell `a + m`, over
the unchanged content tape: the anchor never runs.  The tag premise is load-bearing here, unlike in
G3h's routed reject: a mismatched tag leaves G2's `startConfig` retagging the tag gate's *rejecting*
endpoint, whose head this phase does not characterise.  **Not** a converse; it characterises no
parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < FixedContentGammaTerminator.deadline a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, FixedContentGammaTerminator.deadline a m ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) := by
  intro c
  obtain ⟨hno, hend, hrej⟩ := terminator_reject_arrival (B := B) x w htag hg
  obtain ⟨-, -, -, -, -, -, -, -, hne, -, -, hrw⟩ :=
    FixedContentGammaTerminator.machine.seq_pins
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  have hwork : ∀ t, t < FixedContentGammaTerminator.deadline a m →
      (FixedContentGammaTerminator.machine.run t
        (FixedContentGammaTerminator.startConfig B x w)).state ≠
          FixedContentGammaTerminator.machine.accept := fun t ht => (hno t ht).1
  have hleft :=
    FixedContentGammaTerminator.machine.seq_run_left
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaTerminator.startConfig B x w) hwork
  have hpre : ∀ t, t < FixedContentGammaTerminator.deadline a m →
      (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject := by
    intro t ht
    have h1 : machine.run t c =
        FixedContentGammaTerminator.machine.seqEmbedRouted
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaTerminator.machine.run t
            (FixedContentGammaTerminator.startConfig B x w)) := hleft t (Nat.le_of_lt ht)
    have hst : (machine.run t c).state =
        FixedContentGammaTerminator.machine.seqLeft
          FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaTerminator.machine.run t
            (FixedContentGammaTerminator.startConfig B x w)).state := by
      rw [h1, UniformTM.seqEmbedRouted_state]
      exact hrw _ (hno t ht).1 (hno t ht).2
    exact ⟨by rw [hst]; exact hne _ _, by rw [hst]; exact hne _ _⟩
  refine ⟨hpre, fun s hs => ?_⟩
  have hrun : machine.run s c =
      ⟨machine.reject,
        (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m)
          (FixedContentGammaTerminator.startConfig B x w)).head,
        (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m)
          (FixedContentGammaTerminator.startConfig B x w)).tape⟩ := by
    have h := FixedContentGammaTerminator.machine.seq_reject_handoff
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaTerminator.startConfig B x w) hrej
      (s - FixedContentGammaTerminator.deadline a m)
    rw [show FixedContentGammaTerminator.deadline a m +
      (s - FixedContentGammaTerminator.deadline a m) = s by omega] at h
    exact h
  have hheadval : (machine.run s c).head =
      (FixedContentGammaTerminator.finalConfig B x w).head := by
    rw [hrun]
    exact congrArg Config.head hend
  have htapeval : (machine.run s c).tape =
      (FixedContentGammaTerminator.finalConfig B x w).tape := by
    rw [hrun]
    exact congrArg Config.tape hend
  refine ⟨by rw [hrun], ?_, htapeval⟩
  rw [hheadval]
  show min (terminalIndex (Fin.append x w)) (a + m) = a + m
  unfold FixedContentGammaTerminator.terminalIndex
  rw [hg]
  exact Nat.min_self (a + m)

end
  Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
