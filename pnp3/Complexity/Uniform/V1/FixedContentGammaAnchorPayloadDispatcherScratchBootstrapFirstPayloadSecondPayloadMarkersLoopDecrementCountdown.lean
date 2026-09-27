import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The gamma anchor, the payload dispatcher, the scratch bootstrap, the first payload digit, the
second payload digit, the loop markers, the payload loop, the decrement and the countdown as one
machine (Part A G3h)

**No new table row.**  `machine` is `FixedContentGammaAnchor.machine.seq
FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`:
G2a's fixed 6-state, 18-row gamma-anchor shuttle on the left block `[0, 6)` and the whole landed
G3g 123-state composite on the right block `[6, 129)`, one closed 129-state, 387-row table whose
every row is a row of one of those nine tables with its target routed.  Write `N = a + m` and
`d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Eight executed handoffs.**  H10 — G2a's anchor into G2k's payload dispatcher — is the newly
executed one, and it has exactly **one** live routed row: `qReturn` on `some true`, the anchor's
only row targeting its accept (`accept_row_unique`), which `seq` retargets to the right block's
start `tailStart` at index `6`, writing `some true` and staying, in that same transition and at no
cost.  Six further anchor rows route to the composed reject `128`.  The left copies of the two
anchor verdicts are dead: no composed row targets either (`table_and_resource_pins`).  H11 (six
rows inside `[6, 34)`, all into `34`) and H12 (`40 → 43`) to H17 (`115 → 118`) are inherited from
G3g, its indices shifted by six and located by `(inTail q).val = 6 + q.val` with the universal
right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The anchor has exactly two
absorbing states, `qAccept` and `qReject` — its raw states `4` and `5`, three rows each — so the
landed `seq` routes both and no `mergeAccept` is needed, unlike H11.  Its strict first arrival is
already public and carries no room premise: on a matching tag with a decoded width,
`exact_terminal_contract` puts the anchor in neither verdict before
`successTime zeros = 2 * zeros + 5` and in `finalConfig` at it.
Its endpoint is compatible with the right block's start by construction: G2k's `startConfig`
retags the anchor's run at the *length-only* deadline `2 * N`, and `run_deadline` makes that run
equal to the run at `successTime zeros`, so the switch hands over exactly the head and tape the
right block's own `startConfig` carries — the marked tape with cell `7` erased, on the gamma
terminator cell `8 + zeros`.  The switch time is width-dependent but not path-dependent, and at
most the anchor's own length-only deadline `2 * N` (its landed `successTime_le_deadline`): it adds
a linear prefix to the composed clock and no new room premise.

**The composed run.**  `handoff_exact` takes the matching tag and the decoded width — two
hypotheses, no room, no budget: the run out of `startConfig` is in neither composed verdict at any
time up to and including `2 * zeros + 5`, is G2a's own run routed at every such time, at exactly
`2 * zeros + 5` **is** G3g's landed `startConfig B x w` re-embedded, and every later step is a G3g
step.  `handoff_endpoint_pins` reads that switch configuration back as G2k's own `startConfig`
projections, `tagged_inherited_switch` locates the inherited H11 at `2 * zeros + 5 + C` inside this
machine, and the drained theorem lands the composed accept `127` at exactly
`anchorChainClock C N zeros d v = 2 * zeros + 5 + dispatcherChainClock C N zeros d v` under G3g's
eight hypotheses unchanged.  On a malformed gamma the anchor rejects at step `1` — the dispatcher
never runs — and `malformed_reject_handoff` lands the composed reject `128` from step one on,
forward direction only, out of the decoded width alone with no tag premise.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
nine handoffs before H10 remain proof-level identifications (G2a's `startConfig` retags the actual
G2-terminator `finalConfig`), no raw-input `initialConfig` is executed, and no clock here counts a
step of any earlier phase.  No **first arrival** of the composed accept (the arrivals proved are
the anchor's and, as a hypothesis, the dispatcher's, both inside their own blocks); the **fence**
(all nine tables are uncapped); every **converse**; a **footprint** theorem; and the pnp4 bridge,
not built here, the standalone phases' pnp4 semantics being unchanged.  The composed `accept` is
the countdown's phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither
halting on a raw input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP` or `ContentVerifierBridge` is stated.  The table is fixed and complete but not claimed
state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedContentGammaAnchor (qStart qLeft qErase qReturn qAccept qReject successTime markedTape)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (dispatcherChainClock tagged_handoff
    dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained)

/-- The composed machine: G2a's gamma anchor, then G3g's whole composite, as one closed table.
No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedContentGammaAnchor.machine.seq
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- An anchor state in the composed control, at its own index. -/
def inAnchor (q : Fin FixedContentGammaAnchor.stateCount) : Fin machine.stateCount :=
  FixedContentGammaAnchor.machine.seqLeft
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- A G3g state in the composed control, shifted past the six anchor states. -/
def inTail
    (q : Fin
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedContentGammaAnchor.machine.seqRight
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- The routed target of an anchor row: `qAccept` becomes G3g's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedContentGammaAnchor.stateCount) : Fin machine.stateCount :=
  FixedContentGammaAnchor.machine.seqRoute
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    q

/-- G3g's start in the composed control, index `6`: the target of the one live routed row. -/
def tailStart : Fin machine.stateCount :=
  inTail
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start

/-- G2a's own `startConfig` — the retagged *actual* gamma-terminator endpoint — routed into the
composed control.  Still a phase-local retag, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedContentGammaAnchor.machine.seqEmbedRouted
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
    (FixedContentGammaAnchor.startConfig B x w)

/-- Exact cost of the anchor phase followed by the whole of G3g: the anchor's width-only first
arrival `2 * zeros + 5`, plus the dispatcher's input-dependent first arrival `C`, plus G3e's
`bootChainClock`.  Both handoffs cost nothing. -/
def anchorChainClock (C N zeros d v : Nat) : Nat :=
  successTime zeros + dispatcherChainClock C N zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the state and row counts, the anchor's start and verdicts, the
distinguished states with their indices, the block injections with their offsets and disjointness,
`tailStart` at `6`, the routing cases, every left row as the routed anchor row, every right row as
the G3g row, the public step against the composed raw table, **every** one of the anchor's eighteen
rows in the composed control — the one live routed row `qReturn` on `some true`, the marker-erase
row writing `none`, the six routed rejects, the four working rows and the two dead verdict copies —
and that no **left-block** row targets either dead copy, which together with the right-block row
equation and `inAnchor p ≠ inTail q`, both conjuncts above, is every composed row.  Inherited rows
are not restated: the right-block row equation transports every G3g row verbatim. -/
theorem table_and_resource_pins :
    machine.stateCount = 129 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 387 ∧
      FixedContentGammaAnchor.machine.start = qStart ∧
      FixedContentGammaAnchor.machine.accept = qAccept ∧
      FixedContentGammaAnchor.machine.reject = qReject ∧
      machine.start = route qStart ∧ machine.start = inAnchor qStart ∧
      machine.accept =
        inTail
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inTail
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 127 ∧ machine.reject.val = 128 ∧
      (∀ q, (inAnchor q).val = q.val) ∧ (∀ q, (inAnchor q).val < 6) ∧
      (∀ q, (inTail q).val = 6 + q.val) ∧ (∀ q, 6 ≤ (inTail q).val) ∧
      Function.Injective inAnchor ∧ Function.Injective inTail ∧
      (∀ p q, inAnchor p ≠ inTail q) ∧
      tailStart =
        inTail
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      tailStart.val = 6 ∧ route qAccept = tailStart ∧ route qReject = machine.reject ∧
      (∀ q, q ≠ qAccept → q ≠ qReject → route q = inAnchor q) ∧
      (∀ q s, machine.step (inAnchor q) s =
        (route (FixedContentGammaAnchor.machine.step q s).1,
          (FixedContentGammaAnchor.machine.step q s).2.1,
          (FixedContentGammaAnchor.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail
            (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inAnchor qReturn) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inAnchor qStart) (some true) = (inAnchor qLeft, some true, .left) ∧
      machine.step (inAnchor qLeft) (some false) = (inAnchor qLeft, some false, .left) ∧
      machine.step (inAnchor qLeft) (some true) = (inAnchor qErase, some true, .right) ∧
      machine.step (inAnchor qErase) (some false) = (inAnchor qReturn, none, .right) ∧
      machine.step (inAnchor qReturn) (some false) = (inAnchor qReturn, some false, .right) ∧
      machine.step (inAnchor qStart) (some false) = (machine.reject, some false, .stay) ∧
      machine.step (inAnchor qStart) none = (machine.reject, none, .stay) ∧
      machine.step (inAnchor qLeft) none = (machine.reject, none, .stay) ∧
      machine.step (inAnchor qErase) (some true) = (machine.reject, some true, .stay) ∧
      machine.step (inAnchor qErase) none = (machine.reject, none, .stay) ∧
      machine.step (inAnchor qReturn) none = (machine.reject, none, .stay) ∧
      (∀ s, machine.step (inAnchor qAccept) s = (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inAnchor qReject) s = (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inAnchor q) s).1 ≠ inAnchor qAccept ∧
        (machine.step (inAnchor q) s).1 ≠ inAnchor qReject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedContentGammaAnchor.machine.seq_pins
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun q => q.isLt, fun _ => rfl, fun _ => Nat.le_add_right _ _,
    hli, hri, hne, rfl, rfl, hra, hrr, hrw,
    fun q s => FixedContentGammaAnchor.machine.seq_step_left
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentGammaAnchor.machine.seq_step_right
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    fun q s => FixedContentGammaAnchor.machine.seq_step_eq_rawStep
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      q s,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · decide

/-- **The anchor has exactly one live row targeting its accept.**  Over all six states and all
three symbols, with the accept's own absorbing row excluded, a target of
`FixedContentGammaAnchor.machine.accept` forces `qReturn` on `some true`; so H10 has exactly one
live routed row.  The excluded row is the dead left copy's own, which `seq` routes to `tailStart`
and no composed row ever enters. -/
theorem accept_row_unique (q : Fin FixedContentGammaAnchor.stateCount) (s : Option Bool)
    (hq : q ≠ qAccept)
    (h : (FixedContentGammaAnchor.machine.rawStep q s).1 = FixedContentGammaAnchor.machine.accept) :
    q = qReturn ∧ s = some true := by
  revert h
  revert hq
  revert s
  revert q
  decide

/-- The start, pinned: G2a's `startConfig` routed into the composed control — the same head and
tape, the composed start as control.  Neither step consults decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedContentGammaAnchor.startConfig B x w
    let c := startConfig B x w
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl⟩

/-- The chained clock, pinned: G3g's sum prefixed by the anchor's width-only first arrival
`2 * zeros + 5`, and on `2 ≤ zeros` its full expansion.  `C` has no closed form in `N`. -/
theorem clock_pins (C N zeros d v : Nat) :
    anchorChainClock C N zeros d v = successTime zeros + dispatcherChainClock C N zeros d v ∧
      anchorChainClock C N zeros d v = 2 * zeros + 5 + (C + bootChainClock N zeros d v) ∧
      (2 ≤ zeros → anchorChainClock C N zeros d v =
        2 * zeros + 5 + (C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))))) := by
  refine ⟨rfl, rfl, fun hz => ?_⟩
  show successTime zeros + dispatcherChainClock C N zeros d v = _
  rw [(FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    C N zeros d v).2 hz]
  rfl

/-! ### The anchor's endpoint, as the composition consumes it -/

/-- G2k's `startConfig` is the anchor's run at its **first arrival**, retagged: the anchor's run at
the length-only deadline `2 * N` that G2k retags is its own run at `successTime zeros`, since the
anchor's accept absorbs from the first arrival to the deadline.  This is the semantic dependency
H10 has to respect; it executes nothing. -/
theorem dispatcher_start_at_first_arrival {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    FixedGammaPayloadDispatcher.startConfig B x w =
      FixedGammaPayloadDispatcher.retagG2a
        (FixedContentGammaAnchor.machine.run (successTime zeros)
          (FixedContentGammaAnchor.startConfig B x w)) := by
  obtain ⟨hsome, -⟩ := FixedContentGammaAnchor.exact_terminal_contract (B := B) x w htag
  obtain ⟨-, hend, -⟩ := hsome zeros hg
  unfold FixedGammaPayloadDispatcher.startConfig
  rw [FixedContentGammaAnchor.run_deadline x w htag, hend]

/-! ### The executed handoff -/

/-- **H10 fires when the anchor first returns to the gamma terminator, and it costs nothing.**  On
a matching tag with a decoded width — two hypotheses, no room premise — the run out of
`startConfig` is in neither composed verdict at any time up to and including `2 * zeros + 5` (at
the switch time itself the control is `tailStart`, so the bound is `≤`), is G2a's own run routed at
every such time — same head and whole tape — at exactly `2 * zeros + 5` **is** G3g's landed
`startConfig B x w` re-embedded, and runs G3g on from there. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let c := startConfig B x w
    (∀ t, t ≤ successTime zeros →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ successTime zeros → machine.run t c =
        FixedContentGammaAnchor.machine.seqEmbedRouted
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedContentGammaAnchor.machine.run t (FixedContentGammaAnchor.startConfig B x w))) ∧
      machine.run (successTime zeros) c =
        FixedContentGammaAnchor.machine.seqEmbedRight
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (successTime zeros + s) c =
        FixedContentGammaAnchor.machine.seqEmbedRight
          FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) := by
  intro c
  obtain ⟨hsome, -⟩ := FixedContentGammaAnchor.exact_terminal_contract (B := B) x w htag
  obtain ⟨hno, hend, -⟩ := hsome zeros hg
  have hwork : ∀ t, t < successTime zeros →
      (FixedContentGammaAnchor.machine.run t (FixedContentGammaAnchor.startConfig B x w)).state ≠
        FixedContentGammaAnchor.machine.accept := fun t ht => (hno t ht).1
  have hacc : (FixedContentGammaAnchor.machine.run (successTime zeros)
      (FixedContentGammaAnchor.startConfig B x w)).state =
      FixedContentGammaAnchor.machine.accept := by
    rw [hend]
    simp [FixedContentGammaAnchor.finalConfig, FixedContentGammaAnchor.machine, hg]
  have hcfg :
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
        B x w =
      ⟨FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
        (FixedContentGammaAnchor.machine.run (successTime zeros)
          (FixedContentGammaAnchor.startConfig B x w)).head,
        (FixedContentGammaAnchor.machine.run (successTime zeros)
          (FixedContentGammaAnchor.startConfig B x w)).tape⟩ := by
    refine Config.ext_parts rfl ?_ ?_
    · show (FixedGammaPayloadDispatcher.startConfig B x w).head = _
      rw [dispatcher_start_at_first_arrival x w htag hg]
      rfl
    · show (FixedGammaPayloadDispatcher.startConfig B x w).tape = _
      rw [dispatcher_start_at_first_arrival x w htag hg]
      rfl
  have hleft :=
    FixedContentGammaAnchor.machine.seq_run_left
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaAnchor.startConfig B x w) hwork
  have hsuffix : ∀ s, machine.run (successTime zeros + s) c =
      FixedContentGammaAnchor.machine.seqEmbedRight
        FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          s
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) := by
    intro s
    rw [hcfg]
    exact FixedContentGammaAnchor.machine.seq_handoff
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaAnchor.startConfig B x w) hwork hacc s
  have hC : machine.run (successTime zeros) c =
      FixedContentGammaAnchor.machine.seqEmbedRight
        FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          B x w) := hsuffix 0
  have hCs : (machine.run (successTime zeros) c).state = tailStart := by
    rw [hC]; rfl
  have hCa : (machine.run (successTime zeros) c).state ≠ machine.accept := by
    rw [hCs]; decide
  have hCr : (machine.run (successTime zeros) c).state ≠ machine.reject := by
    rw [hCs]; decide
  exact ⟨UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩

/-- **What the switch hands over is exactly what G2k reads.**  At the anchor's first arrival
`2 * zeros + 5`: the composed control is G3g's start `6`, the composed head and whole tape are
*the same* projections G2k's own `startConfig` carries, that tape is the anchor's `markedTape` —
the content tape with cell `7` erased as the recoverable marker — and the head is the gamma
terminator cell `8 + zeros`. -/
theorem handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (successTime zeros) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) ∧
      (∀ i, i.val ≠ 7 → e.tape i = FixedPairContentMarkerErase.contentTape B x w i) := by
  obtain ⟨-, -, hC, -⟩ := handoff_exact x w htag hg
  have hlt := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
  have hhead : (machine.run (successTime zeros) (startConfig B x w)).head =
      (FixedGammaPayloadDispatcher.startConfig B x w).head := by
    rw [hC]; rfl
  have htape : (machine.run (successTime zeros) (startConfig B x w)).tape =
      (FixedGammaPayloadDispatcher.startConfig B x w).tape := by
    rw [hC]; rfl
  have hfin : FixedGammaPayloadDispatcher.startConfig B x w =
      FixedGammaPayloadDispatcher.retagG2a (FixedContentGammaAnchor.finalConfig B x w) := by
    unfold FixedGammaPayloadDispatcher.startConfig
    rw [FixedContentGammaAnchor.run_deadline x w htag]
  have hheadval : (machine.run (successTime zeros) (startConfig B x w)).head.val = 8 + zeros := by
    rw [hhead, hfin]
    show min (FixedContentGammaTerminator.terminalIndex (Fin.append x w)) (a + m) = 8 + zeros
    unfold FixedContentGammaTerminator.terminalIndex
    rw [hg]
    exact Nat.min_eq_left (Nat.le_of_lt hlt)
  have htapeval : (machine.run (successTime zeros) (startConfig B x w)).tape =
      markedTape B x w := by
    rw [htape, hfin]
    show (FixedContentGammaAnchor.finalConfig B x w).tape = _
    simp [FixedContentGammaAnchor.finalConfig, hg]
  refine ⟨by rw [hC]; rfl, hhead, htape, hheadval, htapeval, fun i hi => ?_, fun i hi => ?_⟩
  · rw [htapeval]
    simp [markedTape, hi]
  · rw [htapeval]
    simp [markedTape, hi]

/-! ### The inherited switch and the composed run -/

/-- **The inherited H11 fires inside this machine at `2 * zeros + 5 + C`.**  There is a strict
first dispatcher arrival `C` at or below G2m's deadline, in one of the two success endpoints, and
at `2 * zeros + 5 + C` — the anchor's own steps counted first — the composed control is G2p-a's
start at index `34`, on exactly the head and tape G2p-a's landed `startConfig` carries.  `C` is
produced, not chosen. -/
theorem tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ FixedGammaPayloadDispatcherDeadline.deadline (a + m) ∧
      StrictFirstTerminalAt B x w C q ∧
      (q = FixedGammaPayloadDispatcher.qAllZero ∨ q = FixedGammaPayloadDispatcher.qHasOne) ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).state.val = 34 ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape := by
  obtain ⟨C, q, hle, hfirst, hq, hswitch⟩ := tagged_handoff (B := B) x w htag hg
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg
  obtain ⟨-, hhead, htape, -⟩ :=
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      x w htag hg hfirst
  have hrun := hsuffix C
  rw [hswitch] at hrun hhead htape
  exact ⟨C, q, hle, hfirst, hq, by rw [hrun]; rfl, by rw [hrun]; exact hhead,
    by rw [hrun]; exact htape⟩

/-- **The concrete exact run: the gamma anchor, H10, the payload dispatcher, H11, the scratch
bootstrap, H12, the first and second payload digits, H13 and H14, the markers, H15, the loop, H16,
the decrement, H17 and the countdown, one machine.**  Under G3g's **eight** hypotheses unchanged,
after exactly `anchorChainClock C (a+m) zeros d v` steps the composed machine is in its accept, the
countdown's `qDone`, on the separator blank `a+m+2+zeros` with tape `loopTape B x w zeros 0 v`,
persisting.  `v` is universally quantified and unsupplied; persistence is not first arrival of the
composed accept. -/
theorem anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := anchorChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg
  obtain ⟨he1, he2, he3, -⟩ :=
    dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (anchorChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedContentGammaAnchor.machine.seqEmbedRight
        FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
          (dispatcherChainClock C (a + m) zeros (borrow x w zeros) v)
          (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w)) :=
    hsuffix (dispatcherChainClock C (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (anchorChainClock C (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = anchorChainClock C (a + m) zeros (borrow x w zeros) v +
      (t - anchorChainClock C (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject.**  No decoded width and **no tag premise**: G2a rejects at step `1` on the
blank boundary cell `a + m` (its landed `run_reject_exact`), the dispatcher never runs, and the
generic rejecting handoff lands the composed reject — index `128`, not G2a's `qReject` at `5` — from
step one on, on the unchanged content tape.  **Not** a converse; it characterises no parsed
target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have he : FixedContentGammaAnchor.machine.run 1 (FixedContentGammaAnchor.startConfig B x w) =
      FixedContentGammaAnchor.finalConfig B x w :=
    FixedContentGammaAnchor.run_reject_exact x w hg
  have hrej : (FixedContentGammaAnchor.machine.run 1
      (FixedContentGammaAnchor.startConfig B x w)).state =
      FixedContentGammaAnchor.machine.reject := by
    rw [he]
    simp [FixedContentGammaAnchor.finalConfig, FixedContentGammaAnchor.machine, hg]
  have hrun : machine.run s (startConfig B x w) =
      ⟨machine.reject,
        (FixedContentGammaAnchor.machine.run 1 (FixedContentGammaAnchor.startConfig B x w)).head,
        (FixedContentGammaAnchor.machine.run 1
          (FixedContentGammaAnchor.startConfig B x w)).tape⟩ := by
    have h := FixedContentGammaAnchor.machine.seq_reject_handoff
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
      (FixedContentGammaAnchor.startConfig B x w) hrej (s - 1)
    rw [show 1 + (s - 1) = s by omega] at h
    exact h
  refine ⟨by rw [hrun], ?_, ?_⟩
  · rw [hrun]
    show (FixedContentGammaAnchor.machine.run 1
      (FixedContentGammaAnchor.startConfig B x w)).head.val = a + m
    rw [he]
    show min (FixedContentGammaTerminator.terminalIndex (Fin.append x w)) (a + m) = a + m
    unfold FixedContentGammaTerminator.terminalIndex
    rw [hg]
    exact Nat.min_self (a + m)
  · rw [hrun]
    show (FixedContentGammaAnchor.machine.run 1
      (FixedContentGammaAnchor.startConfig B x w)).tape = _
    rw [he]
    show (FixedContentGammaAnchor.finalConfig B x w).tape = _
    simp [FixedContentGammaAnchor.finalConfig, hg]

end
  Pnp3.Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
