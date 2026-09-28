import
  Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3k concrete slice: the fixed 4-state, 12-row trailing-content-marker
erasure followed by the whole landed G3j composite, as **one** closed 151-state, 453-row table.  Its
newly executed handoff H7 has exactly **one** live routed row — `qErase` on `some true`, the
marker-erase table's only row targeting its accept outside the accept's own three — into G3j's start
`tailStart` at index `4`, writing `none` and **staying**, so the composed table performs the erasure
itself in the handing-over transition.  The marker-erase reject is the target of exactly **two** live
rows — `qErase` on `some false` and on `none` — proved the only ones once both verdicts' own
absorbing rows are excluded, and `seq` routes each to the composed reject `150`.  Neither is taken
out of this `startConfig`: the left block never rejects at any time.  Both dead left verdict copies
are no composed row's target.  H8 (`16 → 19`), H9 (`19 → 22`), H10 (`25 → 28`) and H11 (six rows
inside `[28, 56)`, all into `56`) to H17 (`137 → 140`) are inherited from G3j.  Every public
declaration is restated in full.

The probes.  The nine words are G3j's (tag `10110010`) — seven well-formed and `malformedWord`,
whose physical suffix holds no gamma terminator, plus `badTag`, that tag with its first bit flipped.
The marker-erase switch is length-only — `N + 3` — so the seven well-formed words switch at `20`,
`16`, `15`, `15`, `14`, `14` and `13`, always on the boundary cell `N`, whatever their widths and
whatever their tags: `badTag` and `malformedWord` switch on time too, the left phase reading neither.
Each inherited switch then fires at G3j's own time plus that `N + 3`.  The `check_*_literal*`
theorems are **derived** from the slice's theorems; `check_reject_row_literals` instantiates
`reject_rows_routed` at both live reject rows and `reject_rows_unique` at `qScan`.  The drain runs at
`B = 22` after `1212` steps — `20` for the marker erasure, `58` for the gate, `5` for the terminator,
`13` for the anchor, `18` for the dispatcher, `1098` for G3e — with the register value `24 > N`
supplied **by hand** (an execution fixture, no accepted-content fixture).  The `check_*_probe`
theorems reduce the composed machine by kernel computation out of the actual `startConfig`, with no
slice theorem used: the marker-erase walk and the erasing switch, all nine H7 switches, the inherited
H8, H9, H10, H11 and H12, the composed reject at the terminator's deadline on the malformed fixture,
and the composed reject on `badTag` at **rejection time** `47`: `badTag`'s mismatch **cell** is `0`,
so `N + 3 + (3 * (a + m) + 0)` is `47` — seven steps before the `54` that the slice's theorem states,
and one step after a control that is in neither composed verdict.

Not here: the composed `startConfig` still embeds the six earlier phases as a retag of the actual
origin-alignment `finalConfig`, so there is no raw-input run and none of those six is **executed** by
this table.  One of them is pinned, as an identification and not as an executed row:
`check_handoff_pins` records H6 — the marker-erase `startConfig` is the origin-alignment `finalConfig`
at its own clock, retagged, with no hypothesis — and no table row of any earlier phase is pinned
anywhere here.  Also not here: no first arrival of the composed accept, fence, converse, footprint
theorem or pnp4 bridge; no exact rejection time on the mismatched branch; and no `accepts`,
`AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedContentGammaTerminator (gammaZeros?)
open Complexity.Uniform.V1.FixedContentGammaAnchor (successTime markedTape)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (gateChainClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_tailMachine : UniformTM := tailMachine
def check_inErase :
    Fin FixedPairContentMarkerErase.eraseStateCount → Fin machine.stateCount := inErase
def check_inTail : Fin tailMachine.stateCount → Fin machine.stateCount := inTail
def check_route : Fin FixedPairContentMarkerErase.eraseStateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_tailStartConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config tailMachine.stateCount (pairLength a m) B :=
  tailStartConfig
def check_switchTime (N : Nat) : Nat := switchTime N
def check_eraseChainClock (C N zeros d v : Nat) : Nat := eraseChainClock C N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
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
          inErase FixedPairContentMarkerErase.machine.reject) :=
  table_and_resource_pins

/-- The one live row into the marker-erase accept, restated in full. -/
theorem check_accept_row_unique (q : Fin FixedPairContentMarkerErase.eraseStateCount)
    (s : Option Bool) (hq : q ≠ FixedPairContentMarkerErase.machine.accept)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.accept) :
    q = FixedPairContentMarkerErase.qErase ∧ q.val = 1 ∧ s = some true :=
  accept_row_unique q s hq h

/-- The two live rows into the marker-erase reject, restated in full. -/
theorem check_reject_rows_unique (q : Fin FixedPairContentMarkerErase.eraseStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairContentMarkerErase.machine.accept)
    (hq : q ≠ FixedPairContentMarkerErase.machine.reject)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.reject) :
    q = FixedPairContentMarkerErase.qErase ∧ q.val = 1 ∧ (s = some false ∨ s = none) :=
  reject_rows_unique q s ha hq h

/-- The routing of every live row into the marker-erase reject, restated in full. -/
theorem check_reject_rows_routed (q : Fin FixedPairContentMarkerErase.eraseStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairContentMarkerErase.machine.accept)
    (hq : q ≠ FixedPairContentMarkerErase.machine.reject)
    (h : (FixedPairContentMarkerErase.machine.rawStep q s).1 =
      FixedPairContentMarkerErase.machine.reject) :
    machine.step (inErase q) s =
      (machine.reject, (FixedPairContentMarkerErase.machine.rawStep q s).2.1,
        (FixedPairContentMarkerErase.machine.rawStep q s).2.2) :=
  reject_rows_routed q s ha hq h

/-- The start as the retagged actual origin-alignment endpoint, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
      c.tape = FixedPairOriginAlignment.alignedTape B x w :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C N zeros d v : Nat) :
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
            (totalClock N zeros + composedClock N zeros d v)))))))))) :=
  clock_pins C N zeros d v

/-- The marker-erase phase's strict first arrival, restated in full. -/
theorem check_erase_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
        FixedPairContentMarkerErase.machine.reject) :=
  erase_first_arrival x w

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_gate_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairContentMarkerErase.machine.run (switchTime (a + m))
      (FixedPairContentMarkerErase.startConfig B x w)
    g = FixedPairContentMarkerErase.finalConfig B x w ∧
      (FixedContentTagGate.startConfig B x w).state = FixedContentTagGate.machine.start ∧
      (FixedContentTagGate.startConfig B x w).head = g.head ∧
      (FixedContentTagGate.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  gate_start_at_first_arrival x w

/-- The executed handoff H7 at the marker-erase length-only first arrival, restated in full. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
          (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (a + m)) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedContentTagGate.startConfig B x w).head ∧
      e.tape = (FixedContentTagGate.startConfig B x w).tape ∧
      e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m ≤ i.val → e.tape i = none) :=
  handoff_endpoint_pins x w

/-- The inherited H8 inside this machine, restated in full. -/
theorem check_tagged_inherited_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7)) (startConfig B x w)
    let p := FixedContentGammaTerminator.startConfig B x w
    e.state.val = 19 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = some false) :=
  tagged_inherited_switch x w htag

/-- The inherited H9 inside this machine, restated in full. -/
theorem check_tagged_inherited_terminator_switch {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7 + (zeros + 1))) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state.val = 22 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) :=
  tagged_inherited_terminator_switch x w htag hg

/-- The inherited H10 inside this machine, restated in full. -/
theorem check_tagged_inherited_anchor_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (3 * (a + m) + 7 + (zeros + 1 + successTime zeros)))
      (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 28 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) :=
  tagged_inherited_anchor_switch x w htag hg

/-- The inherited H11 inside this machine, restated in full. -/
theorem check_tagged_inherited_dispatcher_switch {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
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
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape :=
  tagged_inherited_dispatcher_switch x w htag hg

/-- The twelve-phase exact run, restated in full. -/
theorem check_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) :=
  marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject on a matching tag with no gamma terminator, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime (a + m) +
          (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime (a + m) + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) :=
  malformed_reject_handoff x w htag hg

/-- The routed reject on a mismatched tag, restated in full. -/
theorem check_mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime (a + m) + (3 * (a + m) + 7) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w :=
  mismatched_tag_reject_handoff x w htag

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    switchTime 17 = 20 ∧ switchTime 13 = 16 ∧ switchTime 12 = 15 ∧ switchTime 11 = 14 ∧
      switchTime 10 = 13 ∧ FixedPairContentMarkerErase.clock 8 9 = 20 ∧
      FixedContentTagGate.deadline 8 9 = 58 ∧
      FixedContentGammaTerminator.deadline 8 3 = 4 ∧
      gateChainClock 18 17 4 0 24 = 1192 ∧ eraseChainClock 18 17 4 0 24 = 1212 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The nine probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def badTag : Bitstring 8 := ![false, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def middleWord : Bitstring 4 := ![false, false, true, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def oneWord : Bitstring 3 := ![false, true, false]
private def zeroWord : Bitstring 2 := ![true, false]
private def malformedWord : Bitstring 3 := ![false, false, false]
private def pendTrueWord : Bitstring 5 := ![false, false, true, false, true]
private def pendVirtWord : Bitstring 4 := ![false, false, true, false]

/-! ### Derived literal handoffs -/

/-- Both routed reject rows, **derived**, and the reject-row uniqueness at the scanning state.
`reject_rows_routed` discharged at the two literals — `qErase` on `some false` and `qErase` on
`none`, the malformed-candidate exits — each keeping the marker-erase table's own written symbol and
its `stay` and landing in the composed reject `150`; and `reject_rows_unique` discharged at `qScan`,
which has no row into the reject at all.  Unlike the gate's, this list of live reject rows is
complete, but neither row says anything about the right block, which keeps its own inherited rows
into `150`. -/
theorem check_reject_row_literals :
    machine.step (inErase FixedPairContentMarkerErase.qErase) (some false) =
        (machine.reject, some false, .stay) ∧
      machine.step (inErase FixedPairContentMarkerErase.qErase) none =
        (machine.reject, none, .stay) ∧
      (∀ s, (FixedPairContentMarkerErase.machine.rawStep FixedPairContentMarkerErase.qScan s).1 ≠
        FixedPairContentMarkerErase.machine.reject) ∧
      machine.reject.val = 150 := by
  refine ⟨?_, ?_, fun s h => ?_, rfl⟩
  · exact reject_rows_routed _ (some false) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ none (by decide) (by decide) (by decide)
  · exact absurd
      (reject_rows_unique FixedPairContentMarkerErase.qScan s (by decide) (by decide) h).2.1
      (by decide)

/-- H7 at the widest and the narrowest fixture, **derived**, with no hypothesis discharged because
the theorem takes none.  On `physWord`: no composed verdict at any time up to and including the
switch `20`, at which the run **is** G3j's actual `startConfig 0 tag physWord` re-embedded, on the
boundary cell `17`, with the erased `contentTape`, every allocated cell from `17` on blank.  On
`zeroWord`: that same re-embedding at the switch `13`, on the boundary cell `10` — the switch time
and the handed-over head both move with the length. -/
theorem check_handoff_literal :
    (∀ t, t ≤ 20 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 20 (startConfig 0 tag physWord) =
      FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine
        (tailStartConfig 0 tag physWord) ∧
    (machine.run 20 (startConfig 0 tag physWord)).head.val = 8 + 9 ∧
    (machine.run 20 (startConfig 0 tag physWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag physWord ∧
    (∀ i : Fin (tapeLength (pairLength 8 9) 0), 8 + 9 ≤ i.val →
      (machine.run 20 (startConfig 0 tag physWord)).tape i = none) ∧
    machine.run 13 (startConfig 0 tag zeroWord) =
      FixedPairContentMarkerErase.machine.seqEmbedRight tailMachine
        (tailStartConfig 0 tag zeroWord) ∧
    (machine.run 13 (startConfig 0 tag zeroWord)).head.val = 8 + 2 := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) tag physWord
  obtain ⟨-, -, -, -, -, h3, h4, h5⟩ := handoff_endpoint_pins (B := 0) tag physWord
  obtain ⟨-, -, h6, -⟩ := handoff_exact (B := 0) tag zeroWord
  obtain ⟨-, -, -, -, -, h7, -⟩ := handoff_endpoint_pins (B := 0) tag zeroWord
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept on the separator
blank `23` after exactly `1212` steps — `20` for the marker erasure, none for H7, `58` for the gate,
none for H8, `5` for the terminator, none for H9, `13` for the anchor, none for H10, `18` for the
dispatcher, none for H11, then G3e's `1098` — persisting.  Nothing decodes the hand-written `24`. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (eraseChainClock 18 (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, eraseChainClock 18 (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      (a := 8) (m := 9) (B := 22) (C := 3 * 4 + 6) (zeros := 4) (v := 24) (F := 24) tag physWord
      (by decide) (by decide)
      (first_true_strict_first_terminal (zeros := 4) tag physWord (by decide) (by decide)
        (by omega) (by decide) (by decide)).1
      (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The routed reject at the malformed fixture, derived: no composed verdict before `58` — the
marker-erase switch `14`, the gate's `40` and the terminator's length-only deadline `4` — and the
composed reject from it on, at `58` and again at `62`, there on the boundary head `11` over the
erased content tape.  Both the tag hypothesis and the no-gamma hypothesis are discharged here. -/
theorem check_malformed_literal :
    (∀ t, t < 58 → (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.reject) ∧
    (machine.run 58 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 58 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 58 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 62 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨hpre, hpost⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide)
  obtain ⟨h1, h2, h3⟩ := hpost 58 (by decide)
  obtain ⟨h4, -, -⟩ := hpost 62 (by decide)
  exact ⟨hpre, h1, h2, h3, h4⟩

/-- The routed reject at the mismatched fixture, derived: from `54` on — the marker-erase switch `14`
plus the gate's length-only deadline `40` — at `54` and again at `58`, the composed reject on the
gate's own `finalConfig` head, here the mismatch cell `0`, over the erased content tape.  No claim is
made about any earlier time; the probe below shows the composed reject is in fact entered at `47`. -/
theorem check_mismatched_literal :
    (machine.run 54 (startConfig 0 badTag tightWord)).state = machine.reject ∧
    (machine.run 54 (startConfig 0 badTag tightWord)).head =
      (FixedContentTagGate.finalConfig 0 badTag tightWord).head ∧
    (machine.run 54 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 54 (startConfig 0 badTag tightWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 badTag tightWord ∧
    (machine.run 58 (startConfig 0 badTag tightWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 54 (by decide)
  obtain ⟨h4, -, -⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 58 (by decide)
  refine ⟨h1, h2, ?_, h3, h4⟩
  rw [h2]
  decide

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 4000000 in
/-- **The marker-erase phase, reduced.**  Out of the actual `startConfig 0 tag physWord`: `qScan`
(`0`) on the origin cell `0`, walking right one cell per step — still `qScan` on the marker cell `17`
at step `17`, which is the cell it reads in the step to `18` — standing on the first physical blank
`18` at step `18`, one step left into `qErase` (`1`) on `17` at step `19` with the marker there still
`some true`, and at step `20` the control has left the left block for `tailStart` (`4`), head
unmoved, with cell `17` now `none`: the erasure is performed by the routed row of the composed table
itself.  No slice theorem is used. -/
theorem check_erase_probe :
    (machine.run 0 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 0 (startConfig 0 tag physWord)).head.val = 0 ∧
    (machine.run 17 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 17 (startConfig 0 tag physWord)).head.val = 17 ∧
    (machine.run 18 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 18 ∧
    (machine.run 19 (startConfig 0 tag physWord)).state.val = 1 ∧
    (machine.run 19 (startConfig 0 tag physWord)).head.val = 17 ∧
    (machine.run 19 (startConfig 0 tag physWord)).tape ⟨17, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag physWord)).state.val = 4 ∧
    (machine.run 20 (startConfig 0 tag physWord)).head.val = 17 ∧
    (machine.run 20 (startConfig 0 tag physWord)).tape ⟨17, by decide⟩ = none := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **H7 through its one routed row, reduced.**  One step before each switch the control is `qErase`
(`1`), and at the switch it is G3j's start `4`, the row `qErase`-on-`some true` having fired — steps
`19`/`20` on `physWord`, `15`/`16` on `pendTrueWord`, `14`/`15` on `middleWord` and `pendVirtWord`,
`13`/`14` on `tightWord`, `oneWord` and `malformedWord`, and `12`/`13` on `zeroWord`, which is
`N + 2` and `N + 3` in each case.  `badTag` with `tightWord` switches at the same `13`/`14` as the
matching tag does: the left block reads no tag cell, so a mismatched tag reaches the right block
unhindered and is rejected there. -/
theorem check_h7_probe_reductions :
    (machine.run 19 (startConfig 0 tag physWord)).state.val = 1 ∧
    (machine.run 20 (startConfig 0 tag physWord)).state.val = 4 ∧
    (machine.run 15 (startConfig 0 tag pendTrueWord)).state.val = 1 ∧
    (machine.run 16 (startConfig 0 tag pendTrueWord)).state.val = 4 ∧
    (machine.run 14 (startConfig 0 tag middleWord)).state.val = 1 ∧
    (machine.run 15 (startConfig 0 tag middleWord)).state.val = 4 ∧
    (machine.run 14 (startConfig 0 tag pendVirtWord)).state.val = 1 ∧
    (machine.run 15 (startConfig 0 tag pendVirtWord)).state.val = 4 ∧
    (machine.run 13 (startConfig 0 tag tightWord)).state.val = 1 ∧
    (machine.run 14 (startConfig 0 tag tightWord)).state.val = 4 ∧
    (machine.run 13 (startConfig 0 tag oneWord)).state.val = 1 ∧
    (machine.run 14 (startConfig 0 tag oneWord)).state.val = 4 ∧
    (machine.run 13 (startConfig 0 tag malformedWord)).state.val = 1 ∧
    (machine.run 14 (startConfig 0 tag malformedWord)).state.val = 4 ∧
    (machine.run 12 (startConfig 0 tag zeroWord)).state.val = 1 ∧
    (machine.run 13 (startConfig 0 tag zeroWord)).state.val = 4 ∧
    (machine.run 13 (startConfig 0 badTag tightWord)).state.val = 1 ∧
    (machine.run 14 (startConfig 0 badTag tightWord)).state.val = 4 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The inherited H8, H9, H10 and H11, reduced.**  The gate block runs out of the H7 switch and
hands over to G2 at `N + 3 + (3 * N + 7)` — index `19`, G3j's `15` shifted by the four marker-erase
states: step `78` on `physWord` with its last tag state `16` pinned one step before, `50` on
`zeroWord`, `58` on `middleWord`.  The terminator block then hands over to G2a at index `22`: `83` on
`physWord`, `51` on `zeroWord`, `61` on `middleWord`.  The anchor block then hands over to G2k at
index `28`: `96` on `physWord`, `56` on `zeroWord`.  The dispatcher block then hands over to G2p-a at
index `56`: `114` on `physWord`, `58` on `zeroWord`. -/
theorem check_inherited_handoff_probe :
    (machine.run 77 (startConfig 0 tag physWord)).state.val = 16 ∧
    (machine.run 78 (startConfig 0 tag physWord)).state.val = 19 ∧
    (machine.run 78 (startConfig 0 tag physWord)).head.val = 8 ∧
    (machine.run 83 (startConfig 0 tag physWord)).state.val = 22 ∧
    (machine.run 83 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 96 (startConfig 0 tag physWord)).state.val = 28 ∧
    (machine.run 114 (startConfig 0 tag physWord)).state.val = 56 ∧
    (machine.run 50 (startConfig 0 tag zeroWord)).state.val = 19 ∧
    (machine.run 51 (startConfig 0 tag zeroWord)).state.val = 22 ∧
    (machine.run 56 (startConfig 0 tag zeroWord)).state.val = 28 ∧
    (machine.run 58 (startConfig 0 tag zeroWord)).state.val = 56 ∧
    (machine.run 58 (startConfig 0 tag middleWord)).state.val = 19 ∧
    (machine.run 61 (startConfig 0 tag middleWord)).state.val = 22 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The inherited H12, reduced.**  Out of `startConfig 0 tag physWord` the G2p-a block runs on and
hands over to G2p-b at steps `132`/`133`: index `62`, then `65` on the restored terminator cell `12`.
These are G3j's own steps `112`/`113` shifted by the `20` steps the marker erasure takes and its
indices by the four marker-erase states, so the inherited `62 → 65` fires inside this machine and is
not merely offset arithmetic. -/
theorem check_inherited_h12_probe :
    (machine.run 132 (startConfig 0 tag physWord)).state.val = 62 ∧
    (machine.run 133 (startConfig 0 tag physWord)).state.val = 65 ∧
    (machine.run 133 (startConfig 0 tag physWord)).head.val = 12 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The routed reject on a matching tag with no gamma terminator, reduced.**  Out of
`startConfig 0 tag malformedWord`: the marker erasure hands over at `14`, the gate at `54`, at step
`57` the terminator has scanned the whole physical suffix, is in neither composed verdict, and sits
on the boundary head `11`; at `58` — the switch `14`, the gate's `40` and the terminator's
length-only deadline `4` — the composed reject, index `150`, not the marker-erase `qReject` at `3`
nor G1's at `18` nor G2's at `21`, on that head; and it is still there at `62`. -/
theorem check_malformed_probe :
    (machine.run 54 (startConfig 0 tag malformedWord)).state.val = 19 ∧
    (machine.run 57 (startConfig 0 tag malformedWord)).state.val = 19 ∧
    (machine.run 57 (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
    (machine.run 57 (startConfig 0 tag malformedWord)).state ≠ machine.reject ∧
    (machine.run 57 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 58 (startConfig 0 tag malformedWord)).state.val = 150 ∧
    (machine.run 58 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 62 (startConfig 0 tag malformedWord)).state.val = 150 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The routed reject on a mismatched tag, reduced.**  Out of `startConfig 0 badTag tightWord`:
at step `46` the gate is still working — `qCheckF` at composed index `6`, in neither composed
verdict — and at `47`, the marker-erase switch `14` plus `3 * (a + m) + 0` for the mismatch cell `0`,
the composed reject `150` on cell `0`; it is still there at `54`, the switch plus the gate's
length-only deadline, which is the earliest time `mismatched_tag_reject_handoff` speaks about.  This
probe is the only place the exact rejection time is exhibited, and it is exhibited for one fixture by
computation, not proved in general. -/
theorem check_mismatched_probe :
    (machine.run 46 (startConfig 0 badTag tightWord)).state.val = 6 ∧
    (machine.run 46 (startConfig 0 badTag tightWord)).state ≠ machine.accept ∧
    (machine.run 46 (startConfig 0 badTag tightWord)).state ≠ machine.reject ∧
    (machine.run 47 (startConfig 0 badTag tightWord)).state.val = 150 ∧
    (machine.run 47 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 54 (startConfig 0 badTag tightWord)).state.val = 150 ∧
    FixedContentTagGate.tagMatches (Fin.append badTag tightWord) = false ∧
    (FixedContentTagGate.finalConfig 0 badTag tightWord).head.val = 0 := by
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
