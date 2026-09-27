import
  Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3j concrete slice: G1's fixed 15-state, 45-row content tag gate
followed by the whole landed G3i composite, as **one** closed 147-state, 441-row table.  Its newly
executed handoff H8 has exactly **one** live routed row — the last tag state `12` on `some false`,
the gate's only row targeting its accept outside the accept's own three — into G3i's start
`tailStart` at index `15`, writing `some false` and moving right; unlike the terminator's and the
anchor's, the gate's reject is the target of **many** live rows, all of which `seq` routes to the
composed reject `146`; and the two dead left verdict copies are no composed row's target.  H9
(`15 → 18`), H10 (`21 → 24`) and H11 (six rows inside `[24, 52)`, all into `52`) to H17
(`133 → 136`) are inherited from G3i.  Every public declaration is restated in full.

The probes.  The eight words are G3f's, G3g's, G3h's and G3i's (tag `10110010`) — seven well-formed
and `malformedWord`, whose physical suffix holds no gamma terminator; `badTag` is that tag with its
first bit flipped, the first fixture of this chain that does **not** match.  The gate's switch is
length-only — `3 * (a + m) + 7` — so the seven well-formed words switch at `58`, `43`, `40`, `40`,
`37`, `46` and `43` on the gamma cell `8`, whatever their widths; the
inherited H9 then fires `zeros + 1` steps later, the inherited H10 `2 * zeros + 5` after that, and
the inherited H11 and H12 later still.  The `check_*_literal*` theorems are **derived** from the
slice's theorems, whose hypotheses they discharge inline at the literals; the drain runs at `B = 22`
after `1192` steps — `58` for the gate, `5` for the terminator, `13` for the anchor, `18` for the
dispatcher, `1098` for G3e — with the register value `24 > N` supplied **by hand** (an execution
fixture, no accepted-content fixture).  The `check_*_probe` theorems reduce the composed machine by
kernel computation out of the actual `startConfig`, with no slice theorem used: the gate's rewind and
tag scan, all seven H8 switches, the inherited H9, H10, H11 and H12, the composed reject at the
terminator's deadline on the malformed fixture, and the composed reject on `badTag` at the gate's own
mismatch index `33` — seven steps before the length-only deadline `40` that the slice's theorem
states, and one step after a control that is in neither composed verdict.

Not here: the composed `startConfig` still embeds every earlier phase as a retag of the actual
marker-erase `finalConfig`, so there is no raw-input run and none of the seven earlier handoffs is
**executed** by this table.  One of them is pinned, as an identification and not as an executed row:
`check_handoff_pins` records H7 — G1's `startConfig` is the marker-erase `finalConfig` at its own
clock, retagged, with no hypothesis — and no table row of any earlier phase is pinned anywhere here.
Also not here: no first arrival of the composed accept, fence, converse, footprint theorem or pnp4
bridge; no exact rejection time on the mismatched branch; and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedContentGammaTerminator (gammaZeros?)
open Complexity.Uniform.V1.FixedContentGammaAnchor (successTime markedTape)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (terminatorChainClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inGate : Fin FixedContentTagGate.stateCount → Fin machine.stateCount := inGate
def check_inTail :
    Fin
      FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inTail
def check_route : Fin FixedContentTagGate.stateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_switchTime (N : Nat) : Nat := switchTime N
def check_gateChainClock (C N zeros d v : Nat) : Nat := gateChainClock C N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
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
        (machine.step (inGate q) s).1 ≠ inGate FixedContentTagGate.machine.reject) :=
  table_and_resource_pins

/-- The one live row into the gate's accept, restated in full. -/
theorem check_accept_row_unique (q : Fin FixedContentTagGate.stateCount) (s : Option Bool)
    (hq : q ≠ FixedContentTagGate.machine.accept)
    (h : (FixedContentTagGate.machine.rawStep q s).1 = FixedContentTagGate.machine.accept) :
    q.val = 12 ∧ s = some false :=
  accept_row_unique q s hq h

/-- The routing of every live row into the gate's reject, restated in full. -/
theorem check_reject_rows_routed (q : Fin FixedContentTagGate.stateCount) (s : Option Bool)
    (ha : q ≠ FixedContentTagGate.machine.accept)
    (hq : q ≠ FixedContentTagGate.machine.reject)
    (h : (FixedContentTagGate.machine.rawStep q s).1 = FixedContentTagGate.machine.reject) :
    machine.step (inGate q) s =
      (machine.reject, (FixedContentTagGate.machine.rawStep q s).2.1,
        (FixedContentTagGate.machine.rawStep q s).2.2) :=
  reject_rows_routed q s ha hq h

/-- The start as the retagged actual marker-erase endpoint, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
      c.tape = FixedPairContentMarkerErase.contentTape B x w :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C N zeros d v : Nat) :
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
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))))))) :=
  clock_pins C N zeros d v

/-- The tag gate's strict first successful arrival, restated in full. -/
theorem check_gate_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
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
      switchTime (a + m) = FixedContentTagGate.deadline a m ∧ 8 ≤ a + m :=
  gate_first_arrival x w htag

/-- The tag gate's rejecting arrival at its length-only deadline, restated in full. -/
theorem check_gate_reject_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    FixedContentTagGate.machine.run (switchTime (a + m))
        (FixedContentTagGate.startConfig B x w) = FixedContentTagGate.finalConfig B x w ∧
      (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)).state = FixedContentTagGate.machine.reject :=
  gate_reject_arrival x w htag

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_terminator_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    FixedContentGammaTerminator.startConfig B x w =
      FixedContentGammaTerminator.retag
        (FixedContentTagGate.machine.run (switchTime (a + m))
          (FixedContentTagGate.startConfig B x w)) :=
  terminator_start_at_first_arrival x w

/-- The executed handoff H8 at the gate's length-only first arrival, restated in full. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
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
              B x w))) :=
  handoff_exact x w htag

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let e := machine.run (switchTime (a + m)) (startConfig B x w)
    let p := FixedContentGammaTerminator.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = some false) :=
  handoff_endpoint_pins x w htag

/-- The inherited H9 inside this machine, restated in full. -/
theorem check_tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (zeros + 1)) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state.val = 18 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) :=
  tagged_inherited_switch x w htag hg

/-- The inherited H10 inside this machine, restated in full. -/
theorem check_tagged_inherited_anchor_switch {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime (a + m) + (zeros + 1 + successTime zeros)) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 24 ∧ e.head = p.head ∧ e.tape = p.tape ∧
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
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).state.val = 52 ∧
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (switchTime (a + m) + (zeros + 1 + (successTime zeros + C)))
          (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape :=
  tagged_inherited_dispatcher_switch x w htag hg

/-- The eleven-phase exact run, restated in full. -/
theorem check_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) :=
  tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject on a matching tag with no gamma terminator, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime (a + m) + FixedContentGammaTerminator.deadline a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime (a + m) + FixedContentGammaTerminator.deadline a m ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) :=
  malformed_reject_handoff x w htag hg

/-- The routed reject on a mismatched tag, restated in full. -/
theorem check_mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime (a + m) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w :=
  mismatched_tag_reject_handoff x w htag

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    switchTime 17 = 58 ∧ switchTime 13 = 46 ∧ switchTime 12 = 43 ∧ switchTime 11 = 40 ∧
      switchTime 10 = 37 ∧ FixedContentTagGate.deadline 8 9 = 58 ∧
      FixedContentGammaTerminator.deadline 8 3 = 4 ∧
      terminatorChainClock 18 17 4 0 24 = 1134 ∧ gateChainClock 18 17 4 0 24 = 1192 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- H8 at the widest and the narrowest fixture, **derived**.  On `physWord`: no composed verdict at
any time up to and including the switch `58`, at which the run **is** G3i's actual
`startConfig 0 tag physWord` re-embedded, on the gamma cell `8`, with the unchanged content tape
whose cell `7` carries the tag's own last bit `some false`.  On `zeroWord`: that same re-embedding at
the switch `37`, on that same cell `8` — the switch time differs with the length, the handed-over
head does not. -/
theorem check_handoff_literal :
    (∀ t, t ≤ 58 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 58 (startConfig 0 tag physWord) =
      FixedContentTagGate.machine.seqEmbedRight
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag physWord) ∧
    (machine.run 58 (startConfig 0 tag physWord)).head.val = 8 ∧
    (machine.run 58 (startConfig 0 tag physWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag physWord ∧
    (∀ i, i.val = 7 → (machine.run 58 (startConfig 0 tag physWord)).tape i = some false) ∧
    machine.run 37 (startConfig 0 tag zeroWord) =
      FixedContentTagGate.machine.seqEmbedRight
        FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag zeroWord) ∧
    (machine.run 37 (startConfig 0 tag zeroWord)).head.val = 8 := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) tag physWord (by decide)
  obtain ⟨-, -, -, h3, h4, h5⟩ := handoff_endpoint_pins (B := 0) tag physWord (by decide)
  obtain ⟨-, -, h6, -⟩ := handoff_exact (B := 0) tag zeroWord (by decide)
  obtain ⟨-, -, -, h7, -⟩ := handoff_endpoint_pins (B := 0) tag zeroWord (by decide)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept on the separator
blank `23` after exactly `1192` steps — `58` for the gate, none for H8, `5` for the terminator, none
for H9, `13` for the anchor, `18` for the dispatcher, then G3e's `1098` — persisting.  Nothing
decodes the hand-written `24`. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (gateChainClock 18 (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, gateChainClock 18 (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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

/-- The routed reject at the malformed fixture, derived: no composed verdict before `44` — the gate's
switch `40` plus the terminator's length-only deadline `4` — and the composed reject from it on, at
`44` and again at `48`, there on the boundary head `11` over the unchanged content tape.  Both the
tag hypothesis and the no-gamma hypothesis are discharged here. -/
theorem check_malformed_literal :
    (∀ t, t < 44 → (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.reject) ∧
    (machine.run 44 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 44 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 44 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 48 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨hpre, hpost⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide)
  obtain ⟨h1, h2, h3⟩ := hpost 44 (by decide)
  obtain ⟨h4, -, -⟩ := hpost 48 (by decide)
  exact ⟨hpre, h1, h2, h3, h4⟩

/-- The routed reject at the mismatched fixture, derived: from the gate's length-only deadline `40`
on — at `40` and again at `44` — the composed reject on the gate's own `finalConfig` head, here the
mismatch index `0`, over the unchanged content tape.  No claim is made about any earlier time; the
probe below shows the composed reject is in fact entered at `33`. -/
theorem check_mismatched_literal :
    (machine.run 40 (startConfig 0 badTag tightWord)).state = machine.reject ∧
    (machine.run 40 (startConfig 0 badTag tightWord)).head =
      (FixedContentTagGate.finalConfig 0 badTag tightWord).head ∧
    (machine.run 40 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 40 (startConfig 0 badTag tightWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 badTag tightWord ∧
    (machine.run 44 (startConfig 0 badTag tightWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 40 (by decide)
  obtain ⟨h4, -, -⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 44 (by decide)
  refine ⟨h1, h2, ?_, h3, h4⟩
  rw [h2]
  decide

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 4000000 in
/-- **The tag-gate phase, reduced.**  Out of the actual `startConfig 0 tag physWord`: `qStart` (`0`)
on the boundary blank `17`, one step left into `qProbe` (`1`) on `16`, then the erase/check/restore
cycle — `qCheckT` (`3`) and `qReturnT` (`5`) at steps `2` and `3` — three steps per physical cell
until the first tag state `qTag 0` (`6`) reads cell `1` at step `51`, and the last tag state (`12`)
reads cell `7` at `57`.  No slice theorem is used. -/
theorem check_gate_rewind_probe :
    (machine.run 0 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 0 (startConfig 0 tag physWord)).head.val = 17 ∧
    (machine.run 1 (startConfig 0 tag physWord)).state.val = 1 ∧
    (machine.run 1 (startConfig 0 tag physWord)).head.val = 16 ∧
    (machine.run 2 (startConfig 0 tag physWord)).state.val = 3 ∧
    (machine.run 3 (startConfig 0 tag physWord)).state.val = 5 ∧
    (machine.run 51 (startConfig 0 tag physWord)).state.val = 6 ∧
    (machine.run 51 (startConfig 0 tag physWord)).head.val = 1 ∧
    (machine.run 57 (startConfig 0 tag physWord)).head.val = 7 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **H8 through its one routed row, reduced.**  One step before each switch the control is the last
tag state `12`, and at the switch it is G3i's start `15`, the row `12`-on-`some false` having fired —
steps `57`/`58` on `physWord`, `42`/`43` on `middleWord` and `pendVirtWord`, `39`/`40` on `tightWord`
and `oneWord`, `36`/`37` on `zeroWord` and `45`/`46` on `pendTrueWord`, which is `3 * (a + m) + 6`
and `3 * (a + m) + 7` in each case.  At the widest switch the head is the gamma cell `8` and cell `7`
still holds the tag's own `some false`. -/
theorem check_h8_probe_reductions :
    (machine.run 57 (startConfig 0 tag physWord)).state.val = 12 ∧
    (machine.run 58 (startConfig 0 tag physWord)).state.val = 15 ∧
    (machine.run 58 (startConfig 0 tag physWord)).head.val = 8 ∧
    (machine.run 58 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 42 (startConfig 0 tag middleWord)).state.val = 12 ∧
    (machine.run 43 (startConfig 0 tag middleWord)).state.val = 15 ∧
    (machine.run 39 (startConfig 0 tag tightWord)).state.val = 12 ∧
    (machine.run 40 (startConfig 0 tag tightWord)).state.val = 15 ∧
    (machine.run 39 (startConfig 0 tag oneWord)).state.val = 12 ∧
    (machine.run 40 (startConfig 0 tag oneWord)).state.val = 15 ∧
    (machine.run 36 (startConfig 0 tag zeroWord)).state.val = 12 ∧
    (machine.run 37 (startConfig 0 tag zeroWord)).state.val = 15 ∧
    (machine.run 45 (startConfig 0 tag pendTrueWord)).state.val = 12 ∧
    (machine.run 46 (startConfig 0 tag pendTrueWord)).state.val = 15 ∧
    (machine.run 42 (startConfig 0 tag pendVirtWord)).state.val = 12 ∧
    (machine.run 43 (startConfig 0 tag pendVirtWord)).state.val = 15 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The inherited H9, H10 and H11, reduced.**  The terminator block runs out of the H8 switch and
hands over to G2a at `3 * (a + m) + 7 + (zeros + 1)` — index `18`, G3i's `3` shifted by the fifteen
gate states: step `63` on `physWord` with its `qScan` at `15` pinned one step before, `38` on
`zeroWord`, `46` on `middleWord`.  The anchor block then hands over to G2k at index `24`: `76` on
`physWord`, `43` on `zeroWord`, `55` on `middleWord`.  The dispatcher block then hands over to G2p-a
at index `52`: `94` on `physWord`, `45` on `zeroWord`. -/
theorem check_inherited_handoff_probe :
    (machine.run 62 (startConfig 0 tag physWord)).state.val = 15 ∧
    (machine.run 63 (startConfig 0 tag physWord)).state.val = 18 ∧
    (machine.run 63 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 76 (startConfig 0 tag physWord)).state.val = 24 ∧
    (machine.run 94 (startConfig 0 tag physWord)).state.val = 52 ∧
    (machine.run 38 (startConfig 0 tag zeroWord)).state.val = 18 ∧
    (machine.run 43 (startConfig 0 tag zeroWord)).state.val = 24 ∧
    (machine.run 45 (startConfig 0 tag zeroWord)).state.val = 52 ∧
    (machine.run 46 (startConfig 0 tag middleWord)).state.val = 18 ∧
    (machine.run 55 (startConfig 0 tag middleWord)).state.val = 24 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The inherited H12, reduced.**  Out of `startConfig 0 tag physWord` the G2p-a block runs on and
hands over to G2p-b at steps `112`/`113`: index `58`, then `61` on the restored terminator cell `12`.
These are G3i's own steps `54`/`55` shifted by the `58` steps the gate takes and its indices by the
fifteen gate states, so the inherited `58 → 61` fires inside this machine and is not merely offset
arithmetic. -/
theorem check_inherited_h12_probe :
    (machine.run 112 (startConfig 0 tag physWord)).state.val = 58 ∧
    (machine.run 113 (startConfig 0 tag physWord)).state.val = 61 ∧
    (machine.run 113 (startConfig 0 tag physWord)).head.val = 12 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The routed reject on a matching tag with no gamma terminator, reduced.**  Out of
`startConfig 0 tag malformedWord`: the gate hands over at `40`, at step `43` the terminator has
scanned the whole physical suffix, is in neither composed verdict, and sits on the boundary head
`11`; at `44` — the gate's `40` plus the terminator's length-only deadline `4` — the composed reject,
index `146`, not G1's own `qReject` at `14` nor G2's at `17`, on that head; and it is still there at
`48`. -/
theorem check_malformed_probe :
    (machine.run 40 (startConfig 0 tag malformedWord)).state.val = 15 ∧
    (machine.run 43 (startConfig 0 tag malformedWord)).state.val = 15 ∧
    (machine.run 43 (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
    (machine.run 43 (startConfig 0 tag malformedWord)).state ≠ machine.reject ∧
    (machine.run 43 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 44 (startConfig 0 tag malformedWord)).state.val = 146 ∧
    (machine.run 44 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 48 (startConfig 0 tag malformedWord)).state.val = 146 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The routed reject on a mismatched tag, reduced.**  Out of `startConfig 0 badTag tightWord`:
at step `32` the gate is still working — `qCheckF` (`2`), in neither composed verdict — and at `33`,
`3 * (a + m) + 0` for the mismatch index `0`, the composed reject `146` on cell `0`; it is still
there at the gate's length-only deadline `40`, which is the earliest time
`mismatched_tag_reject_handoff` speaks about.  This probe is the only place the exact mismatch time
is exhibited, and it is exhibited for one fixture by computation, not proved in general. -/
theorem check_mismatched_probe :
    (machine.run 32 (startConfig 0 badTag tightWord)).state.val = 2 ∧
    (machine.run 32 (startConfig 0 badTag tightWord)).state ≠ machine.accept ∧
    (machine.run 32 (startConfig 0 badTag tightWord)).state ≠ machine.reject ∧
    (machine.run 33 (startConfig 0 badTag tightWord)).state.val = 146 ∧
    (machine.run 33 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 40 (startConfig 0 badTag tightWord)).state.val = 146 ∧
    FixedContentTagGate.tagMatches (Fin.append badTag tightWord) = false ∧
    (FixedContentTagGate.finalConfig 0 badTag tightWord).head.val = 0 := by
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
