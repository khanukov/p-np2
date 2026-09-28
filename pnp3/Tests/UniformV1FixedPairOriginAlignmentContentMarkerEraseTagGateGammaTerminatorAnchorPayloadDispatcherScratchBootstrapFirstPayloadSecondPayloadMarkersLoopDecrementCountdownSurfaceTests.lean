import
  Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3l concrete slice: the fixed 26-state, 78-row pair origin alignment
followed by the whole landed G3k composite, as **one** closed 177-state, 531-row table.  Its newly
executed handoff H6 has **three** live routed rows — the alignment states `10`, `11` and `12` on
`none`, proved by `accept_rows_unique` the only rows targeting the phase's accept once the accept's own
three are excluded — into G3k's start `tailStart` at index `26`, each keeping its own restoration write
(`none`, `some false`, `some true`) and its **left** move, which at the endpoint head `0` is the clamp.
Which of the three fires is **not** claimed: those states are `private` in the landed phase.  The
alignment reject is the target of exactly **21** live rows — five `none` rows and sixteen Boolean rows,
`reject_rows_unique` proving that classification exhaustive — and `seq` routes each to the composed
reject `176`.  None is taken out of this `startConfig`: the left block never rejects at any time.  Both
dead left verdict copies are no composed row's target, and the composed start is neither.  H7
(`26 → 30`) to H17 (`163 → 166`) are inherited from G3k.  Every public declaration is restated in full.

The switch time.  `switchTime a m = (10 * a + 7) * (a + m + 1) + 3 * a` is the first clock in this
chain that is **not** a function of `N = a + m`: `check_clock_values` reduces the three pairs with
`a + m = 2` to `21`, `54` and `87`.  The composed clock is therefore quadratic in `a`, and no claim is
made that the cubic budget dominates it.

The probes.  Kernel reduction of `machine.run` is quadratic in the step count, and the tagged fixtures
all have `a = 8`, so `switchTime 8 m` is already `981` or more and reducing to the switch overflows the
kernel stack.  The `check_*_probe` theorems — which use **no** slice theorem — therefore run on new
tiny tag-free fixtures, which is sound because the alignment phase reads no tag, no gamma and no bit
meaning, it only shifts the block to the origin: empty inputs (`switchTime 0 0 = 7`) exercise the
routed row of state `10`, `![true]`/`![false]` (`switchTime 1 1 = 54`) that of state `11`, and
`![true]`/`![true]` that of state `12`, so all three live H6 rows are exhibited, together with
`B = 1`, the inherited H7 firing `N + 3` later, and the composed reject `176` entered through the
**right** block when the tag gate rejects the short content.  The tagged fixtures are kept for the
`check_*_literal*` theorems, which are **derived** from the slice's own theorems and so cost no
reduction: `tag`/`physWord` switches at `1590` and drains at `1590 + 1212 = 2802`, the malformed
fixture rejects from `1126` on and the mismatched one from `1122` on.

Not here: the composed `startConfig` still embeds the five earlier phases as a retag of the actual
origin-shift-bootstrap `finalConfig`, so there is no raw-input run and none of those five is
**executed** by this table.  One of them is pinned, as an identification and not as an executed row:
`check_handoff_pins` records H5 — the alignment `startConfig` is the bootstrap `finalConfig` at its own
clock, retagged, with no hypothesis — and no table row of any earlier phase is pinned anywhere here.
The four deeper inherited locators (H8 at `45`, H9 at `48`, H10 at `54`, H11 at `82`) are not
re-wrapped in this slice; `check_handoff_exact`'s last conjunct is the universal suffix equality that
transports G3k's own four verbatim.  Also not here: no first arrival of the composed accept, fence,
converse, footprint theorem or pnp4 bridge; no exact rejection time on the mismatched branch; and no
`accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedContentGammaTerminator (gammaZeros?)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedContentGammaAnchor (successTime)
open Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (eraseChainClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_tailMachine : UniformTM := tailMachine
def check_inAlign :
    Fin FixedPairOriginAlignment.alignmentStateCount → Fin machine.stateCount := inAlign
def check_inTail : Fin tailMachine.stateCount → Fin machine.stateCount := inTail
def check_route :
    Fin FixedPairOriginAlignment.alignmentStateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_tailStartConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config tailMachine.stateCount (pairLength a m) B :=
  tailStartConfig
def check_switchTime (a m : Nat) : Nat := switchTime a m
def check_alignmentChainClock (C a m zeros d v : Nat) : Nat := alignmentChainClock C a m zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine = FixedPairOriginAlignment.machine.seq
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      tailMachine =
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      machine.stateCount = 177 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 531 ∧
      FixedPairOriginAlignment.machine.stateCount = 26 ∧ tailMachine.stateCount = 151 ∧
      FixedPairOriginAlignment.machine.start.val = 0 ∧
      FixedPairOriginAlignment.machine.accept.val = 24 ∧
      FixedPairOriginAlignment.machine.reject.val = 25 ∧
      tailMachine.start.val = 0 ∧ tailMachine.accept.val = 149 ∧ tailMachine.reject.val = 150 ∧
      machine.start = route FixedPairOriginAlignment.machine.start ∧
      machine.start = inAlign FixedPairOriginAlignment.machine.start ∧
      machine.accept = inTail tailMachine.accept ∧ machine.reject = inTail tailMachine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 175 ∧ machine.reject.val = 176 ∧
      (∀ q, (inAlign q).val = q.val) ∧ (∀ q, (inAlign q).val < 26) ∧
      (∀ q, (inTail q).val = 26 + q.val) ∧ (∀ q, 26 ≤ (inTail q).val) ∧
      Function.Injective inAlign ∧ Function.Injective inTail ∧
      (∀ p q, inAlign p ≠ inTail q) ∧
      tailStart = inTail tailMachine.start ∧ tailStart.val = 26 ∧
      route FixedPairOriginAlignment.machine.accept = tailStart ∧
      route FixedPairOriginAlignment.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedPairOriginAlignment.machine.accept →
        q ≠ FixedPairOriginAlignment.machine.reject → route q = inAlign q) ∧
      (∀ q s, machine.step (inAlign q) s =
        (route (FixedPairOriginAlignment.machine.step q s).1,
          (FixedPairOriginAlignment.machine.step q s).2.1,
          (FixedPairOriginAlignment.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1, (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inAlign ⟨10, by decide⟩) none = (tailStart, none, .left) ∧
      machine.step (inAlign ⟨11, by decide⟩) none = (tailStart, some false, .left) ∧
      machine.step (inAlign ⟨12, by decide⟩) none = (tailStart, some true, .left) ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inAlign q) s).1 ≠
          inAlign FixedPairOriginAlignment.machine.accept ∧
        (machine.step (inAlign q) s).1 ≠
          inAlign FixedPairOriginAlignment.machine.reject) :=
  table_and_resource_pins

/-- The three live rows into the alignment accept, restated in full. -/
theorem check_accept_rows_unique (q : Fin FixedPairOriginAlignment.alignmentStateCount)
    (s : Option Bool) (hq : q ≠ FixedPairOriginAlignment.machine.accept)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.accept) :
    (q.val = 10 ∨ q.val = 11 ∨ q.val = 12) ∧ s = none :=
  accept_rows_unique q s hq h

/-- The twenty-one live rows into the alignment reject, restated in full. -/
theorem check_reject_rows_unique (q : Fin FixedPairOriginAlignment.alignmentStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginAlignment.machine.accept)
    (hq : q ≠ FixedPairOriginAlignment.machine.reject)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.reject) :
    (s = none ∧ (q.val = 4 ∨ q.val = 5 ∨ q.val = 6 ∨ q.val = 16 ∨ q.val = 18)) ∨
      (s ≠ none ∧ (q.val = 0 ∨ q.val = 13 ∨ q.val = 14 ∨ q.val = 15 ∨ q.val = 19 ∨
        q.val = 20 ∨ q.val = 21 ∨ q.val = 23)) :=
  reject_rows_unique q s ha hq h

/-- The routing of every live row into the alignment reject, restated in full. -/
theorem check_reject_rows_routed (q : Fin FixedPairOriginAlignment.alignmentStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginAlignment.machine.accept)
    (hq : q ≠ FixedPairOriginAlignment.machine.reject)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.reject) :
    machine.step (inAlign q) s =
      (machine.reject, (FixedPairOriginAlignment.machine.rawStep q s).2.1,
        (FixedPairOriginAlignment.machine.rawStep q s).2.2) :=
  reject_rows_routed q s ha hq h

/-- The start as the retagged actual origin-shift-bootstrap endpoint, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginShiftBootstrap.machine.run (FixedPairOriginShiftBootstrap.clock a m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    let p := FixedPairOriginAlignment.startConfig B x w
    let c := startConfig B x w
    g = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      g.state = FixedPairOriginShiftBootstrap.qAccept ∧
      p = FixedPairOriginAlignment.retag g ∧
      p.state = FixedPairOriginAlignment.machine.start ∧ p.head = g.head ∧ p.tape = g.tape ∧
      c = FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine p ∧
      c.state = machine.start ∧ c.state = inAlign FixedPairOriginAlignment.machine.start ∧
      c.head = g.head ∧ c.tape = g.tape ∧ c.head.val = pairLength a m + Nat.min B 1 ∧
      c.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C a m zeros d v : Nat) :
    alignmentChainClock C a m zeros d v = switchTime a m + eraseChainClock C (a + m) zeros d v ∧
      switchTime a m = (10 * a + 7) * (a + m + 1) + 3 * a ∧
      switchTime a m = FixedPairOriginAlignment.clock a m ∧
      switchTime a m = 10 * a * a + 10 * a * m + 20 * a + 7 * m + 7 ∧
      switchTime 0 0 = 7 ∧ switchTime 0 2 = 21 ∧ switchTime 1 1 = 54 ∧ switchTime 2 0 = 87 ∧
      (∀ z : Nat,
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          z = z + 3) ∧
      (∀ a' m' : Nat, FixedContentTagGate.deadline a' m' = 3 * (a' + m') + 7) ∧
      (∀ z : Nat, successTime z = 2 * z + 5) ∧
      alignmentChainClock C a m zeros d v =
        switchTime a m + (a + m + 3 + (3 * (a + m) + 7 + (zeros + 1 + (2 * zeros + 5 +
          (C + bootChainClock (a + m) zeros d v))))) ∧
      (2 ≤ zeros → alignmentChainClock C a m zeros d v =
        switchTime a m + (a + m + 3 + (3 * (a + m) + 7 + (zeros + 1 + (2 * zeros + 5 +
          (C + (2 * (a + m) - 11 - zeros + (2 * (a + m) + zeros - 6 + (2 * (a + m) - 7 +
            (zeros + 7 + (totalClock (a + m) zeros +
              composedClock (a + m) zeros d v))))))))))) :=
  clock_pins C a m zeros d v

/-- The alignment phase's strict first arrival, restated in full. -/
theorem check_alignment_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime a m →
        (FixedPairOriginAlignment.machine.run t
            (FixedPairOriginAlignment.startConfig B x w)).state ≠
          FixedPairOriginAlignment.machine.accept ∧
        (FixedPairOriginAlignment.machine.run t
            (FixedPairOriginAlignment.startConfig B x w)).state ≠
          FixedPairOriginAlignment.machine.reject) ∧
      FixedPairOriginAlignment.machine.run (switchTime a m)
          (FixedPairOriginAlignment.startConfig B x w) =
        FixedPairOriginAlignment.finalConfig B x w ∧
      (FixedPairOriginAlignment.machine.run (switchTime a m)
          (FixedPairOriginAlignment.startConfig B x w)).state =
        FixedPairOriginAlignment.machine.accept ∧
      switchTime a m = FixedPairOriginAlignment.clock a m ∧
      (∀ t, (FixedPairOriginAlignment.machine.run t
          (FixedPairOriginAlignment.startConfig B x w)).state ≠
        FixedPairOriginAlignment.machine.reject) :=
  alignment_first_arrival x w

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_marker_erase_start_at_first_arrival {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m) :
    let g := FixedPairOriginAlignment.machine.run (switchTime a m)
      (FixedPairOriginAlignment.startConfig B x w)
    g = FixedPairOriginAlignment.finalConfig B x w ∧
      (FixedPairContentMarkerErase.startConfig B x w).state =
        FixedPairContentMarkerErase.machine.start ∧
      (FixedPairContentMarkerErase.startConfig B x w).head = g.head ∧
      (FixedPairContentMarkerErase.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  marker_erase_start_at_first_arrival x w

/-- The executed handoff H6 at the alignment phase's own clock, restated in full. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let cA := FixedPairOriginAlignment.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a m → (machine.run t c).state.val < 26) ∧
      (∀ t, t ≤ switchTime a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime a m → machine.run t c =
        FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine
          (FixedPairOriginAlignment.machine.run t cA)) ∧
      machine.run (switchTime a m) c =
        FixedPairOriginAlignment.machine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
      (∀ s, machine.run (switchTime a m + s) c =
        FixedPairOriginAlignment.machine.seqEmbedRight tailMachine
          (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.state.val = 26 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedPairContentMarkerErase.startConfig B x w).head ∧
      e.tape = (FixedPairContentMarkerErase.startConfig B x w).tape ∧
      e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w ∧
      e.tape ⟨a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 ≤ i.val → e.tape i = none) :=
  handoff_endpoint_pins x w

/-- The inherited H7 inside this machine, restated in full. -/
theorem check_inherited_marker_erase_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m + (a + m + 3)) (startConfig B x w)
    let p := FixedContentTagGate.startConfig B x w
    e.state.val = 30 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m ≤ i.val → e.tape i = none) :=
  inherited_marker_erase_switch x w

/-- The thirteen-phase exact run, restated in full. -/
theorem check_origin_alignment_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let D := alignmentChainClock C a m zeros d v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) :=
  origin_alignment_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject on a matching tag with no gamma terminator, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m)) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime a m +
            (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m)) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) :=
  malformed_reject_handoff x w htag hg

/-- The routed reject on a mismatched tag, restated in full. -/
theorem check_mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime a m + (a + m + 3 + (3 * (a + m) + 7)) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w :=
  mismatched_tag_reject_handoff x w htag

/-- The literal clocks the probes use, reduced by kernel computation.  The three values at `a + m = 2`
are the concrete witness that `switchTime` is **not** a function of `a + m`. -/
theorem check_clock_values :
    switchTime 0 0 = 7 ∧ switchTime 0 2 = 21 ∧ switchTime 1 1 = 54 ∧ switchTime 2 0 = 87 ∧
      switchTime 8 2 = 981 ∧ switchTime 8 3 = 1068 ∧ switchTime 8 9 = 1590 ∧
      switchTime 8 9 = FixedPairOriginAlignment.clock 8 9 ∧
      FixedContentTagGate.deadline 8 9 = 58 ∧ FixedContentGammaTerminator.deadline 8 3 = 4 ∧
      eraseChainClock 18 17 4 0 24 = 1212 ∧ alignmentChainClock 18 8 9 4 0 24 = 2802 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def badTag : Bitstring 8 := ![false, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def malformedWord : Bitstring 3 := ![false, false, false]
private def emptyWord : Bitstring 0 := fun i => i.elim0
private def probeX : Bitstring 1 := ![true]
private def probeW : Bitstring 1 := ![false]
private def probeT : Bitstring 1 := ![true]

/-- The whole observable configuration of the composed run on the `![true]`/`![false]` fixture at zero
budget: the control index, the head index and the **whole** five-cell allocated tape. -/
private def snap (t : Nat) : Nat × Nat × List (Option Bool) :=
  let c := machine.run t (startConfig 0 probeX probeW)
  (c.state.val, c.head.val, List.ofFn c.tape)

/-! ### Derived literal handoffs -/

set_option maxRecDepth 40000 in
/-- The three live routed accept rows and the two dead verdict copies' rows, as literals.  Each of the
three keeps its own restoration write — `none`, `some false`, `some true` — and its `.left`, and all
three land in `tailStart` at `26`; the dead accept copy's three rows go to `26` and the dead reject
copy's to `176`, and no left-block row targets either copy, so neither is ever occupied. -/
theorem check_accept_row_literals :
    machine.step (inAlign ⟨10, by decide⟩) none = (tailStart, none, .left) ∧
      machine.step (inAlign ⟨11, by decide⟩) none = (tailStart, some false, .left) ∧
      machine.step (inAlign ⟨12, by decide⟩) none = (tailStart, some true, .left) ∧
      tailStart.val = 26 ∧ machine.accept.val = 175 ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.reject) s =
        (machine.reject, s, .stay)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide

set_option maxRecDepth 40000 in
/-- Three of the twenty-one routed reject rows, **derived** from `reject_rows_routed` — a Boolean row
of state `0` and the `none` rows of states `4` and `18` — each keeping the alignment table's own
written symbol and its `stay` and landing in the composed reject `176`; and a state with no row into
the reject at all, `2`, whose every row goes to a working state.  This list of live reject rows is
complete on the left block, but says nothing about the right block, which keeps its own inherited rows
into `176`. -/
theorem check_reject_row_literals :
    machine.step (inAlign ⟨0, by decide⟩) (some true) = (machine.reject, some true, .stay) ∧
      machine.step (inAlign ⟨4, by decide⟩) none = (machine.reject, none, .stay) ∧
      machine.step (inAlign ⟨18, by decide⟩) none = (machine.reject, none, .stay) ∧
      machine.reject.val = 176 ∧
      (∀ s : Option Bool, (FixedPairOriginAlignment.machine.rawStep
          (⟨2, by decide⟩ : Fin FixedPairOriginAlignment.alignmentStateCount) s).1 ≠
        FixedPairOriginAlignment.machine.reject) := by
  refine ⟨?_, ?_, ?_, by decide, by decide⟩
  · exact reject_rows_routed _ (some true) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ none (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ none (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- H6 at the widest fixture, **derived**, with no hypothesis discharged because the theorem takes
none.  On `tag`/`physWord`: the control is strictly inside the left block `[0, 26)` at every time
before the switch `1590`, in neither composed verdict at any time up to and including it, and at
`1590` the run **is** G3k's actual `startConfig 0 tag physWord` re-embedded — control `26`, the origin
head `0`, the `alignedTape`, the trailing marker still `some true` on cell `17`, and every allocated
cell above `17` blank. -/
theorem check_handoff_literal :
    (∀ t, t < 1590 → (machine.run t (startConfig 0 tag physWord)).state.val < 26) ∧
    (∀ t, t ≤ 1590 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 1590 (startConfig 0 tag physWord) =
      FixedPairOriginAlignment.machine.seqEmbedRight tailMachine
        (tailStartConfig 0 tag physWord) ∧
    (machine.run 1590 (startConfig 0 tag physWord)).state.val = 26 ∧
    (machine.run 1590 (startConfig 0 tag physWord)).head.val = 0 ∧
    (machine.run 1590 (startConfig 0 tag physWord)).tape =
      FixedPairOriginAlignment.alignedTape 0 tag physWord ∧
    (machine.run 1590 (startConfig 0 tag physWord)).tape ⟨8 + 9, by decide⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength 8 9) 0), 8 + 9 + 1 ≤ i.val →
      (machine.run 1590 (startConfig 0 tag physWord)).tape i = none) := by
  obtain ⟨h0, h1, -, h2, -⟩ := handoff_exact (B := 0) tag physWord
  obtain ⟨-, h3, -, -, -, -, h4, h5, h6, h7⟩ := handoff_endpoint_pins (B := 0) tag physWord
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept `175` on the separator
blank `23` after exactly `2802` steps — `1590` for the origin alignment, none for H6, `20` for the
marker erasure, none for H7, `58` for the gate, `5` for the terminator, `13` for the anchor, `18` for
the dispatcher, then G3e's `1098` — persisting.  Nothing decodes the hand-written `24`, and persistence
is not first arrival of the composed accept. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (alignmentChainClock 18 8 9 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, alignmentChainClock 18 8 9 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    origin_alignment_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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

/-- The routed reject at the malformed fixture, derived: no composed verdict before `1126` — the
alignment switch `1068`, the marker erasure's `14`, the gate's `40` and the terminator's length-only
deadline `4` — and the composed reject `176` from it on, at `1126` and again at `1130`, there on the
boundary head `11` over the erased content tape.  Both the tag hypothesis and the no-gamma hypothesis
are discharged here. -/
theorem check_malformed_literal :
    (∀ t, t < 1126 → (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.reject) ∧
    (machine.run 1126 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 1126 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 1126 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 1130 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨hpre, hpost⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide)
  obtain ⟨h1, h2, h3⟩ := hpost 1126 (by decide)
  obtain ⟨h4, -, -⟩ := hpost 1130 (by decide)
  exact ⟨hpre, h1, h2, h3, h4⟩

/-- The routed reject at the mismatched fixture, derived: from `1122` on — the alignment switch `1068`,
the marker erasure's `14` plus the gate's length-only deadline `40` — at `1122` and again at `1126`,
the composed reject `176` on the gate's own `finalConfig` head, here the mismatch cell `0`, over the
erased content tape.  No claim is made about any earlier time: this is the gate's deadline, not its
first rejection. -/
theorem check_mismatched_literal :
    (machine.run 1122 (startConfig 0 badTag tightWord)).state = machine.reject ∧
    (machine.run 1122 (startConfig 0 badTag tightWord)).head =
      (FixedContentTagGate.finalConfig 0 badTag tightWord).head ∧
    (machine.run 1122 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 1122 (startConfig 0 badTag tightWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 badTag tightWord ∧
    (machine.run 1126 (startConfig 0 badTag tightWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 1122 (by decide)
  obtain ⟨h4, -, -⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 1126 (by decide)
  refine ⟨h1, h2, ?_, h3, h4⟩
  rw [h2]
  decide

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 4000000 in
/-- **H6 and the routed row of state `11`, reduced.**  Out of the actual `startConfig 0 probeX probeW`
with `probeX = ![true]` and `probeW = ![false]`: at step `0` the alignment start `0` on the source head
`4 = pairLength 1 1`, over the once-shifted tape; at step `53` the classification state `11` on cell
`1`, which that cell has been blanked to probe; at step `54 = switchTime 1 1` the control has left the
left block for `tailStart` (`26`) on the origin cell `0`, and cell `1` carries `some false` again — the
restoration write is performed by the routed row of the composed table itself, in the transition that
hands over.  The marker-erase scan then walks right to the first physical blank `3` at step `57`, steps
left into `qErase` (`27`) at `58`, and at `59 = 54 + (N + 3)` the inherited H7 row has fired into the
tag gate's start (`30`) with the trailing marker on cell `2` now erased.  Each triple is the whole
control index, the whole head index and the **whole** allocated five-cell tape.  No slice theorem is
used. -/
theorem check_h6_literal_probe :
    snap 0 = (0, 4, [none, some true, some false, some true, none]) ∧
    snap 53 = (11, 1, [some true, none, some true, none, none]) ∧
    snap 54 = (26, 0, [some true, some false, some true, none, none]) ∧
    snap 55 = (26, 1, [some true, some false, some true, none, none]) ∧
    snap 58 = (27, 2, [some true, some false, some true, none, none]) ∧
    snap 59 = (30, 2, [some true, some false, none, none, none]) := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The other two live H6 rows, and a positive budget, reduced.**  Empty inputs with `B = 0`:
`switchTime 0 0 = 7`, at step `6` the control is the classification state `10`, at `7` it is
`tailStart` (`26`) on the origin cell `0` with the marker still `some true` on cell `0`, and at
`10 = 7 + (0 + 3)` the inherited H7 row has erased it and handed over to the tag gate's start (`30`);
the routed row of state `10` writes `none`, which is what cell `1` already held.  `![true]`/`![true]`
with `B = 0`: at step `53` the control is the classification state `12` and at `54` it is `26` with
cell `1` restored to `some true` — the third live routed row, writing a different symbol.  `B = 1`
moves the source head from `4` to `5` and changes neither the switch time nor the handed-over
configuration.  No slice theorem is used. -/
theorem check_h6_accept_row_probes :
    (machine.run 6 (startConfig 0 emptyWord emptyWord)).state.val = 10 ∧
    (machine.run 7 (startConfig 0 emptyWord emptyWord)).state.val = 26 ∧
    (machine.run 7 (startConfig 0 emptyWord emptyWord)).head.val = 0 ∧
    List.ofFn (machine.run 7 (startConfig 0 emptyWord emptyWord)).tape = [some true, none] ∧
    (machine.run 10 (startConfig 0 emptyWord emptyWord)).state.val = 30 ∧
    List.ofFn (machine.run 10 (startConfig 0 emptyWord emptyWord)).tape = [none, none] ∧
    (machine.run 53 (startConfig 0 probeX probeT)).state.val = 12 ∧
    (machine.run 54 (startConfig 0 probeX probeT)).state.val = 26 ∧
    (machine.run 54 (startConfig 0 probeX probeT)).head.val = 0 ∧
    List.ofFn (machine.run 54 (startConfig 0 probeX probeT)).tape =
      [some true, some true, some true, none, none] ∧
    (machine.run 0 (startConfig 1 probeX probeW)).head.val = 5 ∧
    (machine.run 54 (startConfig 1 probeX probeW)).state.val = 26 ∧
    (machine.run 54 (startConfig 1 probeX probeW)).head.val = 0 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The composed reject is entered through the right block, reduced.**  Out of
`startConfig 0 probeX probeW` the content is two cells long, so the inherited tag gate cannot match its
eight-bit tag: at step `66` the control is a working right-block state `37` in neither composed verdict,
at `67` it is the composed reject `176`, and it is still there at `80`.  The left block's twenty-one
reject rows are *not* what was taken — the control never leaves `[0, 26)` before `54` and enters the
right block there — so this exhibits the composed reject as reachable only through the inherited
block.  No slice theorem is used. -/
theorem check_composed_reject_probe :
    snap 66 = (37, 2, [some true, some false, none, none, none]) ∧
    (machine.run 66 (startConfig 0 probeX probeW)).state ≠ machine.accept ∧
    (machine.run 66 (startConfig 0 probeX probeW)).state ≠ machine.reject ∧
    snap 67 = (176, 2, [some true, some false, none, none, none]) ∧
    snap 80 = (176, 2, [some true, some false, none, none, none]) := by
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
