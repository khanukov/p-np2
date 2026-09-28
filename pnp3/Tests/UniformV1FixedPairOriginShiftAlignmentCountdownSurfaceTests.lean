import Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown
/-!
Surface pins for the Part A G3m concrete slice: the fixed 7-state, 21-row structural one-cell origin
shift followed by the whole landed G3l composite, as **one** closed 184-state, 552-row table.  Its
newly executed handoff H5 has exactly **one** live routed row — the bootstrap fetch state `4` on
`none`, proved by `accept_rows_unique` the only row targeting the phase's accept once the accept's own
three are excluded — into G3l's start `tailStart` at index `7`, keeping its written `none` and its
`.stay`.  Exactly **six** rows target the bootstrap reject — either Boolean on each of the states `1`,
`2`, `3` — `reject_rows_unique` proving that an **equivalence**, and `seq` routes each to the composed
reject `183`.  None is taken out of this `startConfig`: the left block never rejects at any time.  Both
dead left verdict copies are no composed row's target, and the composed start is neither.  H6 (three
rows, `17`, `18` and `19`, all into `33`) to H17 (`170 → 173`) are inherited from G3l, its indices
shifted by seven.  Every public declaration is restated in full.

The switch time.  `switchTime a m = 4 * a + 3 * m + 5` is linear, and far below G3l's quadratic `1590`
at `a = 8`, `m = 9`, though *not* the smallest switch time in the chain — the length-only `N + 3` and
`3 * N + 7` are both smaller there.  It still reads the split lengths `a` and `m` apart:
`check_clock_values` reduces the three pairs with `a + m = 2` to `11`, `12` and `13`.  G3l's own
quadratic switch time is unchanged, so the composed clock stays quadratic in `a` and no claim is made
that the cubic budget dominates it.

The probes.  Kernel reduction of `machine.run` is quadratic in the step count, and the tagged fixtures
all have `a = 8`, so reaching G3l's own switch at `64 + 1590` overflows the kernel stack.  The
`check_*_probe` theorems — which use **no** slice theorem — therefore run on tiny tag-free fixtures,
which is sound because the bootstrap phase scans those cells but does not test their tag, gamma, or bit
meaning — it only shifts the block one cell left: empty inputs (`switchTime 0 0 = 5`) at **both**
`B = 0` and `B = 1`, and `![true]`/`![false]` (`switchTime 1 1 = 12`) at both budgets, exhibit the whole
allocated tape at and before the switch, the single live routed row firing `4 → 7` on a **blank** cell
with a **stationary** head, both carry states `2` and `1` on the way — each on a blank cell, so each
takes its shifting `none` row and not its rejecting Boolean one — the two budgets moving the source head
from `1` to `2` and from `4` to `5` while the switch step itself clamps on neither, the
inherited H6 `tailSwitchTime a m` later at index `33` on the `alignedTape`, the inherited H7 `N + 3`
after that at index `37` with the marker erased, and the composed reject `183` entered through the
**right** block when the inherited tag gate rejects the short content.  The tagged fixtures are kept for
the `check_*_literal*` theorems, which are **derived** from the slice's own theorems and so cost no
`run` reduction: `tag`/`physWord` switches at `64`, reaches the inherited H6 at `1654` and H7 at `1674`
and drains at `2866 = 64 + 2802`; the malformed fixture rejects from `1172` on and the mismatched one
from `1168` on.

Not here: the composed `startConfig` still embeds the four earlier phases as a retag of the actual
tag-removal `finalConfig`, so there is no raw-input run and none of those four is **executed** by this
table.  One of them is pinned, as an identification and not as an executed row: `check_handoff_pins`
records H4 — the bootstrap `startConfig` is the tag-removal `finalConfig` at its own clock, retagged,
with no hypothesis — together with the fact that the composed start is **not** G3l's start re-embedded,
and no table row of any earlier phase is pinned anywhere here.  The deeper inherited locators (H8, H9,
H10, H11 and below) are not re-wrapped in this slice; `check_handoff_exact`'s last conjunct is the
universal suffix equality that transports G3l's own verbatim.  Also not here: no first arrival of the
composed accept, fence, converse, footprint theorem or pnp4 bridge; no exact rejection time on the
mismatched branch; and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership
statement. -/
namespace Pnp3.Tests.UniformV1FixedPairOriginShiftAlignmentCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown
open Complexity.Uniform.V1.FixedContentGammaTerminator (gammaZeros?)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (eraseChainClock)
open Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (alignmentChainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_tailMachine : UniformTM := tailMachine
def check_inShift :
    Fin FixedPairOriginShiftBootstrap.shiftStateCount → Fin machine.stateCount := inShift
def check_inTail : Fin tailMachine.stateCount → Fin machine.stateCount := inTail
def check_route :
    Fin FixedPairOriginShiftBootstrap.shiftStateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_tailStartConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config tailMachine.stateCount (pairLength a m) B :=
  tailStartConfig
def check_switchTime (a m : Nat) : Nat := switchTime a m
def check_tailSwitchTime (a m : Nat) : Nat := tailSwitchTime a m
def check_shiftChainClock (C a m zeros d v : Nat) : Nat := shiftChainClock C a m zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine = FixedPairOriginShiftBootstrap.machine.seq
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      tailMachine =
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      machine.stateCount = 184 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 552 ∧
      FixedPairOriginShiftBootstrap.machine.stateCount = 7 ∧ tailMachine.stateCount = 177 ∧
      FixedPairOriginShiftBootstrap.machine.start.val = 0 ∧
      FixedPairOriginShiftBootstrap.machine.accept.val = 5 ∧
      FixedPairOriginShiftBootstrap.machine.reject.val = 6 ∧
      tailMachine.start.val = 0 ∧ tailMachine.accept.val = 175 ∧ tailMachine.reject.val = 176 ∧
      machine.start = route FixedPairOriginShiftBootstrap.machine.start ∧
      machine.start = inShift FixedPairOriginShiftBootstrap.machine.start ∧
      machine.accept = inTail tailMachine.accept ∧ machine.reject = inTail tailMachine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 182 ∧ machine.reject.val = 183 ∧
      (∀ q, (inShift q).val = q.val) ∧ (∀ q, (inShift q).val < 7) ∧
      (∀ q, (inTail q).val = 7 + q.val) ∧ (∀ q, 7 ≤ (inTail q).val) ∧
      Function.Injective inShift ∧ Function.Injective inTail ∧
      (∀ p q, inShift p ≠ inTail q) ∧
      (∀ q : Fin machine.stateCount, (∃ p, q = inShift p) ∨ (∃ p, q = inTail p)) ∧
      tailStart = inTail tailMachine.start ∧ tailStart.val = 7 ∧
      route FixedPairOriginShiftBootstrap.machine.accept = tailStart ∧
      route FixedPairOriginShiftBootstrap.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedPairOriginShiftBootstrap.machine.accept →
        q ≠ FixedPairOriginShiftBootstrap.machine.reject → route q = inShift q) ∧
      (∀ q s, machine.step (inShift q) s =
        (route (FixedPairOriginShiftBootstrap.machine.step q s).1,
          (FixedPairOriginShiftBootstrap.machine.step q s).2.1,
          (FixedPairOriginShiftBootstrap.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1, (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inShift ⟨4, by decide⟩) none = (tailStart, none, .stay) ∧
      (∀ b : Bool, machine.step (inShift ⟨1, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ b : Bool, machine.step (inShift ⟨2, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ b : Bool, machine.step (inShift ⟨3, by decide⟩) (some b) =
        (machine.reject, some b, .stay)) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inShift q) s).1 ≠
          inShift FixedPairOriginShiftBootstrap.machine.accept ∧
        (machine.step (inShift q) s).1 ≠
          inShift FixedPairOriginShiftBootstrap.machine.reject) :=
  table_and_resource_pins

/-- The single live row into the bootstrap accept, restated in full. -/
theorem check_accept_rows_unique (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (hq : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (h : (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
      FixedPairOriginShiftBootstrap.machine.accept) :
    q.val = 4 ∧ s = none :=
  accept_rows_unique q s hq h

/-- The six rows into the bootstrap reject, restated in full: both directions. -/
theorem check_reject_rows_unique (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (hq : q ≠ FixedPairOriginShiftBootstrap.machine.reject) :
    (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
        FixedPairOriginShiftBootstrap.machine.reject ↔
      (s ≠ none ∧ (q.val = 1 ∨ q.val = 2 ∨ q.val = 3)) :=
  reject_rows_unique q s ha hq

/-- The routing of every live row into the bootstrap reject, restated in full. -/
theorem check_reject_rows_routed (q : Fin FixedPairOriginShiftBootstrap.shiftStateCount)
    (s : Option Bool) (ha : q ≠ FixedPairOriginShiftBootstrap.machine.accept)
    (hq : q ≠ FixedPairOriginShiftBootstrap.machine.reject)
    (h : (FixedPairOriginShiftBootstrap.machine.rawStep q s).1 =
      FixedPairOriginShiftBootstrap.machine.reject) :
    machine.step (inShift q) s =
      (machine.reject, (FixedPairOriginShiftBootstrap.machine.rawStep q s).2.1,
        (FixedPairOriginShiftBootstrap.machine.rawStep q s).2.2) :=
  reject_rows_routed q s ha hq h

/-- The start as the retagged actual tag-removal endpoint, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let r := FixedPairTagRemoval.machine.run (FixedPairTagRemoval.clock a)
      (FixedPairTagRemoval.startConfig B x w)
    let p := FixedPairOriginShiftBootstrap.startConfig B x w
    let c := startConfig B x w
    r = FixedPairTagRemoval.finalConfig B x w ∧
      r.state = FixedPairTagRemoval.qAccept ∧
      p = FixedPairOriginShiftBootstrap.retag r ∧
      p.state = FixedPairOriginShiftBootstrap.machine.start ∧ p.head = r.head ∧ p.tape = r.tape ∧
      c = FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine p ∧
      c.state = machine.start ∧ c.state = inShift FixedPairOriginShiftBootstrap.machine.start ∧
      c.head = r.head ∧ c.tape = r.tape ∧ c.head.val = 0 ∧
      c.tape = FixedPairTagRemoval.compactTape B x w ∧
      c ≠ FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
        (tailStartConfig B x w) :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C a m zeros d v : Nat) :
    shiftChainClock C a m zeros d v = switchTime a m + alignmentChainClock C a m zeros d v ∧
      switchTime a m = 4 * a + 3 * m + 5 ∧
      switchTime a m = FixedPairOriginShiftBootstrap.clock a m ∧
      switchTime a m = (a + 1) + 3 * (a + m + 1) + 1 ∧
      5 ≤ switchTime a m ∧
      switchTime 0 0 = 5 ∧ switchTime 0 2 = 11 ∧ switchTime 1 1 = 12 ∧ switchTime 2 0 = 13 ∧
      tailSwitchTime a m =
        FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          a m ∧
      tailSwitchTime a m = (10 * a + 7) * (a + m + 1) + 3 * a ∧
      tailSwitchTime a m = FixedPairOriginAlignment.clock a m ∧
      tailSwitchTime 0 2 = 21 ∧ tailSwitchTime 1 1 = 54 ∧ tailSwitchTime 2 0 = 87 ∧
      alignmentChainClock C a m zeros d v =
        tailSwitchTime a m + eraseChainClock C (a + m) zeros d v ∧
      shiftChainClock C a m zeros d v =
        4 * a + 3 * m + 5 +
          ((10 * a + 7) * (a + m + 1) + 3 * a + eraseChainClock C (a + m) zeros d v) :=
  clock_pins C a m zeros d v

/-- The bootstrap phase's strict first arrival, restated in full. -/
theorem check_bootstrap_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime a m →
        (FixedPairOriginShiftBootstrap.machine.run t
            (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
          FixedPairOriginShiftBootstrap.machine.accept ∧
        (FixedPairOriginShiftBootstrap.machine.run t
            (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
          FixedPairOriginShiftBootstrap.machine.reject) ∧
      FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
          (FixedPairOriginShiftBootstrap.startConfig B x w) =
        FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      (FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
          (FixedPairOriginShiftBootstrap.startConfig B x w)).state =
        FixedPairOriginShiftBootstrap.machine.accept ∧
      switchTime a m = FixedPairOriginShiftBootstrap.clock a m ∧
      (∀ t, (FixedPairOriginShiftBootstrap.machine.run t
          (FixedPairOriginShiftBootstrap.startConfig B x w)).state ≠
        FixedPairOriginShiftBootstrap.machine.reject) :=
  bootstrap_first_arrival x w

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_alignment_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginShiftBootstrap.machine.run (switchTime a m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    g = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      (FixedPairOriginAlignment.startConfig B x w).state =
        FixedPairOriginAlignment.machine.start ∧
      (FixedPairOriginAlignment.startConfig B x w).head = g.head ∧
      (FixedPairOriginAlignment.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  alignment_start_at_first_arrival x w

/-- The executed handoff H5 at the bootstrap phase's own clock, restated in full. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let cS := FixedPairOriginShiftBootstrap.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a m → (machine.run t c).state.val < 7) ∧
      (∀ t, t ≤ switchTime a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime a m → machine.run t c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRouted tailMachine
          (FixedPairOriginShiftBootstrap.machine.run t cS)) ∧
      machine.run (switchTime a m) c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
      (∀ s, machine.run (switchTime a m + s) c =
        FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
          (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.state.val = 7 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedPairOriginAlignment.startConfig B x w).head ∧
      e.tape = (FixedPairOriginAlignment.startConfig B x w).tape ∧
      e.head.val = pairLength a m + Nat.min B 1 ∧
      e.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val < a → e.tape i = none) ∧
      (∀ j : Fin (a + m), e.tape ⟨a + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
      e.tape ⟨2 * a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), pairLength a m ≤ i.val → e.tape i = none) ∧
      (0 < a → e.tape ≠ FixedPairOriginAlignment.alignedTape B x w) :=
  handoff_endpoint_pins x w

/-- The inherited H6 and H7 inside this machine, restated in full. -/
theorem check_inherited_alignment_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m + tailSwitchTime a m) (startConfig B x w)
    let p :=
      FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailStartConfig
        B x w
    e.state.val = 33 ∧ e.head = p.head ∧ e.tape = p.tape ∧ e.head.val = 0 ∧
      e.tape = FixedPairOriginAlignment.alignedTape B x w ∧
      e.tape ⟨a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 ≤ i.val → e.tape i = none) ∧
      (machine.run (switchTime a m + (tailSwitchTime a m + (a + m + 3)))
        (startConfig B x w)).state.val = 37 :=
  inherited_alignment_switch x w

/-- The fourteen-phase exact run, restated in full. -/
theorem check_shift_alignment_countdown_drained {a m B C zeros v F : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let D := shiftChainClock C a m zeros d v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) :=
  shift_alignment_countdown_drained x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject on a matching tag with no gamma terminator, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime a m + (tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime a m + (tailSwitchTime a m +
            (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) :=
  malformed_reject_handoff x w htag hg

/-- The routed reject on a mismatched tag, restated in full. -/
theorem check_mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime a m + (tailSwitchTime a m + (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w :=
  mismatched_tag_reject_handoff x w htag

/-- The literal clocks the probes use, reduced by kernel computation.  The three values at `a + m = 2`
are the concrete witness that `switchTime` is **not** a function of `a + m`, and the last three lines
are the exact arithmetic of the composed clock at the tagged fixture: the new prefix contributes `64`
and G3l's landed sum `2802`, with no extra step. -/
theorem check_clock_values :
    switchTime 0 0 = 5 ∧ switchTime 0 2 = 11 ∧ switchTime 1 1 = 12 ∧ switchTime 2 0 = 13 ∧
      switchTime 8 3 = 46 ∧ switchTime 8 9 = 64 ∧
      switchTime 8 9 = FixedPairOriginShiftBootstrap.clock 8 9 ∧
      tailSwitchTime 0 0 = 7 ∧ tailSwitchTime 1 1 = 54 ∧ tailSwitchTime 8 3 = 1068 ∧
      tailSwitchTime 8 9 = 1590 ∧
      switchTime 8 9 + tailSwitchTime 8 9 = 1654 ∧
      switchTime 8 9 + (tailSwitchTime 8 9 + (8 + 9 + 3)) = 1674 ∧
      FixedContentTagGate.deadline 8 3 = 40 ∧ FixedContentGammaTerminator.deadline 8 3 = 4 ∧
      eraseChainClock 18 17 4 0 24 = 1212 ∧ alignmentChainClock 18 8 9 4 0 24 = 2802 ∧
      shiftChainClock 18 8 9 4 0 24 = 2866 ∧ (2866 : Nat) = 64 + 2802 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- The same for the empty fixture at unit budget: three allocated cells. -/
private def snapE (t : Nat) : Nat × Nat × List (Option Bool) :=
  let c := machine.run t (startConfig 1 emptyWord emptyWord)
  (c.state.val, c.head.val, List.ofFn c.tape)

/-! ### Derived literal handoffs -/

set_option maxRecDepth 40000 in
/-- The single live routed accept row, the six live routed reject rows and the two dead verdict copies'
rows, as literals.  The accept row keeps its written `none` and its `.stay` and lands in `tailStart` at
`7`; each of the six reject rows keeps the scanned Boolean and its `.stay` and lands in `183`; the dead
accept copy's three rows go to `7` and the dead reject copy's to `183`, and no left-block row targets
either copy, so neither is ever occupied. -/
theorem check_row_literals :
    machine.step (inShift ⟨4, by decide⟩) none = (tailStart, none, .stay) ∧
      tailStart.val = 7 ∧ machine.accept.val = 182 ∧ machine.reject.val = 183 ∧
      machine.step (inShift ⟨1, by decide⟩) (some false) = (machine.reject, some false, .stay) ∧
      machine.step (inShift ⟨1, by decide⟩) (some true) = (machine.reject, some true, .stay) ∧
      machine.step (inShift ⟨2, by decide⟩) (some false) = (machine.reject, some false, .stay) ∧
      machine.step (inShift ⟨2, by decide⟩) (some true) = (machine.reject, some true, .stay) ∧
      machine.step (inShift ⟨3, by decide⟩) (some false) = (machine.reject, some false, .stay) ∧
      machine.step (inShift ⟨3, by decide⟩) (some true) = (machine.reject, some true, .stay) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inShift FixedPairOriginShiftBootstrap.machine.reject) s =
        (machine.reject, s, .stay)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reject_rows_routed _ (some false) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ (some true) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ (some false) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ (some true) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ (some false) (by decide) (by decide) (by decide)
  · exact reject_rows_routed _ (some true) (by decide) (by decide) (by decide)
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide

set_option maxRecDepth 8192 in
/-- H5 at the widest fixture, **derived**, with no hypothesis discharged because the theorem takes
none.  On `tag`/`physWord` at zero budget: the control is strictly inside the left block `[0, 7)` at
every time before the switch `64`, in neither composed verdict at any time up to and including it, and
at `64` the run **is** G3l's actual `startConfig 0 tag physWord` re-embedded — control `7`, the source
head `26 = pairLength 8 9`, the `shiftedTape`, the trailing marker still `some true` on cell
`25 = 2 * 8 + 9`, every allocated cell from `26` on blank, the prefix below `8` blank, and — since
`0 < 8` — a tape that is **not** the `alignedTape`: the origin alignment has yet to run. -/
theorem check_handoff_literal :
    (∀ t, t < 64 → (machine.run t (startConfig 0 tag physWord)).state.val < 7) ∧
    (∀ t, t ≤ 64 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 64 (startConfig 0 tag physWord) =
      FixedPairOriginShiftBootstrap.machine.seqEmbedRight tailMachine
        (tailStartConfig 0 tag physWord) ∧
    (machine.run 64 (startConfig 0 tag physWord)).state.val = 7 ∧
    (machine.run 64 (startConfig 0 tag physWord)).head.val = 26 ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape =
      FixedPairOriginShiftBootstrap.shiftedTape 0 tag physWord ∧
    (∀ i : Fin (tapeLength (pairLength 8 9) 0), i.val < 8 →
      (machine.run 64 (startConfig 0 tag physWord)).tape i = none) ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨2 * 8 + 9, by decide⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength 8 9) 0), pairLength 8 9 ≤ i.val →
      (machine.run 64 (startConfig 0 tag physWord)).tape i = none) ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ≠
      FixedPairOriginAlignment.alignedTape 0 tag physWord := by
  obtain ⟨h0, h1, -, h2, -⟩ := handoff_exact (B := 0) tag physWord
  obtain ⟨-, h3, -, -, -, -, h4, h5, h6, -, h7, h8, h9⟩ :=
    handoff_endpoint_pins (B := 0) tag physWord
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9 (by omega)⟩

set_option maxRecDepth 8192 in
/-- The two inherited switches at the widest fixture, derived: the origin alignment hands over
`1590` steps after H5, at `1654`, at index `33` on the origin cell `0` over the `alignedTape` with the
trailing marker still `some true` on cell `17`; the marker erasure hands over `20` steps after that, at
`1674`, at index `37`. -/
theorem check_inherited_literal :
    (machine.run 1654 (startConfig 0 tag physWord)).state.val = 33 ∧
    (machine.run 1654 (startConfig 0 tag physWord)).head.val = 0 ∧
    (machine.run 1654 (startConfig 0 tag physWord)).tape =
      FixedPairOriginAlignment.alignedTape 0 tag physWord ∧
    (machine.run 1654 (startConfig 0 tag physWord)).tape ⟨8 + 9, by decide⟩ = some true ∧
    (machine.run 1674 (startConfig 0 tag physWord)).state.val = 37 := by
  obtain ⟨h1, -, -, h2, h3, h4, -, h5⟩ := inherited_alignment_switch (B := 0) tag physWord
  exact ⟨h1, h2, h3, h4, h5⟩

set_option maxRecDepth 40000 in
/-- The composed endpoint at the physical fixture, derived: the composed accept `182` on the separator
blank `23` after exactly `2866` steps — `64` for the origin shift, none for H5, `1590` for the origin
alignment, none for H6, `20` for the marker erasure, `58` for the gate, `5` for the terminator, `13` for
the anchor, `18` for the dispatcher, then G3e's `1098` — persisting.  All eight premises are discharged
here.  Nothing decodes the hand-written register value `24`: this is execution nonvacuity, not
`ContentAccepts` nonvacuity, and persistence is not first arrival of the composed accept. -/
theorem check_drained_literal_endpoint :
    let e := machine.run 2866 (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.state.val = 182 ∧ e.head.val = 23 ∧
      e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, 2866 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  have hc : shiftChainClock (3 * 4 + 6) 8 9 4 0 24 = 2866 := rfl
  obtain ⟨h1, h2, h3, h4⟩ :=
    shift_alignment_countdown_drained
      (a := 8) (m := 9) (B := 22) (C := 3 * 4 + 6) (zeros := 4) (v := 24) (F := 24) tag physWord
      (by decide) (by decide)
      (first_true_strict_first_terminal (zeros := 4) tag physWord (by decide) (by decide)
        (by omega) (by decide) (by decide)).1
      (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  rw [hc] at h1 h2 h3 h4
  refine ⟨h1, ?_, h2, h3, h4⟩
  rw [h1]; decide

/-- The routed reject at the malformed fixture, derived: no composed verdict before `1172` — the origin
shift's `46`, the origin alignment's `1068`, the marker erasure's `14`, the gate's `40` and the
terminator's length-only deadline `4` — and the composed reject `183` from it on, at `1172` and again at
`1176`, there on the boundary head `11` over the erased content tape.  Both the tag hypothesis and the
no-gamma hypothesis are discharged here. -/
theorem check_malformed_literal :
    (∀ t, t < 1172 → (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.reject) ∧
    (machine.run 1172 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 1172 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 1172 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 1176 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨hpre, hpost⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide)
  obtain ⟨h1, h2, h3⟩ := hpost 1172 (by decide)
  obtain ⟨h4, -, -⟩ := hpost 1176 (by decide)
  exact ⟨hpre, h1, h2, h3, h4⟩

/-- The routed reject at the mismatched fixture, derived: from `1168` on — the origin shift's `46`, the
origin alignment's `1068`, the marker erasure's `14` plus the gate's length-only deadline `40` — at
`1168` and again at `1172`, the composed reject `183` on the gate's own `finalConfig` head, here the
mismatch cell `0`, over the erased content tape.  No claim is made about any earlier time: this is the
gate's deadline, not its first rejection. -/
theorem check_mismatched_literal :
    (machine.run 1168 (startConfig 0 badTag tightWord)).state = machine.reject ∧
    (machine.run 1168 (startConfig 0 badTag tightWord)).head =
      (FixedContentTagGate.finalConfig 0 badTag tightWord).head ∧
    (machine.run 1168 (startConfig 0 badTag tightWord)).head.val = 0 ∧
    (machine.run 1168 (startConfig 0 badTag tightWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 badTag tightWord ∧
    (machine.run 1172 (startConfig 0 badTag tightWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 1168 (by decide)
  obtain ⟨h4, -, -⟩ :=
    mismatched_tag_reject_handoff (B := 0) badTag tightWord (by decide) 1172 (by decide)
  refine ⟨h1, h2, ?_, h3, h4⟩
  rw [h2]
  decide

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 4000000 in
/-- **H5, reduced.**  Out of the actual `startConfig 0 probeX probeW` with `probeX = ![true]` and
`probeW = ![false]`: at step `0` the bootstrap start `0` on the tag-removal origin head `0`, over the
`compactTape` whose block sits on cells `2, 3, 4`; at steps `3` and `6` the carry states `2` and `1` —
holding a scanned `some true` and `some false` — each over a **blank** cell, so each takes its shifting
`none` row and neither takes its rejecting Boolean one; at step `11` the fetch state `4` on cell `4`,
which the tape shows **blank**; and at step `12 = switchTime 1 1` the control has left the left block
for `tailStart`
(`7`) on that same cell `4` — the single live routed row fires on a blank cell and does not move, so it
clamps on neither budget, and the block now sits one cell lower, on `1, 2, 3`.  G3l then runs: at step
`66 = 12 + 54` the inherited H6 row has fired into index `33` on the origin cell `0` over the
`alignedTape`, and at `71 = 66 + (N + 3)` the inherited H7 row has fired into index `37` with the
trailing marker erased.  Each triple is the whole control index, the whole head index and the **whole**
allocated five-cell tape.  No slice theorem is used. -/
theorem check_h5_literal_probe :
    snap 0 = (0, 0, [none, none, some true, some false, some true]) ∧
    snap 3 = (2, 1, [none, none, none, some false, some true]) ∧
    snap 6 = (1, 2, [none, some true, none, none, some true]) ∧
    snap 11 = (4, 4, [none, some true, some false, some true, none]) ∧
    snap 12 = (7, 4, [none, some true, some false, some true, none]) ∧
    snap 66 = (33, 0, [some true, some false, some true, none, none]) ∧
    snap 71 = (37, 2, [some true, some false, none, none, none]) := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The budget boundary and the empty fixture, reduced.**  Empty inputs: `switchTime 0 0 = 5`, so at
step `4` the control is the fetch state `4` and at `5` it is `tailStart` (`7`), the head staying where it
was — cell `1 = pairLength 0 0` at `B = 0` and cell `2` at `B = 1`, which is the only difference the
budget makes, and the `.stay` of the routed row is why the switch itself clamps on neither.  At
`12 = 5 + 7` the inherited H6 row has fired into index `33` on the origin cell `0`, the trailing marker
still `some true` there, and at `15 = 12 + (0 + 3)` the inherited H7 row has erased it and handed over
to index `37`.  The `![true]`/`![false]` fixture shows the same boundary at `a = m = 1`: the source head
is `4` at `B = 0` and `5` at `B = 1`, and both reach `tailStart` at the same step `12`.
`![true]`/`![true]` exercises the switch on a different word.  No slice theorem is used. -/
theorem check_h5_boundary_probes :
    (machine.run 4 (startConfig 0 emptyWord emptyWord)).state.val = 4 ∧
    (machine.run 4 (startConfig 0 emptyWord emptyWord)).head.val = 1 ∧
    (machine.run 5 (startConfig 0 emptyWord emptyWord)).state.val = 7 ∧
    (machine.run 5 (startConfig 0 emptyWord emptyWord)).head.val = 1 ∧
    List.ofFn (machine.run 5 (startConfig 0 emptyWord emptyWord)).tape = [some true, none] ∧
    (machine.run 12 (startConfig 0 emptyWord emptyWord)).state.val = 33 ∧
    (machine.run 12 (startConfig 0 emptyWord emptyWord)).head.val = 0 ∧
    List.ofFn (machine.run 12 (startConfig 0 emptyWord emptyWord)).tape = [some true, none] ∧
    (machine.run 15 (startConfig 0 emptyWord emptyWord)).state.val = 37 ∧
    List.ofFn (machine.run 15 (startConfig 0 emptyWord emptyWord)).tape = [none, none] ∧
    snapE 4 = (4, 2, [some true, none, none]) ∧
    snapE 5 = (7, 2, [some true, none, none]) ∧
    snapE 12 = (33, 0, [some true, none, none]) ∧
    snapE 15 = (37, 0, [none, none, none]) ∧
    (machine.run 11 (startConfig 1 probeX probeW)).head.val = 5 ∧
    (machine.run 12 (startConfig 1 probeX probeW)).state.val = 7 ∧
    (machine.run 12 (startConfig 1 probeX probeW)).head.val = 5 ∧
    (machine.run 12 (startConfig 0 probeX probeT)).state.val = 7 ∧
    List.ofFn (machine.run 12 (startConfig 0 probeX probeT)).tape =
      [none, some true, some true, some true, none] := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- **The composed reject is entered through the right block, reduced.**  Out of
`startConfig 0 probeX probeW` the content is two cells long, so the inherited tag gate cannot match its
eight-bit tag: at step `78` the control is a working right-block state `44` in neither composed verdict,
at `79` it is the composed reject `183`, and it is still there at `85`.  The left block's six reject
rows are *not* what was taken: `check_h5_literal_probe` shows this fixture in the left block at the
sampled steps `0`, `3`, `6` and `11` and at `tailStart` at `12`, and `handoff_exact` proves that
confinement at every earlier time, so this reject is entered through the inherited block.  The empty fixture rejects the same way, at `17`.  The conjuncts
below use no slice theorem. -/
theorem check_composed_reject_probe :
    snap 78 = (44, 2, [some true, some false, none, none, none]) ∧
    (machine.run 78 (startConfig 0 probeX probeW)).state ≠ machine.accept ∧
    (machine.run 78 (startConfig 0 probeX probeW)).state ≠ machine.reject ∧
    snap 79 = (183, 2, [some true, some false, none, none, none]) ∧
    snap 85 = (183, 2, [some true, some false, none, none, none]) ∧
    snapE 17 = (183, 0, [none, none, none]) := by
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedPairOriginShiftAlignmentCountdownSurfaceTests
