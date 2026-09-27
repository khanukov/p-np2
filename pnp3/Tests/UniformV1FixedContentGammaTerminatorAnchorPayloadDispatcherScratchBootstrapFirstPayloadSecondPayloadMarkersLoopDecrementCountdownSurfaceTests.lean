import
  Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3i concrete slice: G2's fixed 3-state, 9-row gamma-terminator scan
followed by the whole landed G3h composite, as **one** closed 132-state, 396-row table.  Its newly
executed handoff H9 has exactly **one** live routed row — `qScan` (`0`) on `some true`, the
terminator's only row targeting its accept outside the accept's own three — into G3h's start
`tailStart` at index `3`; exactly one further terminator row outside the reject's own three, `qScan`
on the blank, routes to the composed reject `131`; and the two dead left verdict copies are no
composed row's target.  H10 (`6 → 9`) and H11 (six rows inside `[9, 37)`, all into `37`) to H17
(`118 → 121`) are inherited from G3h.  Every public declaration is restated in full.

The probes.  The eight words are G3f's, G3g's and G3h's (tag `10110010`): `malformedWord` has no
gamma terminator; `zeroWord` decodes to `zeros = 0`, `oneWord` to `zeros = 1`, `middleWord`,
`tightWord`, `pendTrueWord` and `pendVirtWord` to `zeros = 2`, and `physWord` to `zeros = 4`.  The
seven well-formed words switch at the terminator's width-only first arrival `zeros + 1` — `1`, `2`,
`3`, `3`, `3`, `3`, `5` — on the gamma terminator cell `8 + zeros`, whose value is pinned for each of
them; the inherited H10 then fires at `zeros + 1 + (2 * zeros + 5)` — `6`, `9`, `12`, `12`, `12`,
`12`, `18` — and the inherited H11 at `zeros + 1 + (2 * zeros + 5) + C`: `8`, `25`, `24`, `24`, `35`,
`35`, `36`.  The `check_*_literal*` theorems are **derived** from the slice's theorems, whose
hypotheses they discharge inline at the literals; the drain runs at `B = 22` after `1134` steps — `5`
for the terminator, `13` for the anchor, `18` for the dispatcher, `1098` for G3e — with the register
value `24 > N` supplied **by hand** (an execution fixture, no accepted-content fixture).  The
`check_*_probe` theorems reduce the composed machine by kernel computation out of the actual
`startConfig`, with no slice theorem used: the terminator's rightward scan over the zero run, all
seven H9 switches, with the unerased cell `7` pinned at the widest of them, the inherited H10 and
H11, the inherited H12 at steps `54`/`55` on the width-`4` fixture, and the composed reject at the
terminator's deadline `4` on the malformed fixture.

Not here: the composed `startConfig` still embeds every earlier phase as a retag of the actual
tag-gate `finalConfig`, so no raw-input run and none of the eight earlier handoffs is executed or
pinned; no first arrival of the composed accept, fence, converse, footprint theorem or pnp4 bridge;
and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedContentGammaTerminator (qScan gammaZeros? terminalIndex)
open Complexity.Uniform.V1.FixedContentGammaAnchor (successTime markedTape)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (anchorChainClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inTerminator :
    Fin FixedContentGammaTerminator.stateCount → Fin machine.stateCount := inTerminator
def check_inTail :
    Fin
      FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inTail
def check_route : Fin FixedContentGammaTerminator.stateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_switchTime (zeros : Nat) : Nat := switchTime zeros
def check_terminatorChainClock (C N zeros d v : Nat) : Nat := terminatorChainClock C N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
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
        (machine.step (inTerminator q) s).1 ≠ inTerminator FixedContentGammaTerminator.qReject) :=
  table_and_resource_pins

/-- The two unique live verdict rows, restated in full. -/
theorem check_verdict_rows_unique (q : Fin FixedContentGammaTerminator.stateCount)
    (s : Option Bool) :
    (q ≠ FixedContentGammaTerminator.qAccept →
      (FixedContentGammaTerminator.machine.rawStep q s).1 =
        FixedContentGammaTerminator.machine.accept → q = qScan ∧ s = some true) ∧
    (q ≠ FixedContentGammaTerminator.qReject →
      (FixedContentGammaTerminator.machine.rawStep q s).1 =
        FixedContentGammaTerminator.machine.reject → q = qScan ∧ s = none) :=
  verdict_rows_unique q s

/-- The start as the retagged actual tag-gate endpoint, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
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
      c.tape = FixedPairContentMarkerErase.contentTape B x w :=
  handoff_pins x w htag

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C N zeros d v : Nat) :
    terminatorChainClock C N zeros d v = switchTime zeros + anchorChainClock C N zeros d v ∧
      terminatorChainClock C N zeros d v =
        zeros + 1 + (2 * zeros + 5 + (C + bootChainClock N zeros d v)) ∧
      (2 ≤ zeros → terminatorChainClock C N zeros d v =
        zeros + 1 + (2 * zeros + 5 + (C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))))))) :=
  clock_pins C N zeros d v

/-- The terminator's strict first successful arrival, restated in full. -/
theorem check_terminator_first_arrival {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
      switchTime zeros ≤ FixedContentGammaTerminator.deadline a m :=
  terminator_first_arrival x w htag hg

/-- The terminator's strict first rejecting arrival, restated in full. -/
theorem check_terminator_reject_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
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
          FixedContentGammaTerminator.machine.reject :=
  terminator_reject_arrival x w htag hg

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_anchor_start_at_first_arrival {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    FixedContentGammaAnchor.startConfig B x w =
      FixedContentGammaAnchor.retag
        (FixedContentGammaTerminator.machine.run (switchTime zeros)
          (FixedContentGammaTerminator.startConfig B x w)) :=
  anchor_start_at_first_arrival x w htag hg

/-- The executed handoff H9 at the terminator's first arrival, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
              B x w))) :=
  handoff_exact x w htag hg

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime zeros) (startConfig B x w)
    let p := FixedContentGammaAnchor.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i, i.val = 7 → e.tape i ≠ none) :=
  handoff_endpoint_pins x w htag hg

/-- The inherited H10 inside this machine, restated in full. -/
theorem check_tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (switchTime zeros + successTime zeros) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state.val = 9 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) :=
  tagged_inherited_switch x w htag hg

/-- The inherited H11 inside this machine, restated in full. -/
theorem check_tagged_inherited_dispatcher_switch {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
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
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape :=
  tagged_inherited_dispatcher_switch x w htag hg

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) :=
  terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < FixedContentGammaTerminator.deadline a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, FixedContentGammaTerminator.deadline a m ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) :=
  malformed_reject_handoff x w htag hg

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    switchTime 0 = 1 ∧ switchTime 1 = 2 ∧ switchTime 2 = 3 ∧ switchTime 4 = 5 ∧
      FixedContentGammaTerminator.deadline 8 3 = 4 ∧
      anchorChainClock 18 17 4 0 24 = 1129 ∧ terminatorChainClock 18 17 4 0 24 = 1134 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The eight probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
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

/-- H9 at the widest and the narrowest fixture, **derived**.  On `physWord`: no composed verdict at
any time up to and including the switch `5`, at which the run **is** G3h's actual
`startConfig 0 tag physWord` re-embedded, on the gamma terminator cell `12`, with the unmarked
content tape whose cell `7` is not yet blank.  On `zeroWord`: that same re-embedding at the switch
`1`, on cell `8`. -/
theorem check_handoff_literal :
    (∀ t, t ≤ 5 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 5 (startConfig 0 tag physWord) =
      FixedContentGammaTerminator.machine.seqEmbedRight
        FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag physWord) ∧
    (machine.run 5 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 5 (startConfig 0 tag physWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag physWord ∧
    (∀ i, i.val = 7 → (machine.run 5 (startConfig 0 tag physWord)).tape i ≠ none) ∧
    machine.run 1 (startConfig 0 tag zeroWord) =
      FixedContentGammaTerminator.machine.seqEmbedRight
        FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag zeroWord) ∧
    (machine.run 1 (startConfig 0 tag zeroWord)).head.val = 8 := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide) (by decide)
  obtain ⟨-, -, -, h3, h4, h5⟩ :=
    handoff_endpoint_pins (B := 0) (zeros := 4) tag physWord (by decide) (by decide)
  obtain ⟨-, -, h6, -⟩ := handoff_exact (B := 0) (zeros := 0) tag zeroWord (by decide) (by decide)
  obtain ⟨-, -, -, h7, -⟩ :=
    handoff_endpoint_pins (B := 0) (zeros := 0) tag zeroWord (by decide) (by decide)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept on the separator
blank `23` after exactly `1134` steps — `5` for the terminator, none for H9, `13` for the anchor,
none for H10, `18` for the dispatcher, none for H11, then G3e's `1098` — persisting.  Nothing
decodes the hand-written `24`. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (terminatorChainClock 18 (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, terminatorChainClock 18 (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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

/-- The routed reject at the malformed fixture, derived: no composed verdict before the terminator's
length-only deadline `4`, and the composed reject from it on — at `4` and again at `8` — there on the
boundary head `11` over the unchanged content tape.  The tag hypothesis **is** discharged here,
unlike in G3h's routed reject. -/
theorem check_malformed_literal :
    (∀ t, t < 4 → (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag malformedWord)).state ≠ machine.reject) ∧
    (machine.run 4 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 4 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 4 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 8 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨hpre, hpost⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide)
  obtain ⟨h1, h2, h3⟩ := hpost 4 (by decide)
  obtain ⟨h4, -, -⟩ := hpost 8 (by decide)
  exact ⟨hpre, h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 100000 in
/-- **The terminator phase, reduced.**  Out of the actual `startConfig 0 tag physWord`: `qScan` (`0`)
on the first gamma cell `8`, one step right per zero of the run to cell `12`, and the switch one step
later.  Cell `7` still carries the tag's own `some false` at that switch and is blank by step `13` —
the anchor's recoverable marker is written later, inside the right block.  No slice theorem is
used. -/
theorem check_terminator_scan_probe :
    (machine.run 0 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 0 (startConfig 0 tag physWord)).head.val = 8 ∧
    (machine.run 1 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 1 (startConfig 0 tag physWord)).head.val = 9 ∧
    (machine.run 4 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 4 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 4 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 5 (startConfig 0 tag physWord)).state.val = 3 ∧
    (machine.run 5 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 5 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 13 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = none := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 400000 in
/-- **H9 through its one routed row, reduced.**  One step before each switch the control is `qScan`
(`0`), and at the switch it is G3h's start `3`, the row `qScan`-on-`some true` having fired — steps
`4`/`5` on `physWord`, `2`/`3` on `middleWord`, `tightWord`, `pendTrueWord` and `pendVirtWord`,
`1`/`2` on `oneWord`, `0`/`1` on `zeroWord`.  At every switch the head is pinned on the terminator
cell `8 + zeros`: `12`, `10`, `10`, `10`, `10`, `9` and `8`. -/
theorem check_h9_probe_reductions :
    (machine.run 4 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 5 (startConfig 0 tag physWord)).state.val = 3 ∧
    (machine.run 5 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 2 (startConfig 0 tag middleWord)).state.val = 0 ∧
    (machine.run 3 (startConfig 0 tag middleWord)).state.val = 3 ∧
    (machine.run 3 (startConfig 0 tag middleWord)).head.val = 10 ∧
    (machine.run 2 (startConfig 0 tag tightWord)).state.val = 0 ∧
    (machine.run 3 (startConfig 0 tag tightWord)).state.val = 3 ∧
    (machine.run 3 (startConfig 0 tag tightWord)).head.val = 10 ∧
    (machine.run 2 (startConfig 0 tag pendTrueWord)).state.val = 0 ∧
    (machine.run 3 (startConfig 0 tag pendTrueWord)).state.val = 3 ∧
    (machine.run 3 (startConfig 0 tag pendTrueWord)).head.val = 10 ∧
    (machine.run 2 (startConfig 0 tag pendVirtWord)).state.val = 0 ∧
    (machine.run 3 (startConfig 0 tag pendVirtWord)).state.val = 3 ∧
    (machine.run 3 (startConfig 0 tag pendVirtWord)).head.val = 10 ∧
    (machine.run 1 (startConfig 0 tag oneWord)).state.val = 0 ∧
    (machine.run 2 (startConfig 0 tag oneWord)).state.val = 3 ∧
    (machine.run 2 (startConfig 0 tag oneWord)).head.val = 9 ∧
    (machine.run 0 (startConfig 0 tag zeroWord)).state.val = 0 ∧
    (machine.run 1 (startConfig 0 tag zeroWord)).state.val = 3 ∧
    (machine.run 1 (startConfig 0 tag zeroWord)).head.val = 8 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The inherited H10 and H11, reduced.**  The anchor block runs out of the H9 switch and hands
over to G2k at `zeros + 1 + (2 * zeros + 5)` — index `9`, G3h's `6` shifted by the three terminator
states: steps `18` on `physWord`, `12` on `middleWord`, `tightWord`, `pendTrueWord` and
`pendVirtWord`, `9` on `oneWord`, `6` on `zeroWord`, with the anchor's `qReturn` at `6` pinned one
step before the first two of those.  The dispatcher block then hands over to G2p-a at index `37`:
`36` on `physWord` — its own `17` pinned one step before — `25` on `oneWord`, `24` on `middleWord`
and `tightWord`, `35` on `pendTrueWord` and `pendVirtWord`, `8` on `zeroWord`, where the head is
pinned at G2p-a's `7` rather than the `6` pinned on `physWord`. -/
theorem check_inherited_handoff_probe :
    (machine.run 17 (startConfig 0 tag physWord)).state.val = 6 ∧
    (machine.run 18 (startConfig 0 tag physWord)).state.val = 9 ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 11 (startConfig 0 tag middleWord)).state.val = 6 ∧
    (machine.run 12 (startConfig 0 tag middleWord)).state.val = 9 ∧
    (machine.run 12 (startConfig 0 tag tightWord)).state.val = 9 ∧
    (machine.run 12 (startConfig 0 tag pendTrueWord)).state.val = 9 ∧
    (machine.run 12 (startConfig 0 tag pendVirtWord)).state.val = 9 ∧
    (machine.run 9 (startConfig 0 tag oneWord)).state.val = 9 ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).state.val = 9 ∧
    (machine.run 35 (startConfig 0 tag physWord)).state.val = 17 ∧
    (machine.run 36 (startConfig 0 tag physWord)).state.val = 37 ∧
    (machine.run 36 (startConfig 0 tag physWord)).head.val = 6 ∧
    (machine.run 25 (startConfig 0 tag oneWord)).state.val = 37 ∧
    (machine.run 24 (startConfig 0 tag middleWord)).state.val = 37 ∧
    (machine.run 24 (startConfig 0 tag tightWord)).state.val = 37 ∧
    (machine.run 35 (startConfig 0 tag pendTrueWord)).state.val = 37 ∧
    (machine.run 35 (startConfig 0 tag pendVirtWord)).state.val = 37 ∧
    (machine.run 8 (startConfig 0 tag zeroWord)).state.val = 37 ∧
    (machine.run 8 (startConfig 0 tag zeroWord)).head.val = 7 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The inherited H12, reduced.**  Out of `startConfig 0 tag physWord` the G2p-a block runs on and
hands over to G2p-b at steps `54`/`55`: index `43`, then `46` on the restored terminator cell `12`
with G2p-a's scratch `true` at cell `18`.  These are G3h's own steps `49`/`50` shifted by the `5`
steps the terminator takes and its indices by the three terminator states, so the inherited
`43 → 46` fires inside this machine and is not merely offset arithmetic. -/
theorem check_inherited_h12_probe :
    (machine.run 54 (startConfig 0 tag physWord)).state.val = 43 ∧
    (machine.run 55 (startConfig 0 tag physWord)).state.val = 46 ∧
    (machine.run 55 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 55 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 55 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformedWord`: at step `3` the
terminator has scanned the whole physical suffix, is in neither composed verdict, and sits on the
boundary head `11`; at step `4`, its length-only deadline, the composed reject — index `131`, not
G2's own `qReject` at `2` — on that head; and it is still there at step `8`. -/
theorem check_malformed_probe :
    (machine.run 3 (startConfig 0 tag malformedWord)).state.val = 0 ∧
    (machine.run 3 (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
    (machine.run 3 (startConfig 0 tag malformedWord)).state ≠ machine.reject ∧
    (machine.run 3 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 4 (startConfig 0 tag malformedWord)).state.val = 131 ∧
    (machine.run 4 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 8 (startConfig 0 tag malformedWord)).state.val = 131 := by
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
