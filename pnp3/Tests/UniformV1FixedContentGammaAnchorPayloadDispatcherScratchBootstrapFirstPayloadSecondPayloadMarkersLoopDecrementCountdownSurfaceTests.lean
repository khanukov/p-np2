import
  Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3h concrete slice: G2a's fixed 6-state, 18-row gamma anchor followed
by the whole landed G3g composite, as **one** closed 129-state, 387-row table.  Its newly executed
handoff H10 has exactly **one** live routed row — `qReturn` (`3`) on `some true`, the anchor's only
row targeting its accept — into G3g's start `tailStart` at index `6`; six further anchor rows route
to the composed reject `128`, and the two dead left verdict copies are no composed row's target.
H11 (six rows inside `[6, 34)`, all into `34`) and H12 (`40 → 43`) to H17 (`115 → 118`) are
inherited from G3g.  Every public declaration is restated in full.

The probes.  The eight words are G3f's and G3g's (tag `10110010`): `malformedWord` has no gamma
terminator; `zeroWord` decodes to `zeros = 0`, `oneWord` to `zeros = 1`, `middleWord`, `tightWord`,
`pendTrueWord` and `pendVirtWord` to `zeros = 2`, and `physWord` to `zeros = 4`.  The seven
well-formed words switch at the anchor's width-only first arrival `2 * zeros + 5` — `5`, `7`, `9`,
`9`, `9`, `9`, `13` — on the gamma terminator cell `8 + zeros`, whose value is pinned for four of
them, and the inherited H11 then fires at `2 * zeros + 5 + C`: `7`, `23`, `21`, `21`, `32`, `32`,
`31`.  The `check_*_literal*` theorems are
**derived** from the slice's theorems, whose hypotheses they discharge inline at the literals; the
drain runs at `B = 22` after `1129` steps — `13` for the anchor, `18` for the dispatcher, `1098` for
G3e — with the register value `24 > N` supplied **by hand** (an execution fixture, no
accepted-content fixture).  The `check_*_probe` theorems reduce the composed machine by kernel computation
out of the actual `startConfig`, with no slice theorem used: the anchor's leftward walk, its
marker erase writing `none` into cell `7` at step `zeros + 4`, both switches, the inherited H12 at
steps `49`/`50` on the width-`4` fixture, and the composed reject.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the nine earlier handoffs is executed or pinned; no first arrival of the composed
accept, fence, converse, footprint theorem or pnp4 bridge; and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedContentGammaAnchor (qStart qLeft qErase qReturn qAccept qReject
  successTime markedTape)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (dispatcherChainClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inAnchor :
    Fin FixedContentGammaAnchor.stateCount → Fin machine.stateCount := inAnchor
def check_inTail :
    Fin
      FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inTail
def check_route : Fin FixedContentGammaAnchor.stateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_anchorChainClock (C N zeros d v : Nat) : Nat := anchorChainClock C N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
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
        (machine.step (inAnchor q) s).1 ≠ inAnchor qReject) :=
  table_and_resource_pins

/-- The unique live accept row, restated in full. -/
theorem check_accept_row_unique (q : Fin FixedContentGammaAnchor.stateCount) (s : Option Bool)
    (hq : q ≠ qAccept)
    (h : (FixedContentGammaAnchor.machine.rawStep q s).1 = FixedContentGammaAnchor.machine.accept) :
    q = qReturn ∧ s = some true :=
  accept_row_unique q s hq h

/-- The start, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedContentGammaAnchor.startConfig B x w
    let c := startConfig B x w
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C N zeros d v : Nat) :
    anchorChainClock C N zeros d v = successTime zeros + dispatcherChainClock C N zeros d v ∧
      anchorChainClock C N zeros d v = 2 * zeros + 5 + (C + bootChainClock N zeros d v) ∧
      (2 ≤ zeros → anchorChainClock C N zeros d v =
        2 * zeros + 5 + (C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))))) :=
  clock_pins C N zeros d v

/-- The semantic dependency the switch has to respect, restated in full. -/
theorem check_dispatcher_start_at_first_arrival {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    FixedGammaPayloadDispatcher.startConfig B x w =
      FixedGammaPayloadDispatcher.retagG2a
        (FixedContentGammaAnchor.machine.run (successTime zeros)
          (FixedContentGammaAnchor.startConfig B x w)) :=
  dispatcher_start_at_first_arrival x w htag hg

/-- The executed handoff H10 at the anchor's first arrival, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
              B x w))) :=
  handoff_exact x w htag hg

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let e := machine.run (successTime zeros) (startConfig B x w)
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    e.state = tailStart ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = 8 + zeros ∧ e.tape = markedTape B x w ∧
      (∀ i, i.val = 7 → e.tape i = none) ∧
      (∀ i, i.val ≠ 7 → e.tape i = FixedPairContentMarkerErase.contentTape B x w i) :=
  handoff_endpoint_pins x w htag hg

/-- The inherited H11 inside this machine, restated in full. -/
theorem check_tagged_inherited_switch {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ FixedGammaPayloadDispatcherDeadline.deadline (a + m) ∧
      StrictFirstTerminalAt B x w C q ∧
      (q = FixedGammaPayloadDispatcher.qAllZero ∨ q = FixedGammaPayloadDispatcher.qHasOne) ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).state.val = 34 ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).head =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head ∧
      (machine.run (successTime zeros + C) (startConfig B x w)).tape =
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape :=
  tagged_inherited_switch x w htag hg

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) :=
  anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w hg s hs

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    successTime 0 = 5 ∧ successTime 1 = 7 ∧ successTime 2 = 9 ∧ successTime 4 = 13 ∧
      bootChainClock 17 4 0 24 = 1098 ∧ dispatcherChainClock 18 17 4 0 24 = 1116 ∧
      anchorChainClock 18 17 4 0 24 = 1129 :=
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

/-- H10 at the widest and the narrowest fixture, **derived**.  On `physWord`: no composed verdict at
any time up to and including the switch `13`, at which the run **is** G3g's actual
`startConfig 0 tag physWord` re-embedded, on the gamma terminator cell `12`, with the anchor's
marked tape and cell `7` erased.  On `zeroWord`: that same re-embedding at the switch `5`, on
cell `8`. -/
theorem check_handoff_literal :
    (∀ t, t ≤ 13 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 13 (startConfig 0 tag physWord) =
      FixedContentGammaAnchor.machine.seqEmbedRight
        FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag physWord) ∧
    (machine.run 13 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 13 (startConfig 0 tag physWord)).tape = markedTape 0 tag physWord ∧
    (∀ i, i.val = 7 → (machine.run 13 (startConfig 0 tag physWord)).tape i = none) ∧
    machine.run 5 (startConfig 0 tag zeroWord) =
      FixedContentGammaAnchor.machine.seqEmbedRight
        FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag zeroWord) ∧
    (machine.run 5 (startConfig 0 tag zeroWord)).head.val = 8 := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide) (by decide)
  obtain ⟨-, -, -, h3, h4, h5, -⟩ :=
    handoff_endpoint_pins (B := 0) (zeros := 4) tag physWord (by decide) (by decide)
  obtain ⟨-, -, h6, -⟩ := handoff_exact (B := 0) (zeros := 0) tag zeroWord (by decide) (by decide)
  obtain ⟨-, -, -, h7, -⟩ :=
    handoff_endpoint_pins (B := 0) (zeros := 0) tag zeroWord (by decide) (by decide)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept on the separator
blank `23` after exactly `1129` steps — `13` for the anchor, none for H10, `18` for the dispatcher,
none for H11, then G3e's `1098` — persisting.  Nothing decodes the hand-written `24`. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (anchorChainClock 18 (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, anchorChainClock 18 (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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

/-- The routed reject at the malformed fixture, derived: the composed reject at step `1`, there on
the boundary head `11` over the unchanged content tape, and again at step `5`.  No tag hypothesis is
discharged. -/
theorem check_malformed_literal :
    (machine.run 1 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 5 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ := malformed_reject_handoff (B := 0) tag malformedWord (by decide) 1 le_rfl
  obtain ⟨h4, -, -⟩ := malformed_reject_handoff (B := 0) tag malformedWord (by decide) 5 (by omega)
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

set_option maxRecDepth 100000 in
/-- **The anchor phase, reduced.**  Out of the actual `startConfig 0 tag physWord`: `qStart` (`0`)
on the terminator cell `12`, the leftward `qLeft` (`1`) walk to the tag cell `6`, `qErase` (`2`) on
cell `7` — still `some false` — and `qReturn` (`3`) on cell `8` one step later with cell `7` now
`none`: the recoverable marker, written by the composed table's own row.  No slice theorem is
used. -/
theorem check_anchor_walk_probe :
    (machine.run 0 (startConfig 0 tag physWord)).state.val = 0 ∧
    (machine.run 0 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 1 (startConfig 0 tag physWord)).state.val = 1 ∧
    (machine.run 6 (startConfig 0 tag physWord)).state.val = 1 ∧
    (machine.run 6 (startConfig 0 tag physWord)).head.val = 6 ∧
    (machine.run 7 (startConfig 0 tag physWord)).state.val = 2 ∧
    (machine.run 7 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 7 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 8 (startConfig 0 tag physWord)).state.val = 3 ∧
    (machine.run 8 (startConfig 0 tag physWord)).head.val = 8 ∧
    (machine.run 8 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = none := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 400000 in
/-- **H10 through its one routed row, reduced.**  One step before each switch the control is
`qReturn` (`3`), and at the switch it is G3g's start `6`, the row `qReturn`-on-`some true` having
fired — steps `12`/`13` on `physWord`, `8`/`9` on `middleWord`, `tightWord`, `pendTrueWord` and
`pendVirtWord`, `6`/`7` on `oneWord`, `4`/`5` on `zeroWord`.  At the switch the head is pinned on the
terminator cell `8 + zeros` for four of them: `12`, `10`, `9` and `8` on `physWord`, `middleWord`,
`oneWord` and `zeroWord`. -/
theorem check_h10_probe_reductions :
    (machine.run 12 (startConfig 0 tag physWord)).state.val = 3 ∧
    (machine.run 13 (startConfig 0 tag physWord)).state.val = 6 ∧
    (machine.run 13 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 8 (startConfig 0 tag middleWord)).state.val = 3 ∧
    (machine.run 9 (startConfig 0 tag middleWord)).state.val = 6 ∧
    (machine.run 9 (startConfig 0 tag middleWord)).head.val = 10 ∧
    (machine.run 8 (startConfig 0 tag tightWord)).state.val = 3 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).state.val = 6 ∧
    (machine.run 8 (startConfig 0 tag pendTrueWord)).state.val = 3 ∧
    (machine.run 9 (startConfig 0 tag pendTrueWord)).state.val = 6 ∧
    (machine.run 8 (startConfig 0 tag pendVirtWord)).state.val = 3 ∧
    (machine.run 9 (startConfig 0 tag pendVirtWord)).state.val = 6 ∧
    (machine.run 6 (startConfig 0 tag oneWord)).state.val = 3 ∧
    (machine.run 7 (startConfig 0 tag oneWord)).state.val = 6 ∧
    (machine.run 7 (startConfig 0 tag oneWord)).head.val = 9 ∧
    (machine.run 4 (startConfig 0 tag zeroWord)).state.val = 3 ∧
    (machine.run 5 (startConfig 0 tag zeroWord)).state.val = 6 ∧
    (machine.run 5 (startConfig 0 tag zeroWord)).head.val = 8 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The inherited H11, reduced.**  The dispatcher block runs out of the switch and hands over to
G2p-a at index `34`, at `2 * zeros + 5 + C`: `31` on `physWord` (one step earlier the dispatcher's
`qCursorFillOne` at `14`), `23` on `oneWord`, `21` on `middleWord` and `tightWord`, `32` on
`pendTrueWord` and `pendVirtWord`, `7` on `zeroWord`, where the head is pinned at G2p-a's `7`
rather than the `6` pinned on `physWord`.  Only those two heads are pinned here; the other five
words' heads are left to `check_tagged_inherited_switch`. -/
theorem check_inherited_handoff_probe :
    (machine.run 30 (startConfig 0 tag physWord)).state.val = 14 ∧
    (machine.run 31 (startConfig 0 tag physWord)).state.val = 34 ∧
    (machine.run 31 (startConfig 0 tag physWord)).head.val = 6 ∧
    (machine.run 23 (startConfig 0 tag oneWord)).state.val = 34 ∧
    (machine.run 21 (startConfig 0 tag middleWord)).state.val = 34 ∧
    (machine.run 21 (startConfig 0 tag tightWord)).state.val = 34 ∧
    (machine.run 32 (startConfig 0 tag pendTrueWord)).state.val = 34 ∧
    (machine.run 32 (startConfig 0 tag pendVirtWord)).state.val = 34 ∧
    (machine.run 7 (startConfig 0 tag zeroWord)).state.val = 34 ∧
    (machine.run 7 (startConfig 0 tag zeroWord)).head.val = 7 := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The inherited H12, reduced.**  Out of `startConfig 0 tag physWord` the G2p-a block runs on and
hands over to G2p-b at steps `49`/`50`: index `40`, then `43` on the restored terminator cell `12`
with G2p-a's scratch `true` at cell `18`.  These are G3g's own steps `36`/`37` shifted by the `13`
steps the anchor takes and its indices by the six anchor states, so the inherited `40 → 43` fires
inside this machine and is not merely offset arithmetic. -/
theorem check_inherited_h12_probe :
    (machine.run 49 (startConfig 0 tag physWord)).state.val = 40 ∧
    (machine.run 50 (startConfig 0 tag physWord)).state.val = 43 ∧
    (machine.run 50 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 50 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 50 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformedWord`: the start is in
neither composed verdict, on the boundary head `11`; one step later the composed reject — index
`128`, not G2a's own `qReject` at `5` — on that head; and it is still there at step `5`. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformedWord)).state ≠ machine.reject ∧
    (machine.run 0 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).state.val = 128 ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformedWord)).state.val = 128 := by
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
