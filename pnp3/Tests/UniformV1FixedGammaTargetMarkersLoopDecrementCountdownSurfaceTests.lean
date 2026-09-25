import Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown

/-!
Surface pins for the Part A G2z concrete slice: G2p-d's marker preamble and G2y's
loop-decrement-countdown composite as **one** closed 54-state, 162-row table.  Its newly executed
handoff H15 is a preamble row into `qDone` routed to G2y's start (composed index `14`); H16
(`33 → 36`) and H17 (`40 → 43`) are inherited from G2y.  Every public declaration is restated in
full; `check_clock_values` reduces the literal clocks the probes use: `exactClock 4 = 11`,
`exactClock 2 = 9`, `totalClock 17 4 = 64`, `chainClock 17 4 0 24 = 1009` and
`markersChainClock 17 4 0 24 = 1020`.

The probes.  The tag is `10110010`.  `physWord` decodes to `zeros = 4` with `N = 17` and both
payload sources physical; `middleWord` to `zeros = 2` with `N = 12` and one source physical;
`tightWord` to `zeros = 2` with `N = 11` and neither physical.  The three shapes take H15 through
the two of its four routed rows that `qSrcB` can select here: `qClearB` (index `9`, write blank and
move right) on `physWord`, `qBackB` (index `10`, preserve `true` and stay) on the other two.  Each
probe is a claim about its own word; nothing here says which row an arbitrary word of that width
takes.  `middleWord` is the middle source shape
that the old foundation literal probes never covered.  `check_markers_handoff_instance` inhabits
`handoff_exact`'s four hypotheses at all three shapes at the *probe's* budget `B = 0`, and
`check_markers_drained_instance` the drain's seven at `B = 22`, where `4 + 2 + 24 = 8 + 22` meets
the lane budget exactly — so budget `0` is never presented as validating the 1020-step drain, and
the short probes never establish the long run's room premise.  The register value `24` is supplied
**by hand**; `24 > N = 17`, so this is a pnp3 execution fixture and neither an accepted-content
fixture nor evidence for the pnp4 cap.

`check_handoff_literal` and `check_markers_literal_endpoint` are **derived** from `handoff_exact`
and `markers_loop_decrement_countdown_drained` at those literals.  The reduction probes are
**independent**: `phys_start`, `middle_start`, `tight_start` and `malformed_start` identify the
composed `startConfig B tag ·` with an explicit configuration using only G2p-c's landed
second-payload endpoint theorems, which execute nothing, and kernel computation then reads the
composed machine back off that configuration.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the fourteen earlier handoffs is executed or pinned; no first arrival of the
composed accept — the first arrival proved is the marker preamble's, inside the left block; no
fence, so an oversized register still times out; the rejecting run is exercised but is no converse
and characterises no parsed target; no footprint theorem, so every room premise is sufficient and
used, never shown necessary; and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or
language-membership statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation (exactClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown (chainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inMarkers :
    Fin FixedGammaTargetPayloadLoopFoundation.stateCount → Fin machine.stateCount := inMarkers
def check_inTail :
    Fin FixedGammaTargetLoopDecrementCountdown.machine.stateCount → Fin machine.stateCount := inTail
def check_route :
    Fin FixedGammaTargetPayloadLoopFoundation.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_markersChainClock (N zeros d v : Nat) : Nat := markersChainClock N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 54 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 162 ∧
      machine.start = route FixedGammaTargetPayloadLoopFoundation.qStart ∧
      machine.start = inMarkers FixedGammaTargetPayloadLoopFoundation.qStart ∧
      machine.accept = inTail FixedGammaTargetLoopDecrementCountdown.machine.accept ∧
      machine.reject = inTail FixedGammaTargetLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 52 ∧ machine.reject.val = 53 ∧
      (∀ q, (inMarkers q).val = q.val) ∧ (∀ q, (inMarkers q).val < 14) ∧
      (∀ q, (inTail q).val = 14 + q.val) ∧ (∀ q, 14 ≤ (inTail q).val) ∧
      (∀ q, (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop q)).val = 14 + q.val) ∧
      (∀ q, (inTail (FixedGammaTargetLoopDecrementCountdown.inTail q)).val = 36 + q.val) ∧
      Function.Injective inMarkers ∧ Function.Injective inTail ∧
      (∀ p q, inMarkers p ≠ inTail q) ∧
      route FixedGammaTargetPayloadLoopFoundation.qDone =
        inTail FixedGammaTargetLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetPayloadLoopFoundation.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetPayloadLoopFoundation.qDone →
        q ≠ FixedGammaTargetPayloadLoopFoundation.qReject → route q = inMarkers q) ∧
      (∀ q s, machine.step (inMarkers q) s =
        (route (FixedGammaTargetPayloadLoopFoundation.machine.step q s).1,
          (FixedGammaTargetPayloadLoopFoundation.machine.step q s).2.1,
          (FixedGammaTargetPayloadLoopFoundation.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (FixedGammaTargetLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qZeroA).val = 1 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qClearB).val = 9 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qBackB).val = 10 ∧
      (inMarkers FixedGammaTargetPayloadLoopFoundation.qFin).val = 11 ∧
      (inTail FixedGammaTargetLoopDecrementCountdown.machine.start).val = 14 ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qZeroA) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some true, .left) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qClearB) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, none, .right) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qBackB) (some true) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some true, .stay) ∧
      machine.step (inMarkers FixedGammaTargetPayloadLoopFoundation.qFin) (some false) =
        (inTail FixedGammaTargetLoopDecrementCountdown.machine.start, some false, .stay) ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop
        FixedGammaTargetPayloadRound.qFin)).val = 33 ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        FixedGammaTargetDecrementCountdown.machine.start)).val = 36 ∧
      machine.step (inTail (FixedGammaTargetLoopDecrementCountdown.inLoop
          FixedGammaTargetPayloadRound.qFin)) (some false) =
        (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          FixedGammaTargetDecrementCountdown.machine.start), some false, .stay) ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        (FixedGammaTargetDecrementCountdown.inDecrement
          FixedGammaTargetRegisterDecrement.qBorrow))).val = 40 ∧
      (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
        (FixedGammaTargetDecrementCountdown.inCountdown
          FixedGammaTargetUnaryCountdown.qStart))).val = 43 ∧
      machine.step (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inDecrement
            FixedGammaTargetRegisterDecrement.qBorrow))) (some true) =
        (inTail (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inCountdown
            FixedGammaTargetUnaryCountdown.qStart)), some false, .stay) :=
  table_and_resource_pins

/-- The start, restated in full: the marker preamble's `startConfig` routed into the composed
control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadLoopFoundation.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
        FixedGammaTargetLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (N zeros d v : Nat) :
    markersChainClock N zeros d v =
        exactClock zeros + FixedGammaTargetLoopDecrementCountdown.chainClock N zeros d v ∧
      markersChainClock N zeros d v =
        zeros + 7 + (totalClock N zeros + composedClock N zeros d v) :=
  clock_pins N zeros d v

/-- The executed handoff H15, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let T := exactClock zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRouted
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetPayloadLoopFoundation.machine.run t
            (FixedGammaTargetPayloadLoopFoundation.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
          FixedGammaTargetLoopDecrementCountdown.machine
          (FixedGammaTargetLoopDecrementCountdown.machine.run s
            (FixedGammaTargetLoopDecrementCountdown.startConfig B x w))) :=
  handoff_exact x w htag hg hzeros hroom

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_markers_loop_decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := markersChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) :=
  markers_loop_decrement_countdown_drained x w htag hg hzeros hfence hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w htag hg s hs

/-- The literal clocks the probes use, reduced by kernel computation: the preamble's first arrival
at the two probe widths, the payload loop's, G2y's sum and this slice's sum. -/
theorem check_clock_values :
    exactClock 4 = 11 ∧ exactClock 2 = 9 ∧ totalClock 17 4 = 64 ∧
      chainClock 17 4 0 24 = 1009 ∧ markersChainClock 17 4 0 24 = 1020 ∧
      markersChainClock 17 4 0 24 = exactClock 4 + chainClock 17 4 0 24 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The three source shapes -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def middleWord : Bitstring 4 := ![false, false, true, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def malformed : Bitstring 3 := ![false, false, false]

/-- `handoff_exact`'s four hypotheses are satisfiable at all three source shapes, at the *probe's*
budget `B = 0`: the tag matches, the words decode to `zeros = 4`, `2` and `2`, and the preamble's
room `20 < 27`, `15 < 22` and `14 < 21` holds. -/
theorem check_markers_handoff_instance :
    (FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 8 + 9 + 3 < tapeLength (pairLength 8 9) 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag middleWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag middleWord) = some 2 ∧
      2 ≤ 2 ∧ 8 + 4 + 3 < tapeLength (pairLength 8 4) 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag tightWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag tightWord) = some 2 ∧
      2 ≤ 2 ∧ 8 + 3 + 3 < tapeLength (pairLength 8 3) 0) :=
  ⟨⟨by decide, by decide, by omega, by decide⟩, ⟨by decide, by decide, by omega, by decide⟩,
    ⟨by decide, by decide, by omega, by decide⟩⟩

/-- `malformed_reject_handoff`'s two hypotheses are satisfiable: the tag matches and the word has no
gamma terminator below the boundary `N = 11`. -/
theorem check_malformed_instance :
    FixedContentTagGate.tagMatches (Fin.append tag malformed) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag malformed) = none :=
  ⟨by decide, by decide⟩

/-- `markers_loop_decrement_countdown_drained`'s seven hypotheses are satisfiable at the physical
fixture, at the *drain's* budget `B = 22`: `zeros = 4`, the decremented digits are the bits of `24`,
and `F = 24`, `B = 22` meet the lane budget exactly.  The `24` is supplied by hand. -/
theorem check_markers_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- H15 at the physical fixture, derived from `handoff_exact` rather than reduced: no composed
verdict before step `11`, and at step `11` G2y's actual `startConfig 0 tag physWord`,
re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 11 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 11 (startConfig 0 tag physWord) =
      FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight
        FixedGammaTargetLoopDecrementCountdown.machine
        (FixedGammaTargetLoopDecrementCountdown.startConfig 0 tag physWord) := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by decide)
  exact ⟨h1, h2⟩

/-- The composed endpoint at the physical fixture, derived rather than reduced: the composed accept
on the separator blank `23` after exactly `markersChainClock 17 4 0 24 = 1020` steps — `11` for the
marker preamble, none for H15, `64` for the payload loop, none for H16, `18` for the decrement, none
for H17, `927` for the countdown — with the register emptied and twenty-four marks laid, persisting.
Nothing decodes the hand-written `24`. -/
theorem check_markers_literal_endpoint :
    let e := machine.run (markersChainClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, markersChainClock (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    markers_loop_decrement_countdown_drained (a := 8) (m := 9) (B := 22) (zeros := 4) (v := 24)
      (F := 24) tag physWord (by decide) (by decide) (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

/-- Rebuild a configuration from its projections, over a configuration *variable*, so that
identifying the phase-local start configuration never has to reduce the G2p-c run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

/-- The composed `startConfig B tag physWord`: the composed start on head `7` over G2p-c's
second-payload tape.  Only G2p-c's landed endpoint theorem is used, and it executes nothing. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTargetPayloadLoopFoundation.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetSecondPayload.secondPayloadTape B tag physWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag physWord) (9 + 4)).getD false)
          ((FixedContentTagGate.physicalSymbol (Fin.append tag physWord) (10 + 4)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.second_payload_at_deadline
    (B := B) (zeros := 4) tag physWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem middle_start (B : Nat) :
    startConfig B tag middleWord =
      ⟨route FixedGammaTargetPayloadLoopFoundation.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetSecondPayload.secondPayloadTape B tag middleWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag middleWord) (9 + 2)).getD false)
          ((FixedContentTagGate.physicalSymbol (Fin.append tag middleWord) (10 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.second_payload_at_deadline
    (B := B) (zeros := 2) tag middleWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem tight_start (B : Nat) :
    startConfig B tag tightWord =
      ⟨route FixedGammaTargetPayloadLoopFoundation.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetSecondPayload.secondPayloadTape B tag tightWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag tightWord) (9 + 2)).getD false)
          ((FixedContentTagGate.physicalSymbol (Fin.append tag tightWord) (10 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.second_payload_at_deadline
    (B := B) (zeros := 2) tag tightWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem malformed_start (B : Nat) :
    startConfig B tag malformed =
      ⟨route FixedGammaTargetPayloadLoopFoundation.qStart,
        ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

set_option maxRecDepth 100000 in
/-- **H15 on both payload sources physical, reduced.**  Out of the actual composed
`startConfig 0 tag physWord`: at step `10` the preamble's `qClearB` (index `9`) on the *outgoing*
terminator cell `13`, still `some true`; at step `11` G2y's `qLoop` (index `14`) at head `14`, the
cell `qSrcB` has just marked as the new terminator, with cell `13` blanked by that same transition —
the `qClearB` row took the machine across the block boundary while writing `none` and moving right.
Cells `8` and `9`, the two consumed gamma zeros, are marked. -/
theorem check_h15_probe_physical :
    (machine.run 10 (startConfig 0 tag physWord)).state.val = 9 ∧
    (machine.run 10 (startConfig 0 tag physWord)).head.val = 13 ∧
    (machine.run 10 (startConfig 0 tag physWord)).tape ⟨13, by decide⟩ = some true ∧
    (machine.run 11 (startConfig 0 tag physWord)).state.val = 14 ∧
    (machine.run 11 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 11 (startConfig 0 tag physWord)).tape ⟨13, by decide⟩ = none ∧
    (machine.run 11 (startConfig 0 tag physWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 11 (startConfig 0 tag physWord)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 11 (startConfig 0 tag physWord)).tape ⟨9, by decide⟩ = some true := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H15 on the middle source shape, reduced** — the first payload source physical, the second the
boundary blank, a shape no earlier literal probe covered.  Out of `startConfig 0 tag middleWord`
(`N = 12`, `zeros = 2`): at step `8` the preamble's `qBackB` (index `10`) at head `11` on
`some true`; at step `9` G2y's `qLoop` (index `14`) at that same head `11`, the cell preserved — the
`qBackB` row crossed the boundary writing `some true` and staying — with the trail cell `10` blank,
the boundary cell `12` blank and the consumed marks at `8` and `9`. -/
theorem check_h15_probe_middle :
    (machine.run 8 (startConfig 0 tag middleWord)).state.val = 10 ∧
    (machine.run 8 (startConfig 0 tag middleWord)).head.val = 11 ∧
    (machine.run 8 (startConfig 0 tag middleWord)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag middleWord)).state.val = 14 ∧
    (machine.run 9 (startConfig 0 tag middleWord)).head.val = 11 ∧
    (machine.run 9 (startConfig 0 tag middleWord)).tape ⟨10, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag middleWord)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag middleWord)).tape ⟨12, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag middleWord)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag middleWord)).tape ⟨9, by decide⟩ = some true := by
  rw [middle_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H15 on neither source physical, reduced.**  Out of `startConfig 0 tag tightWord` (`N = 11`,
`zeros = 2`): at step `8` the preamble's `qBackB` (index `10`) at head `10` on `some true`; at step
`9` G2y's `qLoop` (index `14`) at that same head, the terminator cell `10` preserved and the cell
past it blank — the stay exit, which does not move the walking terminator. -/
theorem check_h15_probe_tight :
    (machine.run 8 (startConfig 0 tag tightWord)).state.val = 10 ∧
    (machine.run 8 (startConfig 0 tag tightWord)).head.val = 10 ∧
    (machine.run 8 (startConfig 0 tag tightWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag tightWord)).state.val = 14 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).head.val = 10 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨9, by decide⟩ = some true := by
  rw [tight_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The two inherited handoffs, reduced in the composed control.**  Out of the same actual
`startConfig 0 tag physWord`: at step `74` the payload loop's `qFin` (index `33`) on the tag cell
`7`; at step `75` G2q's `qStart` (index `36`) on that same cell, `some false` preserved — H16; at
step `92` G2q's `qBorrow` (index `40`) on the register digit `22`, still `some true`; at step `93`
the countdown's `qStart` (index `43`) on that cell, now `some false` — H17.  These are G2y's steps
`63`/`64` and `81`/`82` shifted by the `11` steps the marker preamble takes.  The reduction is
bounded at `93` steps and does not touch the thousand-step drain. -/
theorem check_inherited_handoff_probe :
    (machine.run 74 (startConfig 0 tag physWord)).state.val = 33 ∧
    (machine.run 74 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 75 (startConfig 0 tag physWord)).state.val = 36 ∧
    (machine.run 75 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 75 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 92 (startConfig 0 tag physWord)).state.val = 40 ∧
    (machine.run 92 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 92 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 93 (startConfig 0 tag physWord)).state.val = 43 ∧
    (machine.run 93 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 93 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformed`: the handed-over
configuration is in neither composed verdict; one step later the composed reject — index `53`, not
the preamble's own `qReject` at index `13` — at the boundary head `11`; and it absorbs.  The routed
edge fired in that one transition. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state.val = 53 ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformed)).state.val = 53 := by
  rw [malformed_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetMarkersLoopDecrementCountdownSurfaceTests
