import Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown

/-!
Surface pins for the Part A G3a concrete slice: G2p-c's second-payload table and G2z's whole
marker-loop composite as **one** closed 68-state, 204-row table.  Its newly executed handoff H14 is
the *single* live routed row `qScanLeft`-on-blank, targeting G2z's start at composed index `14`;
H15 (four routed rows into `28`, of which `2 ≤ zeros` reaches only `23` and `24`), H16
(`47 → 50`) and H17 (`54 → 57`) are inherited from G2z and pinned
here by composed index only, their rows being transported verbatim by the universal right-block row
equation; of those, `check_inherited_handoff_probe` reduces concretely the `qClearB` row `23 → 28`,
H16 and H17, while the `qBackB` row `24 → 28` rests on that row equation and G2z's own probes and is
reached by no fixture here.  Every public declaration is
restated in full; `check_clock_values` reduces the literal clocks the probes
use: `FixedGammaTargetSecondPayload.exactClock 17 4 = 27`, `... 12 2 = 17`, `... 11 2 = 15`,
`... 10 0 = 3`, `... 11 1 = 5`, `markersChainClock 17 4 0 24 = 1020` and
`secondChainClock 17 4 0 24 = 1047`.

The probes.  The tag is `10110010`.  `physWord` decodes to `zeros = 4` with `N = 17` and both
payload sources physical; `middleWord` to `zeros = 2` with `N = 12` and the second source on the
boundary blank; `tightWord` to `zeros = 2` with `N = 11`, where the *first* payload cell is already
the boundary and `qRead` is bypassed; `zeroWord` to `zeros = 0` with `N = 10` and `oneWord` to
`zeros = 1` with `N = 11`.  All five take H14 through the same one routed row — G2p-c has no other
working-state row into `qDone` — so what the five probes separate is the **switch time**, which
unlike G2z's is length-dependent: `2N - 7` at the three positive widths and the length-free `3` and
`5` at the two degenerate ones.  Each probe is a claim about its own word; nothing here says which
width an arbitrary word decodes to.  `check_second_handoff_instance` inhabits `handoff_exact`'s four
hypotheses at all three positive shapes and `check_degenerate_handoff_instance` the premises of
`zero_width_handoff` and `width_one_handoff`, all at the *probe's* budget `B = 0`;
`check_second_drained_instance` inhabits the drain's seven at `B = 22`, where `4 + 2 + 24 = 8 + 22`
meets the lane budget exactly — so budget `0` is never presented as validating the 1047-step drain,
and the short probes never establish the long run's room premise.  The register value `24` is
supplied **by hand**; `24 > N = 17`, so this is a pnp3 execution fixture and neither an
accepted-content fixture nor evidence for the pnp4 cap.

`check_handoff_literal` and `check_second_literal_endpoint` are **derived** from `handoff_exact` and
`second_payload_markers_loop_decrement_countdown_drained` at those literals.  The reduction probes
are **independent**: `phys_start`, `middle_start`, `tight_start`, `zero_start`, `one_start` and
`malformed_start` identify the composed `startConfig B tag ·` with an explicit configuration using
only G2p-b's landed first-payload endpoint theorems, which execute nothing, and kernel computation
then reads the composed machine back off that configuration.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the thirteen earlier handoffs is executed or pinned; no first arrival of the
composed accept — the first arrival proved is G2p-c's, inside the left block; no fence, so an
oversized register still times out; the two degenerate widths get the switch and nothing downstream;
the rejecting run is exercised but is no converse and characterises no parsed target; no footprint
theorem, so every room premise is sufficient and used, never shown necessary; and no `accepts`,
`AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetMarkersLoopDecrementCountdown (markersChainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inSecond :
    Fin FixedGammaTargetSecondPayload.stateCount → Fin machine.stateCount := inSecond
def check_inChain :
    Fin FixedGammaTargetMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inChain
def check_route :
    Fin FixedGammaTargetSecondPayload.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_secondChainClock (N zeros d v : Nat) : Nat := secondChainClock N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 68 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 204 ∧
      machine.start = route FixedGammaTargetSecondPayload.qStart ∧
      machine.start = inSecond FixedGammaTargetSecondPayload.qStart ∧
      machine.accept =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 66 ∧ machine.reject.val = 67 ∧
      (∀ q, (inSecond q).val = q.val) ∧ (∀ q, (inSecond q).val < 14) ∧
      (∀ q, (inChain q).val = 14 + q.val) ∧ (∀ q, 14 ≤ (inChain q).val) ∧
      (∀ q, (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers q)).val
        = 14 + q.val) ∧
      (∀ q, (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail q)).val
        = 28 + q.val) ∧
      Function.Injective inSecond ∧ Function.Injective inChain ∧
      (∀ p q, inSecond p ≠ inChain q) ∧
      route FixedGammaTargetSecondPayload.qDone =
        inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetSecondPayload.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetSecondPayload.qDone →
        q ≠ FixedGammaTargetSecondPayload.qReject → route q = inSecond q) ∧
      (∀ q s, machine.step (inSecond q) s =
        (route (FixedGammaTargetSecondPayload.machine.step q s).1,
          (FixedGammaTargetSecondPayload.machine.step q s).2.1,
          (FixedGammaTargetSecondPayload.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inSecond FixedGammaTargetSecondPayload.qScanLeft).val = 11 ∧
      (inSecond FixedGammaTargetSecondPayload.qDone).val = 12 ∧
      (inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start).val = 14 ∧
      machine.step (inSecond FixedGammaTargetSecondPayload.qScanLeft) none =
        (inChain FixedGammaTargetMarkersLoopDecrementCountdown.machine.start, some false,
          .stay) ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers
        FixedGammaTargetPayloadLoopFoundation.qClearB)).val = 23 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inMarkers
        FixedGammaTargetPayloadLoopFoundation.qBackB)).val = 24 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        FixedGammaTargetLoopDecrementCountdown.machine.start)).val = 28 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inLoop
          FixedGammaTargetPayloadRound.qFin))).val = 47 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          FixedGammaTargetDecrementCountdown.machine.start))).val = 50 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inDecrement
            FixedGammaTargetRegisterDecrement.qBorrow)))).val = 54 ∧
      (inChain (FixedGammaTargetMarkersLoopDecrementCountdown.inTail
        (FixedGammaTargetLoopDecrementCountdown.inTail
          (FixedGammaTargetDecrementCountdown.inCountdown
            FixedGammaTargetUnaryCountdown.qStart)))).val = 57 :=
  table_and_resource_pins

/-- The start, restated in full: G2p-c's `startConfig` routed into the composed control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetSecondPayload.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetSecondPayload.machine.seqEmbedRouted
        FixedGammaTargetMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (N zeros d v : Nat) :
    secondChainClock N zeros d v =
        FixedGammaTargetSecondPayload.exactClock N zeros +
          markersChainClock N zeros d v ∧
      (2 ≤ zeros → secondChainClock N zeros d v =
        2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))) :=
  clock_pins N zeros d v

/-- The executed handoff H14 at a decoded `2 ≤ zeros`, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRouted
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayload.machine.run t
            (FixedGammaTargetSecondPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) :=
  handoff_exact x w htag hg hzeros hroom

/-- H14 at the decoded width zero, restated in full.  Nothing downstream is claimed here. -/
theorem check_zero_width_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) 0
    let c := startConfig B x w
    T = 3 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) :=
  zero_width_handoff x w htag hg

/-- H14 at the decoded width one, restated in full.  Nothing downstream is claimed here. -/
theorem check_width_one_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetSecondPayload.exactClock (a + m) 1
    let c := startConfig B x w
    T = 5 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetSecondPayload.machine.seqEmbedRight
          FixedGammaTargetMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig B x w))) :=
  width_one_handoff x w htag hg hroom

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_second_payload_markers_loop_decrement_countdown_drained {a m B zeros v F : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := secondChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) :=
  second_payload_markers_loop_decrement_countdown_drained x w htag hg hzeros hfence hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w htag hg s hs

/-- The literal clocks the probes use, reduced by kernel computation: G2p-c's first arrival at all
five probe widths — length-dependent at the three positive ones, length-free at the two degenerate
ones — G2z's sum, and this slice's sum. -/
theorem check_clock_values :
    FixedGammaTargetSecondPayload.exactClock 17 4 = 27 ∧
      FixedGammaTargetSecondPayload.exactClock 12 2 = 17 ∧
      FixedGammaTargetSecondPayload.exactClock 11 2 = 15 ∧
      FixedGammaTargetSecondPayload.exactClock 10 0 = 3 ∧
      FixedGammaTargetSecondPayload.exactClock 11 1 = 5 ∧
      markersChainClock 17 4 0 24 = 1020 ∧ secondChainClock 17 4 0 24 = 1047 ∧
      secondChainClock 17 4 0 24 =
        FixedGammaTargetSecondPayload.exactClock 17 4 + markersChainClock 17 4 0 24 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The five probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def middleWord : Bitstring 4 := ![false, false, true, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def zeroWord : Bitstring 2 := ![true, false]
private def oneWord : Bitstring 3 := ![false, true, false]
private def malformed : Bitstring 3 := ![false, false, false]

/-- `handoff_exact`'s four hypotheses are satisfiable at all three positive source shapes, at the
*probe's* budget `B = 0`: the tag matches, the words decode to `zeros = 4`, `2` and `2`, and G2p-c's
room `20 < 27`, `15 < 22` and `14 < 21` holds. -/
theorem check_second_handoff_instance :
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

/-- The premises of the two degenerate-width handoffs are satisfiable: `zeroWord` decodes to
`zeros = 0` at `N = 10` and needs no room, `oneWord` to `zeros = 1` at `N = 11` under G2p-b's
weaker room `13 < 21`. -/
theorem check_degenerate_handoff_instance :
    (FixedContentTagGate.tagMatches (Fin.append tag zeroWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag zeroWord) = some 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag oneWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag oneWord) = some 1 ∧
      8 + 3 + 2 < tapeLength (pairLength 8 3) 0) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- `malformed_reject_handoff`'s two hypotheses are satisfiable: the tag matches and the word has no
gamma terminator below the boundary `N = 11`. -/
theorem check_malformed_instance :
    FixedContentTagGate.tagMatches (Fin.append tag malformed) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag malformed) = none :=
  ⟨by decide, by decide⟩

/-- `second_payload_markers_loop_decrement_countdown_drained`'s seven hypotheses are satisfiable at
the physical fixture, at the *drain's* budget `B = 22`: `zeros = 4`, the decremented digits are the
bits of `24`, and `F = 24`, `B = 22` meet the lane budget exactly.  The `24` is supplied by hand. -/
theorem check_second_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- H14 at the physical fixture, derived from `handoff_exact` rather than reduced: no composed
verdict before step `27 = 2 * 17 - 7`, and at step `27` G2z's actual `startConfig 0 tag physWord`,
re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 27 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 27 (startConfig 0 tag physWord) =
      FixedGammaTargetSecondPayload.machine.seqEmbedRight
        FixedGammaTargetMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetMarkersLoopDecrementCountdown.startConfig 0 tag physWord) := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by decide)
  exact ⟨h1, h2⟩

/-- The composed endpoint at the physical fixture, derived rather than reduced: the composed accept
on the separator blank `23` after exactly `secondChainClock 17 4 0 24 = 1047` steps — `27` for the
second payload digit, none for H14, `11` for the marker preamble, none for H15, `64` for the payload
loop, none for H16, `18` for the decrement, none for H17, `927` for the countdown — with the
register emptied and twenty-four marks laid, persisting.  Nothing decodes the hand-written `24`. -/
theorem check_second_literal_endpoint :
    let e := machine.run (secondChainClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, secondChainClock (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    second_payload_markers_loop_decrement_countdown_drained (a := 8) (m := 9) (B := 22)
      (zeros := 4) (v := 24) (F := 24) tag physWord (by decide) (by decide) (by omega) (by omega)
      (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

/-- Rebuild a configuration from its projections, over a configuration *variable*, so that
identifying the phase-local start configuration never has to reduce the G2p-b run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

/-- The composed `startConfig B tag physWord`: the composed start on head `7` over G2p-b's
first-payload tape.  Only G2p-b's landed endpoint theorem is used, and it executes nothing. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag physWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag physWord) (9 + 4)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_payload_at_deadline
    (B := B) (zeros := 4) tag physWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem middle_start (B : Nat) :
    startConfig B tag middleWord =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag middleWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag middleWord) (9 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_payload_at_deadline
    (B := B) (zeros := 2) tag middleWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem tight_start (B : Nat) :
    startConfig B tag tightWord =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag tightWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag tightWord) (9 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_payload_at_deadline
    (B := B) (zeros := 2) tag tightWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem zero_start (B : Nat) :
    startConfig B tag zeroWord =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag zeroWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.zero_width_at_deadline
    (B := B) tag zeroWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem one_start (B : Nat) :
    startConfig B tag oneWord =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag oneWord
          ((FixedContentTagGate.physicalSymbol (Fin.append tag oneWord) (9 + 1)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_payload_at_deadline
    (B := B) (zeros := 1) tag oneWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

private theorem malformed_start (B : Nat) :
    startConfig B tag malformed =
      ⟨route FixedGammaTargetSecondPayload.qStart,
        ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

set_option maxRecDepth 100000 in
/-- **H14 on both payload sources physical, reduced.**  Out of the actual composed
`startConfig 0 tag physWord` (`N = 17`, `zeros = 4`): at step `26` G2p-c's `qScanLeft` (index `11`)
back at the blanked anchor cell `7`; at step `27 = 2 * 17 - 7` G2z's start (index `14`) at that same
head, the anchor restored to `some false` by that very transition — the single routed row took the
machine across the block boundary while writing and staying.  The tape handed over carries the
register `true` at `18`, G2p-b's first payload digit `true` at `19` and G2p-c's second payload digit
`false` at the target cell `20`. -/
theorem check_h14_probe_physical :
    (machine.run 26 (startConfig 0 tag physWord)).state.val = 11 ∧
    (machine.run 26 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 26 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 27 (startConfig 0 tag physWord)).state.val = 14 ∧
    (machine.run 27 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H14 on the middle source shape, reduced** — the first payload source physical, the second the
boundary blank.  Out of `startConfig 0 tag middleWord` (`N = 12`, `zeros = 2`): the same routed row
at step `17 = 2 * 12 - 7`, with the virtual `false` at the target cell `15`. -/
theorem check_h14_probe_middle :
    (machine.run 16 (startConfig 0 tag middleWord)).state.val = 11 ∧
    (machine.run 16 (startConfig 0 tag middleWord)).head.val = 7 ∧
    (machine.run 17 (startConfig 0 tag middleWord)).state.val = 14 ∧
    (machine.run 17 (startConfig 0 tag middleWord)).head.val = 7 ∧
    (machine.run 17 (startConfig 0 tag middleWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 17 (startConfig 0 tag middleWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag middleWord)).tape ⟨15, by decide⟩ = some false := by
  rw [middle_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H14 with `qRead` bypassed, reduced** — the *first* payload cell is already the boundary blank,
so `qStepOne` hands straight to the register.  Out of `startConfig 0 tag tightWord` (`N = 11`,
`zeros = 2`): the same routed row at step `15 = 2 * 11 - 7`, with virtual `false` at both `13` and
the target cell `14`. -/
theorem check_h14_probe_tight :
    (machine.run 14 (startConfig 0 tag tightWord)).state.val = 11 ∧
    (machine.run 14 (startConfig 0 tag tightWord)).head.val = 7 ∧
    (machine.run 15 (startConfig 0 tag tightWord)).state.val = 14 ∧
    (machine.run 15 (startConfig 0 tag tightWord)).head.val = 7 ∧
    (machine.run 15 (startConfig 0 tag tightWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 15 (startConfig 0 tag tightWord)).tape ⟨13, by decide⟩ = some false ∧
    (machine.run 15 (startConfig 0 tag tightWord)).tape ⟨14, by decide⟩ = some false := by
  rw [tight_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H14 at the two degenerate widths, reduced.**  Out of `startConfig 0 tag zeroWord` (`N = 10`,
`zeros = 0`) the same routed row fires at step `3`, and out of `startConfig 0 tag oneWord`
(`N = 11`, `zeros = 1`) at step `5` — both length-free, because neither width walks the content.
Each leaves the tape it was handed with no net write — that is the tape equality of
`zero_width_exact`/`width_one_exact`, not a conjunct below — so neither is followed downstream. -/
theorem check_h14_probe_degenerate :
    (machine.run 2 (startConfig 0 tag zeroWord)).state.val = 11 ∧
    (machine.run 3 (startConfig 0 tag zeroWord)).state.val = 14 ∧
    (machine.run 3 (startConfig 0 tag zeroWord)).head.val = 7 ∧
    (machine.run 3 (startConfig 0 tag zeroWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 4 (startConfig 0 tag oneWord)).state.val = 11 ∧
    (machine.run 5 (startConfig 0 tag oneWord)).state.val = 14 ∧
    (machine.run 5 (startConfig 0 tag oneWord)).head.val = 7 ∧
    (machine.run 5 (startConfig 0 tag oneWord)).tape ⟨7, by decide⟩ = some false := by
  rw [zero_start 0, one_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The three inherited handoffs, reduced in the composed control.**  Out of the same actual
`startConfig 0 tag physWord`: at step `37` the marker preamble's `qClearB` (index `23`) on the
outgoing terminator cell `13` and at step `38` the payload loop's `qLoop` (index `28`) at head `14`
— H15; at steps `101`/`102` the loop's `qFin` (index `47`) and G2q's `qStart` (index `50`) on the
tag cell `7` — H16; at steps `119`/`120` G2q's `qBorrow` (index `54`) and the countdown's `qStart`
(index `57`) on the register digit `22`, which that transition clears — H17.  These are G2z's steps
`10`/`11`, `74`/`75` and `92`/`93` shifted by the `27` steps G2p-c takes.  The reduction is bounded
at `120` steps and does not touch the thousand-step drain. -/
theorem check_inherited_handoff_probe :
    (machine.run 37 (startConfig 0 tag physWord)).state.val = 23 ∧
    (machine.run 37 (startConfig 0 tag physWord)).head.val = 13 ∧
    (machine.run 38 (startConfig 0 tag physWord)).state.val = 28 ∧
    (machine.run 38 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 101 (startConfig 0 tag physWord)).state.val = 47 ∧
    (machine.run 101 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 102 (startConfig 0 tag physWord)).state.val = 50 ∧
    (machine.run 102 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 119 (startConfig 0 tag physWord)).state.val = 54 ∧
    (machine.run 119 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 119 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 120 (startConfig 0 tag physWord)).state.val = 57 ∧
    (machine.run 120 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformed`: the handed-over
configuration is in neither composed verdict; one step later the composed reject — index `67`, not
G2p-c's own `qReject` at index `13` nor G2z's at `53` — at the boundary head `11`; and it absorbs.
The routed edge fired in that one transition. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state.val = 67 ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformed)).state.val = 67 := by
  rw [malformed_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
