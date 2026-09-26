import Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

/-!
Surface pins for the Part A G3c concrete slice: G2p-b's first-payload table and G3a's whole
second-payload composite as **one** closed 86-state, 258-row table.  Its newly executed handoff H13
is the *single* live routed row `qSeekAnchor`-on-blank, targeting G3a's start at composed index
`18`; H14 (`29 → 32`), H15 (four routed rows into `46`, of which `2 ≤ zeros` reaches only `41` and
`42`), H16 (`65 → 68`) and H17 (`72 → 75`) are inherited from G3a and pinned here by the two
block-offset equations only, their rows being transported verbatim by the universal right-block row
equation; of those, `check_inherited_handoff_probe` reduces concretely H14, the `qClearB` row
`41 → 46`, H16 and H17, while the `qBackB` row `42 → 46` rests on that row equation and G2z's
probes, transported through two right-block row equations, and is reached by no fixture here.
Every public declaration is restated in full;
`check_clock_values` reduces the literal clocks the probes use:
`FixedGammaTargetFirstPayload.exactClock 17 4 = 32`, `... 12 2 = 20`, `... 11 2 = 18`,
`... 11 1 = 17`, `... 10 0 = 6`, `secondChainClock 17 4 0 24 = 1047` and
`firstChainClock 17 4 0 24 = 1079`.

The probes.  The tag is `10110010`.  `physWord` decodes to `zeros = 4` with `N = 17` and a physical
first payload cell; `middleWord` to `zeros = 2` with `N = 12`, physical; `oneWord` to `zeros = 1`
with `N = 11`, physical; `tightWord` to `zeros = 2` with `N = 11`, where the first payload cell
`9 + zeros` *is* the boundary blank and the copied bit is the virtual zero; `zeroWord` to
`zeros = 0` with `N = 10`, the one width that copies nothing.  All five take H13 through the same
one routed row — G2p-b has no other working-state row into `qDone` — so what the five probes
separate is the **switch time**, which is `2N + zeros - 6` in four positive-width fixtures and the
length-free `6` at width zero.  Each probe is a claim about its own word; nothing here says which
width an arbitrary word decodes to.  `check_first_handoff_instance` inhabits `handoff_exact`'s four
hypotheses in all four positive-width fixtures and `check_zero_width_instance` the premises of
`zero_width_handoff`, all at the *probe's* budget `B = 0`; `check_first_drained_instance` inhabits
the drain's seven at `B = 22`, where `4 + 2 + 24 = 8 + 22` meets the lane budget exactly — so budget
`0` is never presented as validating the 1079-step drain, and the short probes never establish the
long run's room premise.  The register value `24` is supplied **by hand**; `24 > N = 17`, so this is
a pnp3 execution fixture and neither an accepted-content fixture nor evidence for the pnp4 cap.

`check_handoff_literal` and `check_first_literal_endpoint` are **derived** from `handoff_exact` and
`first_payload_second_payload_markers_loop_decrement_countdown_drained` at those literals.  The
reduction probes are **independent**: `phys_start`, `middle_start`, `tight_start`, `one_start`,
`zero_start` and `malformed_start` identify the composed `startConfig B tag ·` with an explicit
configuration using only G2p-a's landed bootstrap endpoint theorems, which execute nothing, and
kernel computation then reads the composed machine back off that configuration.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the twelve earlier handoffs is executed or pinned; no first arrival of the composed
accept — the first arrival proved is G2p-b's, inside the left block; no fence, so an oversized
register still times out; width zero gets the switch and nothing downstream; the rejecting run is
exercised but is no converse and characterises no parsed target; no footprint theorem, so every room
premise is sufficient and used, never shown necessary; and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or language-membership statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown
  (secondChainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inFirst :
    Fin FixedGammaTargetFirstPayload.stateCount → Fin machine.stateCount := inFirst
def check_inChain :
    Fin FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inChain
def check_route :
    Fin FixedGammaTargetFirstPayload.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_firstChainClock (N zeros d v : Nat) : Nat := firstChainClock N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 86 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 258 ∧
      machine.start = route FixedGammaTargetFirstPayload.qStart ∧
      machine.start = inFirst FixedGammaTargetFirstPayload.qStart ∧
      machine.accept =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 84 ∧ machine.reject.val = 85 ∧
      (∀ q, (inFirst q).val = q.val) ∧ (∀ q, (inFirst q).val < 18) ∧
      (∀ q, (inChain q).val = 18 + q.val) ∧ (∀ q, 18 ≤ (inChain q).val) ∧
      (∀ q, (inChain (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inSecond q)).val
        = 18 + q.val) ∧
      (∀ q, (inChain (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inChain q)).val
        = 32 + q.val) ∧
      Function.Injective inFirst ∧ Function.Injective inChain ∧
      (∀ p q, inFirst p ≠ inChain q) ∧
      route FixedGammaTargetFirstPayload.qDone =
        inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTargetFirstPayload.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetFirstPayload.qDone →
        q ≠ FixedGammaTargetFirstPayload.qReject → route q = inFirst q) ∧
      (∀ q s, machine.step (inFirst q) s =
        (route (FixedGammaTargetFirstPayload.machine.step q s).1,
          (FixedGammaTargetFirstPayload.machine.step q s).2.1,
          (FixedGammaTargetFirstPayload.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inFirst FixedGammaTargetFirstPayload.qSeekAnchor).val = 15 ∧
      (inFirst FixedGammaTargetFirstPayload.qDone).val = 16 ∧
      (inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start).val = 18 ∧
      machine.step (inFirst FixedGammaTargetFirstPayload.qSeekAnchor) none =
        (inChain FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.start,
          some false, .stay) :=
  table_and_resource_pins

/-- The start, restated in full: G2p-b's `startConfig` routed into the composed control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetFirstPayload.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetFirstPayload.machine.seqEmbedRouted
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (N zeros d v : Nat) :
    firstChainClock N zeros d v =
        FixedGammaTargetFirstPayload.exactClock N zeros + secondChainClock N zeros d v ∧
      (0 < zeros → firstChainClock N zeros d v =
        2 * N + zeros - 6 + secondChainClock N zeros d v) ∧
      (2 ≤ zeros → firstChainClock N zeros d v =
        2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))) :=
  clock_pins N zeros d v

/-- The executed handoff H13 at a decoded `0 < zeros`, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let T := FixedGammaTargetFirstPayload.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRouted
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayload.machine.run t
            (FixedGammaTargetFirstPayload.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w))) :=
  handoff_exact x w htag hg hzeros hroom

/-- H13 at the decoded width zero, restated in full.  Nothing downstream is claimed here. -/
theorem check_zero_width_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let T := FixedGammaTargetFirstPayload.exactClock (a + m) 0
    let c := startConfig B x w
    T = 6 ∧
      (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      machine.run T c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetFirstPayload.machine.seqEmbedRight
          FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w))) :=
  zero_width_handoff x w htag hg

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := firstChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) :=
  first_payload_second_payload_markers_loop_decrement_countdown_drained x w htag hg hzeros hfence
    hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w htag hg s hs

/-- The literal clocks the probes use, reduced by kernel computation: G2p-b's first arrival at all
five probe widths — length-dependent at the four positive ones, length-free at width zero — G3a's
sum, and this slice's sum. -/
theorem check_clock_values :
    FixedGammaTargetFirstPayload.exactClock 17 4 = 32 ∧
      FixedGammaTargetFirstPayload.exactClock 12 2 = 20 ∧
      FixedGammaTargetFirstPayload.exactClock 11 2 = 18 ∧
      FixedGammaTargetFirstPayload.exactClock 11 1 = 17 ∧
      FixedGammaTargetFirstPayload.exactClock 10 0 = 6 ∧
      secondChainClock 17 4 0 24 = 1047 ∧ firstChainClock 17 4 0 24 = 1079 ∧
      firstChainClock 17 4 0 24 =
        FixedGammaTargetFirstPayload.exactClock 17 4 + secondChainClock 17 4 0 24 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The six probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def middleWord : Bitstring 4 := ![false, false, true, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def oneWord : Bitstring 3 := ![false, true, false]
private def zeroWord : Bitstring 2 := ![true, false]
private def malformed : Bitstring 3 := ![false, false, false]

/-- `handoff_exact`'s four hypotheses are satisfiable in all four positive-width fixtures, at the *probe's*
budget `B = 0`: the tag matches, the words decode to `zeros = 4`, `2`, `2` and `1`, and G2p-b's room
`19 < 27`, `14 < 22`, `13 < 21` and `13 < 21` holds. -/
theorem check_first_handoff_instance :
    (FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      0 < 4 ∧ 8 + 9 + 2 < tapeLength (pairLength 8 9) 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag middleWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag middleWord) = some 2 ∧
      0 < 2 ∧ 8 + 4 + 2 < tapeLength (pairLength 8 4) 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag tightWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag tightWord) = some 2 ∧
      0 < 2 ∧ 8 + 3 + 2 < tapeLength (pairLength 8 3) 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag oneWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag oneWord) = some 1 ∧
      0 < 1 ∧ 8 + 3 + 2 < tapeLength (pairLength 8 3) 0) :=
  ⟨⟨by decide, by decide, by omega, by decide⟩, ⟨by decide, by decide, by omega, by decide⟩,
    ⟨by decide, by decide, by omega, by decide⟩, ⟨by decide, by decide, by omega, by decide⟩⟩

/-- The premises of the width-zero handoff are satisfiable: `zeroWord` decodes to `zeros = 0` at
`N = 10` and needs no room. -/
theorem check_zero_width_instance :
    FixedContentTagGate.tagMatches (Fin.append tag zeroWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag zeroWord) = some 0 :=
  ⟨by decide, by decide⟩

/-- `malformed_reject_handoff`'s two hypotheses are satisfiable: the tag matches and the word has no
gamma terminator below the boundary `N = 11`. -/
theorem check_malformed_instance :
    FixedContentTagGate.tagMatches (Fin.append tag malformed) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag malformed) = none :=
  ⟨by decide, by decide⟩

/-- The drain's seven hypotheses are satisfiable at the physical fixture, at the *drain's* budget
`B = 22`: `zeros = 4`, the decremented digits are the bits of `24`, and `F = 24`, `B = 22` meet the
lane budget exactly.  The `24` is supplied by hand. -/
theorem check_first_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- H13 at the physical fixture, derived from `handoff_exact` rather than reduced: no composed
verdict before step `32 = 2 * 17 + 4 - 6`, and at step `32` G3a's actual `startConfig 0 tag
physWord`, re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 32 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 32 (startConfig 0 tag physWord) =
      FixedGammaTargetFirstPayload.machine.seqEmbedRight
        FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.startConfig 0 tag physWord) := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by decide)
  exact ⟨h1, h2⟩

/-- The composed endpoint at the physical fixture, derived rather than reduced: the composed accept
on the separator blank `23` after exactly `firstChainClock 17 4 0 24 = 1079` steps — `32` for the
first payload digit, none for H13, `27` for the second payload digit, none for H14, `11` for the
marker preamble, none for H15, `64` for the payload loop, none for H16, `18` for the decrement, none
for H17, `927` for the countdown — with the register emptied and twenty-four marks laid, persisting.
Nothing decodes the hand-written `24`. -/
theorem check_first_literal_endpoint :
    let e := machine.run (firstChainClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, firstChainClock (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    first_payload_second_payload_markers_loop_decrement_countdown_drained (a := 8) (m := 9)
      (B := 22) (zeros := 4) (v := 24) (F := 24) tag physWord (by decide) (by decide) (by omega)
      (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

/-- Rebuild a configuration from its projections, over a configuration *variable*, so that
identifying the phase-local start configuration never has to reduce the G2p-a run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

/-- The composed `startConfig B tag physWord`: the composed start on the terminator cell `8 + 4` over
G2p-a's scratch tape.  Only G2p-a's landed endpoint theorem is used, and it executes nothing. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨12, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag physWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 4) tag physWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem middle_start (B : Nat) :
    startConfig B tag middleWord =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨10, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag middleWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 2) tag middleWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem tight_start (B : Nat) :
    startConfig B tag tightWord =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨10, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag tightWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 2) tag tightWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem one_start (B : Nat) :
    startConfig B tag oneWord =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨9, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag oneWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 1) tag oneWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem zero_start (B : Nat) :
    startConfig B tag zeroWord =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨8, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag zeroWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 0) tag zeroWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem malformed_start (B : Nat) :
    startConfig B tag malformed =
      ⟨route FixedGammaTargetFirstPayload.qStart,
        ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

set_option maxRecDepth 100000 in
/-- **H13 on a physical first payload cell, reduced.**  Out of the actual composed
`startConfig 0 tag physWord` (`N = 17`, `zeros = 4`): at step `31` G2p-b's `qSeekAnchor` (index `15`)
back at the blanked anchor cell `7`; at step `32 = 2 * 17 + 4 - 6` G3a's start (index `18`) at that
same head, the anchor restored to `some false` by that very transition — the single routed row took
the machine across the block boundary while writing and staying.  The tape handed over carries
G2p-a's register `true` at `18` and G2p-b's first payload digit `true` at the target cell `19`. -/
theorem check_h13_probe_physical :
    (machine.run 31 (startConfig 0 tag physWord)).state.val = 15 ∧
    (machine.run 31 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 31 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 32 (startConfig 0 tag physWord)).state.val = 18 ∧
    (machine.run 32 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 32 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 32 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 32 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H13 at two further physical widths, reduced.**  Out of `startConfig 0 tag middleWord`
(`N = 12`, `zeros = 2`) the same routed row fires at step `20 = 2 * 12 + 2 - 6`, with the payload
bit `true` at the target cell `14`; out of `startConfig 0 tag oneWord` (`N = 11`, `zeros = 1`) at
step `17 = 2 * 11 + 1 - 6`, with the payload bit `false` at the target cell `13`.  Together with the
physical probe above these separate the switch time in both `N` and `zeros`. -/
theorem check_h13_probe_physical_short :
    (machine.run 19 (startConfig 0 tag middleWord)).state.val = 15 ∧
    (machine.run 20 (startConfig 0 tag middleWord)).state.val = 18 ∧
    (machine.run 20 (startConfig 0 tag middleWord)).head.val = 7 ∧
    (machine.run 20 (startConfig 0 tag middleWord)).tape ⟨13, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag middleWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 16 (startConfig 0 tag oneWord)).state.val = 15 ∧
    (machine.run 17 (startConfig 0 tag oneWord)).state.val = 18 ∧
    (machine.run 17 (startConfig 0 tag oneWord)).head.val = 7 ∧
    (machine.run 17 (startConfig 0 tag oneWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag oneWord)).tape ⟨13, by decide⟩ = some false := by
  rw [middle_start 0, one_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H13 on the virtual source, reduced** — the first payload cell `9 + zeros` *is* the boundary
blank.  Out of `startConfig 0 tag tightWord` (`N = 11`, `zeros = 2`): the same routed row at step
`18 = 2 * 11 + 2 - 6`, with the virtual `false` at the target cell `13`, the register `true` at `12`
left alone and the anchor restored. -/
theorem check_h13_probe_virtual :
    (machine.run 17 (startConfig 0 tag tightWord)).state.val = 15 ∧
    (machine.run 18 (startConfig 0 tag tightWord)).state.val = 18 ∧
    (machine.run 18 (startConfig 0 tag tightWord)).head.val = 7 ∧
    (machine.run 18 (startConfig 0 tag tightWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag tightWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag tightWord)).tape ⟨13, by decide⟩ = some false := by
  rw [tight_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H13 at width zero, reduced.**  Out of `startConfig 0 tag zeroWord` (`N = 10`, `zeros = 0`) the
same routed row fires at step `6` — length-free, because this width never walks the content.  The
target cell `12` is left blank: this width copies no payload digit.  That the tape handed over is
the incoming bootstrap scratch tape *in full*, with no net write, is `zero_width_exact`'s tape
equality and not one of the three cells read below.  Nothing downstream is claimed for it. -/
theorem check_h13_probe_zero_width :
    (machine.run 5 (startConfig 0 tag zeroWord)).state.val = 15 ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).state.val = 18 ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).head.val = 7 ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 6 (startConfig 0 tag zeroWord)).tape ⟨12, by decide⟩ = none := by
  rw [zero_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The four inherited handoffs, reduced in the composed control.**  Out of the same actual
`startConfig 0 tag physWord`: at steps `58`/`59` G2p-c's `qScanLeft` (index `29`) and G2p-d's marker
start (index `32`) on the anchor cell `7` — H14; at step `69` the marker preamble's `qClearB` (index
`41`) on the outgoing terminator cell `13` and at step `70` the payload loop's `qLoop` (index `46`)
at head `14` — H15; at steps `133`/`134` the loop's `qFin` (index `65`) and G2q's `qStart` (index
`68`) on the tag cell `7` — H16; at steps `151`/`152` G2q's `qBorrow` (index `72`) and the
countdown's `qStart` (index `75`) on the register digit `22`, which that transition clears — H17.
These are G3a's steps `26`/`27`, `37`/`38`, `101`/`102` and `119`/`120` shifted by the `32` steps
G2p-b takes.  The reduction is bounded at `152` steps and does not touch the thousand-step drain. -/
theorem check_inherited_handoff_probe :
    (machine.run 58 (startConfig 0 tag physWord)).state.val = 29 ∧
    (machine.run 58 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 59 (startConfig 0 tag physWord)).state.val = 32 ∧
    (machine.run 59 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 59 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 69 (startConfig 0 tag physWord)).state.val = 41 ∧
    (machine.run 69 (startConfig 0 tag physWord)).head.val = 13 ∧
    (machine.run 70 (startConfig 0 tag physWord)).state.val = 46 ∧
    (machine.run 70 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 133 (startConfig 0 tag physWord)).state.val = 65 ∧
    (machine.run 133 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 134 (startConfig 0 tag physWord)).state.val = 68 ∧
    (machine.run 134 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 151 (startConfig 0 tag physWord)).state.val = 72 ∧
    (machine.run 151 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 151 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 152 (startConfig 0 tag physWord)).state.val = 75 ∧
    (machine.run 152 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformed`: the handed-over
configuration is in neither composed verdict; one step later the composed reject — index `85`, not
G2p-b's own `qReject` at index `17` nor G2p-c's at `31` — at the boundary head `11`; and it absorbs.
The routed edge fired in that one transition. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state.val = 85 ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformed)).state.val = 85 := by
  rw [malformed_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
