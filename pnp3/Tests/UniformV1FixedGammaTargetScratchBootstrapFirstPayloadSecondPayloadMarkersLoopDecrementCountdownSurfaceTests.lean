import
  Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3e concrete slice: G2p-a's scratch-bootstrap table and G3c's whole
first-payload composite as **one** closed 95-state, 285-row table.  Its newly executed handoff H12
is the *single* live routed row `qScanLeft`-on-blank, targeting G3c's start at composed index `9`;
H13 (`24 → 27`), H14 (`38 → 41`), H15 (four routed rows into `55`, of which `2 ≤ zeros` reaches
only `50` and `51`), H16 (`74 → 77`) and H17 (`81 → 84`) are inherited from G3c and pinned here by
the four block-offset equations only, their rows being transported verbatim by the universal
right-block row equation; of those, `check_inherited_handoff_probe` reduces concretely H13, H14,
the `qClearB` row `50 → 55`, H16 and H17, while the `qBackB` row `51 → 55` rests on that row
equation and G2z's probes, transported through three right-block row equations, and is reached by
no fixture here.  Every public declaration is restated in full; `check_clock_values` reduces the
literal clocks the probes use: `FixedGammaTerminatorScratchBootstrap.exactClock 17 4 = 19`,
`... 12 2 = 11`, `... 11 2 = 9`, `... 11 1 = 10`, `... 10 0 = 9`, `firstChainClock 17 4 0 24 = 1079`
and `bootChainClock 17 4 0 24 = 1098`.

The probes.  The tag is `10110010`.  `physWord` decodes to `zeros = 4` with `N = 17`; `middleWord`
to `zeros = 2` with `N = 12`; `oneWord` to `zeros = 1` with `N = 11`; `tightWord` to `zeros = 2`
with `N = 11`; `zeroWord` to `zeros = 0` with `N = 10`, the one width whose incoming dispatcher
head is `7` rather than `6`.  All five take H12 through the same one routed row — G2p-a has no
other working-state row into `qTerm` — so what the five probes separate is the **switch time**,
which is `2N - 11 - zeros` at every decoded width, width zero included.  Each probe is a claim
about its own word; nothing here says which width an arbitrary word decodes to.
`check_boot_handoff_instance` inhabits `handoff_exact`'s **two** hypotheses in all five fixtures;
the configuration parameter is `B = 0`, but those hypotheses mention neither `B`, room nor a
positive width, so no room conjunct appears — and `check_boot_drained_instance` inhabits the drain's seven at `B = 22`, where
`4 + 2 + 24 = 8 + 22` meets the lane budget exactly, so budget `0` is never presented as validating
the 1098-step drain.  The register value `24` is supplied **by hand**; `24 > N = 17`, so this is a
pnp3 execution fixture and neither an accepted-content fixture nor evidence for the pnp4 cap.

`check_handoff_literal` and `check_boot_literal_endpoint` are **derived** from `handoff_exact` and
`scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained` at those
literals.  The reduction probes are **independent**: `phys_start`, `middle_start`, `tight_start`,
`one_start`, `zero_start` and `malformed_start` identify the composed `startConfig B tag ·` with an
explicit configuration using only G2m's landed dispatcher endpoint classification, which executes
nothing, and kernel computation then reads the composed machine back off that configuration.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the eleven earlier handoffs is executed or pinned; no first arrival of the composed
accept — the first arrival proved is G2p-a's, inside the left block; no fence, so an oversized
register still times out; the rejecting run is exercised but is no converse and characterises no
parsed target; no footprint theorem for the composite, so every room premise of the tail is
sufficient and used, never shown necessary; and no `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (firstChainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_machine : UniformTM := machine
def check_inBoot :
    Fin FixedGammaTerminatorScratchBootstrap.stateCount → Fin machine.stateCount := inBoot
def check_inChain :
    Fin FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inChain
def check_route :
    Fin FixedGammaTerminatorScratchBootstrap.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_bootChainClock (N zeros d v : Nat) : Nat := bootChainClock N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 95 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 285 ∧
      machine.start = route FixedGammaTerminatorScratchBootstrap.qStart ∧
      machine.start = inBoot FixedGammaTerminatorScratchBootstrap.qStart ∧
      machine.accept =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 93 ∧ machine.reject.val = 94 ∧
      (∀ q, (inBoot q).val = q.val) ∧ (∀ q, (inBoot q).val < 9) ∧
      (∀ q, (inChain q).val = 9 + q.val) ∧ (∀ q, 9 ≤ (inChain q).val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inFirst q)).val
        = 9 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain q)).val
        = 27 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inSecond q))).val
        = 27 + q.val) ∧
      (∀ q, (inChain
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inChain
          (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.inChain q))).val
        = 41 + q.val) ∧
      Function.Injective inBoot ∧ Function.Injective inChain ∧
      (∀ p q, inBoot p ≠ inChain q) ∧
      route FixedGammaTerminatorScratchBootstrap.qTerm =
        inChain
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      route FixedGammaTerminatorScratchBootstrap.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTerminatorScratchBootstrap.qTerm →
        q ≠ FixedGammaTerminatorScratchBootstrap.qReject → route q = inBoot q) ∧
      (∀ q s, machine.step (inBoot q) s =
        (route (FixedGammaTerminatorScratchBootstrap.machine.step q s).1,
          (FixedGammaTerminatorScratchBootstrap.machine.step q s).2.1,
          (FixedGammaTerminatorScratchBootstrap.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inChain q) s =
        (inChain
            (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inBoot FixedGammaTerminatorScratchBootstrap.qScanLeft).val = 6 ∧
      (inBoot FixedGammaTerminatorScratchBootstrap.qTerm).val = 7 ∧
      (inChain
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start).val
        = 9 ∧
      machine.step (inBoot FixedGammaTerminatorScratchBootstrap.qScanLeft) none =
        (inChain
            FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start,
          some true, .stay) :=
  table_and_resource_pins

/-- The start, restated in full: G2p-a's `startConfig` routed into the composed control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTerminatorScratchBootstrap.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (N zeros d v : Nat) :
    bootChainClock N zeros d v =
        FixedGammaTerminatorScratchBootstrap.exactClock N zeros +
          firstChainClock N zeros d v ∧
      bootChainClock N zeros d v = 2 * N - 11 - zeros + firstChainClock N zeros d v ∧
      (2 ≤ zeros → bootChainClock N zeros d v =
        2 * N - 11 - zeros +
          (2 * N + zeros - 6 +
            (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v))))) :=
  clock_pins N zeros d v

/-- The executed handoff H12 at every decoded width, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let T := FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRouted
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTerminatorScratchBootstrap.machine.run t
            (FixedGammaTerminatorScratchBootstrap.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
          FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run s
            (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) :=
  handoff_exact x w htag hg

/-- The semantic content of the switch, restated in full: the head and whole tape handed over are
G2p-b's own `startConfig` projections. -/
theorem check_handoff_endpoint_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let T := FixedGammaTerminatorScratchBootstrap.exactClock (a + m) zeros
    let e := machine.run T (startConfig B x w)
    let p := FixedGammaTargetFirstPayload.startConfig B x w
    e.head.val = 8 + zeros ∧
      e.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      p.head.val = 8 + zeros ∧
      p.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      e.head = p.head ∧ e.tape = p.tape :=
  handoff_endpoint_pins x w htag hg

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := bootChainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) :=
  scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained x w htag
    hg hzeros hfence hroom hv hhigh

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w htag hg s hs

/-- The literal clocks the probes use, reduced by kernel computation: G2p-a's first arrival in all
five fixtures over four widths — including width zero and needing no case split — G3c's
sum, and this slice's sum. -/
theorem check_clock_values :
    FixedGammaTerminatorScratchBootstrap.exactClock 17 4 = 19 ∧
      FixedGammaTerminatorScratchBootstrap.exactClock 12 2 = 11 ∧
      FixedGammaTerminatorScratchBootstrap.exactClock 11 2 = 9 ∧
      FixedGammaTerminatorScratchBootstrap.exactClock 11 1 = 10 ∧
      FixedGammaTerminatorScratchBootstrap.exactClock 10 0 = 9 ∧
      firstChainClock 17 4 0 24 = 1079 ∧ bootChainClock 17 4 0 24 = 1098 ∧
      bootChainClock 17 4 0 24 =
        FixedGammaTerminatorScratchBootstrap.exactClock 17 4 + firstChainClock 17 4 0 24 :=
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

/-- `handoff_exact`'s **two** hypotheses are satisfiable in all five probe fixtures: the tag matches
and the words decode to `zeros = 4`, `2`, `2`, `1` and `0`.  There is no third conjunct: G2p-a's
phase needs no room, and its clock does not split on the width, so width zero enters through the
same statement as the four positive-width fixtures. -/
theorem check_boot_handoff_instance :
    (FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag middleWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag middleWord) = some 2) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag tightWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag tightWord) = some 2) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag oneWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag oneWord) = some 1) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag zeroWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag zeroWord) = some 0) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- `malformed_reject_handoff`'s two hypotheses are satisfiable: the tag matches and the word has
no gamma terminator below the boundary `N = 11`. -/
theorem check_malformed_instance :
    FixedContentTagGate.tagMatches (Fin.append tag malformed) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag malformed) = none :=
  ⟨by decide, by decide⟩

/-- The drain's seven hypotheses are satisfiable at the physical fixture, at the *drain's* budget
`B = 22`: `zeros = 4`, the decremented digits are the bits of `24`, and `F = 24`, `B = 22` meet the
lane budget exactly.  The `24` is supplied by hand. -/
theorem check_boot_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- H12 at the physical fixture, derived from `handoff_exact` rather than reduced: no composed
verdict before step `19 = 2 * 17 - 11 - 4`, and at step `19` G3c's actual `startConfig 0 tag
physWord`, re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 19 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 19 (startConfig 0 tag physWord) =
      FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight
        FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag physWord) := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide) (by decide)
  exact ⟨h1, h2⟩

/-- The composed endpoint at the physical fixture, derived rather than reduced: the composed accept
on the separator blank `23` after exactly `bootChainClock 17 4 0 24 = 1098` steps — `19` for the
scratch bootstrap, none for H12, `32` for the first payload digit, none for H13, `27` for the second
payload digit, none for H14, `11` for the marker preamble, none for H15, `64` for the payload loop,
none for H16, `18` for the decrement, none for H17, `927` for the countdown — with the register
emptied and twenty-four marks laid, persisting.  Nothing decodes the hand-written `24`. -/
theorem check_boot_literal_endpoint :
    let e := machine.run (bootChainClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, bootChainClock (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      (a := 8) (m := 9) (B := 22) (zeros := 4) (v := 24) (F := 24) tag physWord (by decide)
      (by decide) (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

/-- Rebuild a configuration from its projections, over a configuration *variable*, so that
identifying the phase-local start configuration never has to reduce the G2m dispatcher run term
inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

/-- The bootstrap start projections at a decoded **positive** width, read off G2m's landed endpoint
classification: the dispatcher head `6` on the unchanged `contentTape`.  Nothing is executed. -/
private theorem boot_start_pos {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros) :
    (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head.val = 6 ∧
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨htape, hcases⟩ :=
    FixedGammaPayloadDispatcherDeadline.tagged_endpoint_classification (B := B) x w htag
  rw [hg] at hcases
  rcases hcases with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨z, -, -, hh, -⟩
  · cases h
  · exact absurd (Option.some.inj h) (by omega)
  · exact ⟨hh, htape⟩

/-- The same at the decoded width **zero**, where the dispatcher stops one cell further right. -/
private theorem boot_start_zero {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head.val = 7 ∧
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨htape, hcases⟩ :=
    FixedGammaPayloadDispatcherDeadline.tagged_endpoint_classification (B := B) x w htag
  rw [hg] at hcases
  rcases hcases with ⟨-, -, h⟩ | ⟨-, hh, -⟩ | ⟨z, hz, hpos, -, -⟩
  · cases h
  · exact ⟨hh, htape⟩
  · exact absurd (Option.some.inj hz).symm (by omega)

/-- The same on a **malformed** gamma, where the dispatcher stopped at the blank boundary cell. -/
private theorem boot_start_malformed {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    (FixedGammaTerminatorScratchBootstrap.startConfig B x w).head.val = a + m ∧
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨htape, hcases⟩ :=
    FixedGammaPayloadDispatcherDeadline.tagged_endpoint_classification (B := B) x w htag
  rw [hg] at hcases
  rcases hcases with ⟨-, hh, -⟩ | ⟨-, -, h⟩ | ⟨z, h, -, -, -⟩
  · exact ⟨hh, htape⟩
  · cases h
  · cases h

/-- The composed `startConfig B tag physWord`: the composed start on the dispatcher's head `6` over
the unchanged content tape.  Only G2m's landed classification is used, and it executes nothing. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag physWord⟩ :=
  let ⟨hh, ht⟩ := boot_start_pos (B := B) (zeros := 4) tag physWord (by decide) (by decide)
    (by omega)
  config_of_parts rfl hh ht

private theorem middle_start (B : Nat) :
    startConfig B tag middleWord =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag middleWord⟩ :=
  let ⟨hh, ht⟩ := boot_start_pos (B := B) (zeros := 2) tag middleWord (by decide) (by decide)
    (by omega)
  config_of_parts rfl hh ht

private theorem tight_start (B : Nat) :
    startConfig B tag tightWord =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag tightWord⟩ :=
  let ⟨hh, ht⟩ := boot_start_pos (B := B) (zeros := 2) tag tightWord (by decide) (by decide)
    (by omega)
  config_of_parts rfl hh ht

private theorem one_start (B : Nat) :
    startConfig B tag oneWord =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag oneWord⟩ :=
  let ⟨hh, ht⟩ := boot_start_pos (B := B) (zeros := 1) tag oneWord (by decide) (by decide)
    (by omega)
  config_of_parts rfl hh ht

private theorem zero_start (B : Nat) :
    startConfig B tag zeroWord =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag zeroWord⟩ :=
  let ⟨hh, ht⟩ := boot_start_zero (B := B) tag zeroWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem malformed_start (B : Nat) :
    startConfig B tag malformed =
      ⟨route FixedGammaTerminatorScratchBootstrap.qStart,
        ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨hh, ht⟩ := boot_start_malformed (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

set_option maxRecDepth 100000 in
/-- **H12 at a decoded width four, reduced.**  Out of the actual composed `startConfig 0 tag
physWord` (`N = 17`, `zeros = 4`): at step `18` G2p-a's `qScanLeft` (index `6`) on its own return
marker, the blanked terminator cell `12`; at step `19 = 2 * 17 - 11 - 4` G3c's start (index `9`) at
that same head, the terminator restored to `some true` by that very transition — the single routed
row took the machine across the block boundary while writing and staying.  The tape handed over
carries G2p-a's scratch `true` at the register cell `18` and the blank boundary at `17`. -/
theorem check_h12_probe_physical :
    (machine.run 18 (startConfig 0 tag physWord)).state.val = 6 ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = none ∧
    (machine.run 19 (startConfig 0 tag physWord)).state.val = 9 ∧
    (machine.run 19 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 19 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag physWord)).tape ⟨17, by decide⟩ = none ∧
    (machine.run 19 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H12 in three further fixtures, reduced.**  Out of `startConfig 0 tag middleWord` (`N = 12`,
`zeros = 2`) the same routed row fires at step `11 = 2 * 12 - 11 - 2`, restoring the terminator at
`10` and leaving the scratch `true` at `13`; out of `startConfig 0 tag oneWord` (`N = 11`,
`zeros = 1`) at step `10 = 2 * 11 - 11 - 1`, terminator `9`, scratch `12`; out of `startConfig 0 tag
tightWord` (`N = 11`, `zeros = 2`) at step `9 = 2 * 11 - 11 - 2`, terminator `10`, scratch `12`.
Together with the probe above these separate the switch time in both `N` and `zeros`. -/
theorem check_h12_probe_short_widths :
    (machine.run 10 (startConfig 0 tag middleWord)).state.val = 6 ∧
    (machine.run 11 (startConfig 0 tag middleWord)).state.val = 9 ∧
    (machine.run 11 (startConfig 0 tag middleWord)).head.val = 10 ∧
    (machine.run 11 (startConfig 0 tag middleWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 11 (startConfig 0 tag middleWord)).tape ⟨13, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag oneWord)).state.val = 6 ∧
    (machine.run 10 (startConfig 0 tag oneWord)).state.val = 9 ∧
    (machine.run 10 (startConfig 0 tag oneWord)).head.val = 9 ∧
    (machine.run 10 (startConfig 0 tag oneWord)).tape ⟨9, by decide⟩ = some true ∧
    (machine.run 10 (startConfig 0 tag oneWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 8 (startConfig 0 tag tightWord)).state.val = 6 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).state.val = 9 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).head.val = 10 ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag tightWord)).tape ⟨12, by decide⟩ = some true := by
  rw [middle_start 0, one_start 0, tight_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **H12 at width zero, reduced** — the one probe whose incoming dispatcher head is `7` and not
`6`.  Out of `startConfig 0 tag zeroWord` (`N = 10`, `zeros = 0`) the same routed row fires at step
`9 = 2 * 10 - 11 - 0`, restoring the terminator at `8` and leaving the scratch `true` at `11`: the
bootstrap does its whole job at this width too, and hands G3c the same shape of tape.  What G3c
then does with it is its own business, and nothing downstream of the switch is claimed here. -/
theorem check_h12_probe_zero_width :
    (machine.run 8 (startConfig 0 tag zeroWord)).state.val = 6 ∧
    (machine.run 9 (startConfig 0 tag zeroWord)).state.val = 9 ∧
    (machine.run 9 (startConfig 0 tag zeroWord)).head.val = 8 ∧
    (machine.run 9 (startConfig 0 tag zeroWord)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag zeroWord)).tape ⟨11, by decide⟩ = some true := by
  rw [zero_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **The five inherited handoffs, reduced in the composed control.**  Out of the same actual
`startConfig 0 tag physWord`: at steps `50`/`51` G2p-b's `qSeekAnchor` (index `24`) and G2p-c's
start (index `27`) on the anchor cell `7`, with G2p-b's first payload digit already at the target
cell `19` — H13; at steps `77`/`78` G2p-c's `qScanLeft` (index `38`) and G2p-d's marker start
(index `41`) on the anchor cell `7` — H14; at step `88` the marker preamble's `qClearB` (index
`50`) on the outgoing terminator cell `13` and at step `89` the payload loop's `qLoop` (index `55`)
at head `14` — H15; at steps `152`/`153` the loop's `qFin` (index `74`) and G2q's `qStart` (index
`77`) on the tag cell `7` — H16; at steps `170`/`171` G2q's `qBorrow` (index `81`) and the
countdown's `qStart` (index `84`) on the register digit `22`, which that transition clears — H17.
These are G3c's own steps `31`/`32`, `58`/`59`, `69`/`70`, `133`/`134` and `151`/`152`, each shifted
by nine states and by the `19` steps G2p-a takes.  The reduction is bounded at `171` steps and does
not touch the thousand-step drain. -/
theorem check_inherited_handoff_probe :
    (machine.run 50 (startConfig 0 tag physWord)).state.val = 24 ∧
    (machine.run 50 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 51 (startConfig 0 tag physWord)).state.val = 27 ∧
    (machine.run 51 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 51 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 77 (startConfig 0 tag physWord)).state.val = 38 ∧
    (machine.run 78 (startConfig 0 tag physWord)).state.val = 41 ∧
    (machine.run 78 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 78 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 88 (startConfig 0 tag physWord)).state.val = 50 ∧
    (machine.run 88 (startConfig 0 tag physWord)).head.val = 13 ∧
    (machine.run 89 (startConfig 0 tag physWord)).state.val = 55 ∧
    (machine.run 89 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 152 (startConfig 0 tag physWord)).state.val = 74 ∧
    (machine.run 152 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 153 (startConfig 0 tag physWord)).state.val = 77 ∧
    (machine.run 153 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 170 (startConfig 0 tag physWord)).state.val = 81 ∧
    (machine.run 170 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 170 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 171 (startConfig 0 tag physWord)).state.val = 84 ∧
    (machine.run 171 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformed`: the handed-over
configuration is in neither composed verdict; one step later the composed reject — index `94`, not
G2p-a's own `qReject` at index `8` nor G2p-b's at `26` — at the boundary head `11`; and it absorbs.
The routed edge fired in that one transition. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state.val = 94 ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformed)).state.val = 94 := by
  rw [malformed_start 0]
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
