import
  Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
Surface pins for the Part A G3g concrete slice: G2k's payload dispatcher with `qHasOne` merged into
its accept `qAllZero`, then G3e's whole composite, as **one** closed 123-state, 369-row table.  Its
newly executed handoff H11 has **six** live routed rows into G3e's start `tailStart` at index `28`:
`qCursorBackFirst` (`1`), `qCursorFillOne` (`8`) and `qCursorFillVirtual` (`9`) on the blank,
`qZeroFillCounter` (`19`), `qPendingFillOne` (`23`) and `qPendingFillVirtual` (`24`) on `true`; `8`
and `23` targeted `qHasOne` before the merge.  H12 (`34 → 37`) to H17 (`109 → 112`) are inherited
from G3e.  Every public declaration is restated in full.

The probes.  The eight words are G3f's (tag `10110010`): `malformedWord` has no gamma terminator;
`zeroWord` decodes to `zeros = 0`, `oneWord` to `zeros = 1` with an exhausted payload, `middleWord`
and `physWord` to `zeros = 2` and `zeros = 4` with a physical `true` at the first payload cell,
`tightWord` to `zeros = 2` with a virtual one, and `pendTrueWord` and `pendVirtWord` to `zeros = 2`
with `false` then `true`, respectively a virtual cell.  The seven well-formed words reach H11
through all six routed rows at switch times `2`, `16`, `12`, `18`, `12`, `23`, `23`; `physWord`,
`middleWord` and `pendTrueWord` take the two rows the merge retargeted.  The `check_*_literal*`
theorems are **derived** from the slice's theorems and G3f's path theorems, whose hypotheses they
discharge inline at the literals; the drain runs at `B = 22`, where `4 + 2 + 24 = 8 + 22` meets the
lane budget exactly, with the register value `24 > N` supplied **by hand** (an execution fixture,
no accepted-content fixture).  The independent `probe_start` identifies the composed `startConfig`
with an explicit configuration built from G2a's landed `run_deadline` equality alone.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and none of the ten earlier handoffs is executed or pinned; nothing reads the merged verdict
back; no first arrival of the composed accept, fence, converse, footprint theorem or pnp4 bridge;
and no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/
namespace
  Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open
  Complexity.Uniform.V1.FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaPayloadDispatcher (qCursorStart qCursorBackFirst
  qCursorFillOne qCursorFillVirtual qZeroFillCounter qPendingFillOne qPendingFillVirtual qAllZero
  qHasOne qReject retagG2a)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline (deadline)
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds (pendingEndClock zeroEndClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)

def check_mergedDispatcher : UniformTM := mergedDispatcher
def check_machine : UniformTM := machine
def check_inDispatcher :
    Fin FixedGammaPayloadDispatcher.stateCount → Fin machine.stateCount := inDispatcher
def check_inTail :
    Fin
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.stateCount →
      Fin machine.stateCount := inTail
def check_route : Fin FixedGammaPayloadDispatcher.stateCount → Fin machine.stateCount := route
def check_tailStart : Fin machine.stateCount := tailStart
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_dispatcherChainClock (C N zeros d v : Nat) : Nat := dispatcherChainClock C N zeros d v

set_option maxRecDepth 40000 in
/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 123 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 369 ∧
      mergedDispatcher.start = qCursorStart ∧ mergedDispatcher.accept = qAllZero ∧
      mergedDispatcher.reject = qReject ∧
      machine.start = route qCursorStart ∧ machine.start = inDispatcher qCursorStart ∧
      machine.accept =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.accept ∧
      machine.reject =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 121 ∧ machine.reject.val = 122 ∧
      (∀ q, (inDispatcher q).val = q.val) ∧ (∀ q, (inDispatcher q).val < 28) ∧
      (∀ q, (inTail q).val = 28 + q.val) ∧ (∀ q, 28 ≤ (inTail q).val) ∧
      Function.Injective inDispatcher ∧ Function.Injective inTail ∧
      (∀ p q, inDispatcher p ≠ inTail q) ∧
      tailStart =
        inTail
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.start ∧
      tailStart.val = 28 ∧ route qAllZero = tailStart ∧ route qReject = machine.reject ∧
      (∀ q, q ≠ qAllZero → q ≠ qReject → route q = inDispatcher q) ∧
      (∀ q s, mergedDispatcher.step q s =
        (FixedGammaPayloadDispatcher.machine.mergeState qHasOne
            (FixedGammaPayloadDispatcher.machine.step q s).1,
          (FixedGammaPayloadDispatcher.machine.step q s).2.1,
          (FixedGammaPayloadDispatcher.machine.step q s).2.2)) ∧
      (∀ q s, (mergedDispatcher.step q s).1 ≠ qHasOne) ∧
      mergedDispatcher.step qCursorFillOne none = (qAllZero, some false, .left) ∧
      mergedDispatcher.step qPendingFillOne (some true) = (qAllZero, some true, .stay) ∧
      (∀ q s, machine.step (inDispatcher q) s =
        (route (mergedDispatcher.step q s).1, (mergedDispatcher.step q s).2.1,
          (mergedDispatcher.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail
            (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
              q s).1,
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.1,
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.step
            q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inDispatcher qCursorBackFirst) none = (tailStart, some false, .stay) ∧
      machine.step (inDispatcher qCursorFillOne) none = (tailStart, some false, .left) ∧
      machine.step (inDispatcher qCursorFillVirtual) none = (tailStart, some false, .left) ∧
      machine.step (inDispatcher qZeroFillCounter) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qPendingFillOne) (some true) = (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qPendingFillVirtual) (some true) =
        (tailStart, some true, .stay) ∧
      machine.step (inDispatcher qCursorStart) none = (machine.reject, none, .stay) :=
  table_and_resource_pins

/-- The start, restated in full. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaPayloadDispatcher.startConfig B x w
    let c := startConfig B x w
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The chained clock, restated in full. -/
theorem check_clock_pins (C N zeros d v : Nat) :
    dispatcherChainClock C N zeros d v = C + bootChainClock N zeros d v ∧
      (2 ≤ zeros → dispatcherChainClock C N zeros d v =
        C + (2 * N - 11 - zeros + (2 * N + zeros - 6 +
          (2 * N - 7 + (zeros + 7 + (totalClock N zeros + composedClock N zeros d v)))))) :=
  clock_pins C N zeros d v

/-- Uniqueness of the strict first arrival, restated in full. -/
theorem check_strictFirstTerminalAt_unique {a m B C C' : Nat}
    {q q' : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (h : StrictFirstTerminalAt B x w C q) (h' : StrictFirstTerminalAt B x w C' q') :
    C = C' ∧ q = q' :=
  strictFirstTerminalAt_unique x w h h'

/-- The two side premises of the handoff, restated in full. -/
theorem check_side_premises_of_strictFirstTerminalAt {a m B C zeros : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q) : C ≤ deadline (a + m) ∧ q ≠ qReject :=
  side_premises_of_strictFirstTerminalAt x w htag hg h

/-- The executed handoff H11 at the dispatcher's first arrival, restated in full. -/
theorem check_handoff_of_first_terminal {a m B C : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (h : StrictFirstTerminalAt B x w C q) (hq : q ≠ qReject) (hle : C ≤ deadline (a + m)) :
    let c := startConfig B x w
    (∀ t, t < C →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ C → machine.run t c =
        mergedDispatcher.seqEmbedRouted
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaPayloadDispatcher.machine.mergeConfig qHasOne
            (FixedGammaPayloadDispatcher.machine.run t
              (FixedGammaPayloadDispatcher.startConfig B x w)))) ∧
      machine.run C c =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) ∧
      (∀ s, machine.run (C + s) c =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run
            s
            (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
              B x w))) :=
  handoff_of_first_terminal x w h hq hle

/-- The semantic content of the switch, restated in full. -/
theorem check_handoff_endpoint_pins {a m B C zeros : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q) :
    let e := machine.run C (startConfig B x w)
    let p := FixedGammaTerminatorScratchBootstrap.startConfig B x w
    (q = qAllZero ∨ q = qHasOne) ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (zeros = 0 → e.head.val = 7) ∧ (0 < zeros → e.head.val = 6) :=
  handoff_endpoint_pins x w htag hg h

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let K := dispatcherChainClock C (a + m) zeros d v
    let e := machine.run K (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, K ≤ t → machine.run t (startConfig B x w) = e) :=
  dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh

/-- The existential handoff, restated in full. -/
theorem check_tagged_handoff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    ∃ C q, C ≤ deadline (a + m) ∧ StrictFirstTerminalAt B x w C q ∧
      (q = qAllZero ∨ q = qHasOne) ∧
      machine.run C (startConfig B x w) =
        mergedDispatcher.seqEmbedRight
          FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
          (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
            B x w) :=
  tagged_handoff x w htag hg

/-- The routed reject, restated in full. -/
theorem check_malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let e := machine.run s (startConfig B x w)
    e.state = machine.reject ∧ e.head.val = a + m ∧
      e.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_reject_handoff x w htag hg s hs

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    3 * 4 + 6 = 18 ∧ zeroEndClock 1 = 16 ∧ pendingEndClock 2 1 = 23 ∧ 18 ≤ deadline 17 ∧
      16 ≤ deadline 11 ∧ 2 ≤ deadline 10 ∧ bootChainClock 17 4 0 24 = 1098 ∧
      dispatcherChainClock 18 17 4 0 24 = 1116 :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, rfl, rfl⟩

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

/-- H11 through both success endpoints, **derived**: no composed verdict before the switch, and at
the switch — `18` on `physWord` (`qHasOne`, retargeted row `8`) and `16` on `oneWord` (`qAllZero`,
row `19`) — G3e's actual `startConfig 0 tag ·`, re-embedded; and, from `handoff_endpoint_pins`,
head `6` on the unchanged `contentTape` at `physWord` and head `7` at width zero (`zeroWord`). -/
theorem check_handoff_literal :
    (∀ t, t < 18 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 18 (startConfig 0 tag physWord) =
      mergedDispatcher.seqEmbedRight
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag physWord) ∧
    (∀ t, t < 16 → (machine.run t (startConfig 0 tag oneWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag oneWord)).state ≠ machine.reject) ∧
    machine.run 16 (startConfig 0 tag oneWord) =
      mergedDispatcher.seqEmbedRight
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
          0 tag oneWord) ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 6 ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag physWord ∧
    (machine.run 2 (startConfig 0 tag zeroWord)).head.val = 7 := by
  have hphys := first_true_strict_first_terminal (B := 0) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by decide) (by decide)
  obtain ⟨h1, -, h2, -⟩ := handoff_of_first_terminal tag physWord hphys.1 (by decide) (by decide)
  obtain ⟨h3, -, h4, -⟩ := handoff_of_first_terminal (B := 0) tag oneWord
    (exhausted_strict_first_terminal (zeros := 1) tag oneWord (by decide) (by decide) (by omega)
      (by
        intro j hj0 hj1
        obtain rfl : j = 10 := by omega
        decide)).1 (by decide) (by decide)
  obtain ⟨-, -, -, h5, -, h6⟩ :=
    handoff_endpoint_pins (zeros := 4) tag physWord (by decide) (by decide) hphys.1
  obtain ⟨-, -, -, -, h7, -⟩ := handoff_endpoint_pins (B := 0) (zeros := 0) tag zeroWord
    (by decide) (by decide) (zero_width_strict_first_terminal tag zeroWord (by decide) (by decide)).1
  exact ⟨h1, h2, h3, h4, h6 (by omega), h5, h7 rfl⟩

/-- The composed endpoint at the physical fixture, derived: the composed accept on the separator
blank `23` after exactly `1116` steps — `18` for the dispatcher, none for H11, then G3e's `1098` —
persisting.  Nothing decodes the hand-written `24`. -/
theorem check_drained_literal_endpoint :
    let e := machine.run (dispatcherChainClock 18 (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, dispatcherChainClock 18 (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
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

/-- The routed reject at the malformed fixture, derived: the composed reject at steps `1` and `5`
on the boundary head `11` over the unchanged content tape. -/
theorem check_malformed_literal :
    (machine.run 1 (startConfig 0 tag malformedWord)).state = machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 8 + 3 ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).tape =
      FixedPairContentMarkerErase.contentTape 0 tag malformedWord ∧
    (machine.run 5 (startConfig 0 tag malformedWord)).state = machine.reject := by
  obtain ⟨h1, h2, h3⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide) 1 le_rfl
  obtain ⟨h4, -, -⟩ :=
    malformed_reject_handoff (B := 0) tag malformedWord (by decide) (by decide) 5 (by omega)
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probes -/

/-- The composed `startConfig B tag ·` is G2a's landed `finalConfig`, retagged, merged and routed.
The proved `run_deadline` equality identifies the anchor endpoint; it executes nothing here. -/
private theorem probe_start {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    startConfig B x w =
      mergedDispatcher.seqEmbedRouted
        FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
        (FixedGammaPayloadDispatcher.machine.mergeConfig qHasOne
          (retagG2a (FixedContentGammaAnchor.finalConfig B x w))) := by
  unfold startConfig
  rw [FixedGammaPayloadDispatcher.startConfig, FixedContentGammaAnchor.run_deadline x w htag]

set_option maxRecDepth 100000 in
/-- **H11 through all six routed rows, reduced.**  One step before each switch the control is in
the dispatcher state owning the row — `8` on `physWord` and `middleWord`, `23` on `pendTrueWord`,
`9` on `tightWord`, `19` on `oneWord`, `24` on `pendVirtWord`, `1` on `zeroWord` — and at the
switch in G3e's start `28` on head `6`, or `7` at width zero.  No slice theorem is used. -/
theorem check_h11_probe_reductions :
    (machine.run 17 (startConfig 0 tag physWord)).state.val = 8 ∧
    (machine.run 18 (startConfig 0 tag physWord)).state.val = 28 ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 6 ∧
    (machine.run 11 (startConfig 0 tag middleWord)).state.val = 8 ∧
    (machine.run 12 (startConfig 0 tag middleWord)).state.val = 28 ∧
    (machine.run 12 (startConfig 0 tag middleWord)).head.val = 6 ∧
    (machine.run 22 (startConfig 0 tag pendTrueWord)).state.val = 23 ∧
    (machine.run 23 (startConfig 0 tag pendTrueWord)).state.val = 28 ∧
    (machine.run 23 (startConfig 0 tag pendTrueWord)).head.val = 6 ∧
    (machine.run 11 (startConfig 0 tag tightWord)).state.val = 9 ∧
    (machine.run 12 (startConfig 0 tag tightWord)).state.val = 28 ∧
    (machine.run 12 (startConfig 0 tag tightWord)).head.val = 6 ∧
    (machine.run 15 (startConfig 0 tag oneWord)).state.val = 19 ∧
    (machine.run 16 (startConfig 0 tag oneWord)).state.val = 28 ∧
    (machine.run 16 (startConfig 0 tag oneWord)).head.val = 6 ∧
    (machine.run 22 (startConfig 0 tag pendVirtWord)).state.val = 24 ∧
    (machine.run 23 (startConfig 0 tag pendVirtWord)).state.val = 28 ∧
    (machine.run 23 (startConfig 0 tag pendVirtWord)).head.val = 6 ∧
    (machine.run 1 (startConfig 0 tag zeroWord)).state.val = 1 ∧
    (machine.run 2 (startConfig 0 tag zeroWord)).state.val = 28 ∧
    (machine.run 2 (startConfig 0 tag zeroWord)).head.val = 7 := by
  rw [probe_start 0 tag physWord (by decide), probe_start 0 tag middleWord (by decide),
    probe_start 0 tag pendTrueWord (by decide), probe_start 0 tag tightWord (by decide),
    probe_start 0 tag oneWord (by decide), probe_start 0 tag pendVirtWord (by decide),
    probe_start 0 tag zeroWord (by decide)]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- **Two inherited handoffs, reduced.**  Out of `startConfig 0 tag physWord`: H12 at steps
`36`/`37` (`34` then `37` on the restored terminator cell `12`, G2p-a's scratch `true` at `18`) and
H13 at `68`/`69` (`52` then `55` on the anchor cell `7`) — G3e's own steps `18`/`19` and `50`/`51`,
shifted by twenty-eight states and by the `18` steps the dispatcher takes. -/
theorem check_inherited_handoff_probe :
    (machine.run 36 (startConfig 0 tag physWord)).state.val = 34 ∧
    (machine.run 37 (startConfig 0 tag physWord)).state.val = 37 ∧
    (machine.run 37 (startConfig 0 tag physWord)).head.val = 12 ∧
    (machine.run 37 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 37 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 68 (startConfig 0 tag physWord)).state.val = 52 ∧
    (machine.run 69 (startConfig 0 tag physWord)).state.val = 55 ∧
    (machine.run 69 (startConfig 0 tag physWord)).head.val = 7 := by
  rw [probe_start 0 tag physWord (by decide)]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The routed reject, reduced.**  Out of `startConfig 0 tag malformedWord`: the start is in
neither composed verdict, on the boundary head `11`; one step later the composed reject — index
`122`, not G2k's own `qReject` at `27` — on that head; and it absorbs. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformedWord)).state ≠ machine.accept ∧
    (machine.run 0 (startConfig 0 tag malformedWord)).state ≠ machine.reject ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).state.val = 122 ∧
    (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformedWord)).state.val = 122 := by
  rw [probe_start 0 tag malformedWord (by decide)]
  repeat' apply And.intro
  all_goals decide

end
  Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownSurfaceTests
