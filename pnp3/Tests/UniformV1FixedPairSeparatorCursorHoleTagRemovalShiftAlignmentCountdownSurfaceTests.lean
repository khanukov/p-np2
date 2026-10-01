import Complexity.Uniform.V1.FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown
namespace Pnp3.Tests.UniformV1FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
open Complexity.Uniform.V1
open PairEncoding
open FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt first_true_strict_first_terminal)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

/-! Infrastructure only. Full propositions below freeze every public contract.
Tiny probes reduce independently; the large execution witness is theorem-derived. -/
theorem check_leftMachine : leftMachine = FixedPairSeparatorCursor.machine := rfl
theorem check_tailMachine : tailMachine = FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine := rfl
theorem check_tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    tailStartConfig B x w = FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w := rfl
theorem check_machine : machine = leftMachine.seq tailMachine := rfl
theorem check_inCursor (q : Fin leftMachine.stateCount) :
    inCursor q = leftMachine.seqLeft tailMachine q := rfl
theorem check_inTail (q : Fin tailMachine.stateCount) :
    inTail q = leftMachine.seqRight tailMachine q := rfl
theorem check_route (q : Fin leftMachine.stateCount) :
    route q = leftMachine.seqRoute tailMachine q := rfl
theorem check_tailStart : tailStart = inTail tailMachine.start := rfl
theorem check_startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    startConfig B x w = leftMachine.seqEmbedRouted tailMachine
      (FixedPairSeparatorCursor.startConfig B (encodePair x w)) := rfl
theorem check_switchTime (a : Nat) : switchTime a = 2 * a + 2 := rfl
theorem check_cursorChainClock (C a m zeros d v : Nat) :
    cursorChainClock C a m zeros d v = switchTime a +
      FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.holeChainClock C a m zeros d v := rfl

theorem check_tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run (switchTime a)
      (FixedPairSeparatorCursor.startConfig B (encodePair x w))
    g = FixedPairSeparatorCursor.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  tail_start_at_first_arrival x w

theorem check_cursor_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < (switchTime a) →
      (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠ leftMachine.accept ∧
      (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠ leftMachine.reject) ∧
    (leftMachine.run (switchTime a) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state =
      leftMachine.accept ∧
    (∀ t, (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠
      leftMachine.reject) :=
  cursor_first_arrival x w

theorem check_suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (switchTime a + s) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailStartConfig B x w)) :=
  suffix x w s

theorem check_table_and_resource_pins :
    machine.stateCount = 201 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 603 ∧
    machine.start.val = 0 ∧ machine.accept.val = 199 ∧
    machine.reject.val = 200 ∧ tailStart.val = 5 ∧
    (∀ q, (inCursor q).val = q.val) ∧
    (∀ q, (inTail q).val = 5 + q.val) ∧
    Function.Injective inCursor ∧ Function.Injective inTail ∧
    (∀ p q, inCursor p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inCursor p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inCursor q) s =
        (route (leftMachine.step q s).1,
          (leftMachine.step q s).2.1,
          (leftMachine.step q s).2.2)) ∧
    (∀ q s,
      machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1,
          (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) :=
  table_and_resource_pins

theorem check_accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q = FixedPairSeparatorCursor.qPeek ∧ ∃ b : Bool, s = some b :=
  accept_rows_unique q s ha

theorem check_reject_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      (q = FixedPairSeparatorCursor.qTag ∨ q = FixedPairSeparatorCursor.qData ∨
        q = FixedPairSeparatorCursor.qPeek) ∧ s = none :=
  reject_rows_unique q s ha hr

theorem check_handoff_exact {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let cR := FixedPairSeparatorCursor.startConfig B (encodePair x w)
    let c := startConfig B x w
    (∀ t, t < (switchTime a) → (machine.run t c).state.val < 5) ∧
    (∀ t, t ≤ (switchTime a) →
      (machine.run t c).state ≠ machine.accept ∧
      (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ (switchTime a) →
      machine.run t c =
        leftMachine.seqEmbedRouted tailMachine (leftMachine.run t cR)) ∧
    machine.run (switchTime a) c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
    (machine.run (switchTime a) c).state.val = 5 ∧
    (machine.run (switchTime a) c).head.val = 2 * a ∧
    (machine.run (switchTime a) c).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (∀ s, machine.run ((switchTime a) + s) c =
      leftMachine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

theorem check_separator_cursor_countdown_drained
    {a m B C zeros v F : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros)
    (hfence : v ≤ F)
    (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros →
      v.testBit (zeros - j) =
        decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let D := cursorChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) :=
  separator_cursor_countdown_drained x w htag hg h hzeros hfence hroom hv hhigh

theorem check_entry_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    pairLength a m = 2 * a + 1 + m ∧
    tapeLength (pairLength a m) B = 2 * a + m + B + 2 ∧
    (startConfig B x w).state.val = 0 ∧
    (startConfig B x w).head.val = 0 ∧
    (startConfig B x w).tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) :=
  entry_pins x w

theorem check_step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s :=
  step_eq_rawStep q s

theorem check_dead_left_verdicts :
    machine.start.val ≠ 3 ∧ machine.start.val ≠ 4 ∧
    (∀ q s, (machine.step q s).1.val ≠ 3 ∧ (machine.step q s).1.val ≠ 4) :=
  dead_left_verdicts

theorem check_left_rows :
    machine.step (inCursor FixedPairSeparatorCursor.qTag) none = (machine.reject, none, .stay) ∧
    machine.step (inCursor FixedPairSeparatorCursor.qTag) (some false) =
      (inCursor FixedPairSeparatorCursor.qData, some false, .right) ∧
    machine.step (inCursor FixedPairSeparatorCursor.qTag) (some true) =
      (inCursor FixedPairSeparatorCursor.qPeek, some true, .right) ∧
    machine.step (inCursor FixedPairSeparatorCursor.qData) none = (machine.reject, none, .stay) ∧
    (∀ b, machine.step (inCursor FixedPairSeparatorCursor.qData) (some b) =
      (inCursor FixedPairSeparatorCursor.qTag, some b, .right)) ∧
    machine.step (inCursor FixedPairSeparatorCursor.qPeek) none = (machine.reject, none, .stay) ∧
    (∀ b, machine.step (inCursor FixedPairSeparatorCursor.qPeek) (some b) = (tailStart, some b, .left)) ∧
    (∀ s, machine.step (inCursor leftMachine.accept) s = (tailStart, s, .stay)) ∧
    (∀ s, machine.step (inCursor leftMachine.reject) s = (machine.reject, s, .stay)) ∧
    machine.step ⟨5, by decide⟩ (some true) = (⟨8, by decide⟩, none, .stay) ∧
    machine.step ⟨9, by decide⟩ none = (⟨17, by decide⟩, none, .stay) :=
  left_rows

theorem check_h2_preterminal_and_no_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    switchTime a - 1 = 2 * a + 1 ∧
    (let c := machine.run (2 * a + 1) (startConfig B x w)
     c.state = inCursor FixedPairSeparatorCursor.qPeek ∧ c.head.val = 2 * a + 1 ∧
     c.tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
     (∃ b : Bool, c.tape c.head = some b ∧ machine.step c.state (c.tape c.head) =
       (tailStart, some b, .left)) ∧ 0 < c.head.val) ∧
    (machine.run (switchTime a) (startConfig B x w)).head.val = 2 * a ∧
    (∀ t, t < switchTime a →
      let c := machine.run t (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.val + 1 < tapeLength (pairLength a m) B) ∧
      ((machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val)) ∧
    (∀ t, t ≤ switchTime a →
      (machine.run t (startConfig B x w)).head.val ≤ 2 * a + 1 ∧
      (machine.run t (startConfig B x w)).tape =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w)) :=
  h2_preterminal_and_no_clamp x w

theorem check_h3_stationary {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime a) (startConfig B x w)
    (machine.step c.state (c.tape c.head)).2.2 = .stay :=
  h3_stationary x w

theorem check_inherited_h3 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a + 1) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w)) ∧
    e.state.val = 8 ∧ e.head.val = 2 * a ∧ e.tape = FixedPairSeparatorHole.holeTape B x w :=
  inherited_h3 x w

theorem check_inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a + (1 + FixedPairTagRemoval.clock a)) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w))) ∧
    e.state.val = 17 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w :=
  inherited_h4 x w

theorem check_inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m)))
      (startConfig B x w)).state.val = 24 ∧
    (let e := machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m)))) (startConfig B x w)
     e.state.val = 50 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3))))))
      (startConfig B x w)).state.val = 54 :=
  inherited_switches x w

theorem check_inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a - 2))) (startConfig B x w)
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left :=
  inherited_origin_clamp x w

theorem check_rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (FixedContentTagGate.tagMatches (Fin.append x w) = true →
      gammaZeros? (Fin.append x w) = none →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).state = machine.reject ∧
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).head.val = a + m ∧
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) ∧
    (FixedContentTagGate.tagMatches (Fin.append x w) = false →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).state = machine.reject ∧
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + s))) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) :=
  rejection_transport x w

theorem check_scanned_reject {N B : Nat} (cL : Config leftMachine.stateCount N B)
    (hstate : cL.state = FixedPairSeparatorCursor.qTag ∨ cL.state = FixedPairSeparatorCursor.qData ∨
      cL.state = FixedPairSeparatorCursor.qPeek)
    (hread : cL.tape cL.head = none) (s : Nat) :
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine cL) =
      ⟨machine.reject, cL.head, cL.tape⟩ :=
  scanned_reject cL hstate hread s

theorem check_malformed_sentinel_reject {N B : Nat} (raw : Bitstring N)
    (hdecode : decodePair raw = none) (hB : 0 < B) (s : Nat) :
    let c := leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig B raw)
    let e := machine.run (N + 2 + s) c
    e.state = machine.reject ∧ e.head.val = N + 1 ∧
    e.tape = FixedPairConcatSentinel.sentinelTape B raw ∧
    e = ⟨machine.reject, ⟨N + 1, by unfold tapeLength; omega⟩,
      FixedPairConcatSentinel.sentinelTape B raw⟩ :=
  malformed_sentinel_reject raw hdecode hB s

theorem check_clock_pins (C a m zeros d v : Nat) :
    switchTime a = FixedPairSeparatorCursor.clock a ∧ switchTime a = 2 * a + 2 ∧
    2 ≤ switchTime a ∧
    cursorChainClock C a m zeros d v = switchTime a +
      FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.holeChainClock C a m zeros d v ∧
    cursorChainClock C a m zeros d v = switchTime a +
      (1 + FixedPairTagRemovalShiftAlignmentCountdown.removalChainClock C a m zeros d v) ∧
    cursorChainClock C a m zeros d v = switchTime a + 1 + FixedPairTagRemoval.clock a +
      FixedPairOriginShiftAlignmentCountdown.switchTime a m +
      FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3) +
      (3 * (a + m) + 7) + (zeros + 1) + (2 * zeros + 5) + C +
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.bootChainClock
        (a + m) zeros d v :=
  clock_pins C a m zeros d v

private def emptyWord : Bitstring 0 := fun i => i.elim0

set_option maxRecDepth 4000000 in
/-- Independent finite reductions, including the complete tapes at each boundary. -/
theorem check_empty_probes : ∀ B : Fin 2,
    List.ofFn (startConfig B.val emptyWord emptyWord).tape =
      [some true, some true] ++ List.replicate B.val none ∧
    (machine.run 1 (startConfig B.val emptyWord emptyWord)).state.val = 2 ∧
    (machine.run 1 (startConfig B.val emptyWord emptyWord)).head.val = 1 ∧
    (machine.run 1 (startConfig B.val emptyWord emptyWord)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair emptyWord emptyWord) ∧
    (machine.run 2 (startConfig B.val emptyWord emptyWord)).state.val = 5 ∧
    (machine.run 2 (startConfig B.val emptyWord emptyWord)).head.val = 0 ∧
    (machine.run 2 (startConfig B.val emptyWord emptyWord)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair emptyWord emptyWord) ∧
    (machine.run 3 (startConfig B.val emptyWord emptyWord)).state.val = 8 ∧
    (machine.run 3 (startConfig B.val emptyWord emptyWord)).head.val = 0 ∧
    (machine.run 3 (startConfig B.val emptyWord emptyWord)).tape = FixedPairSeparatorHole.holeTape B.val emptyWord emptyWord ∧
    (machine.run 5 (startConfig B.val emptyWord emptyWord)).state.val = 17 ∧
    (machine.run 5 (startConfig B.val emptyWord emptyWord)).head.val = 0 ∧
    (machine.run 5 (startConfig B.val emptyWord emptyWord)).tape = FixedPairTagRemoval.compactTape B.val emptyWord emptyWord ∧
    (let c := machine.run 1 (startConfig B.val emptyWord emptyWord)
     0 < c.head.val ∧ (machine.step c.state (c.tape c.head)).2.2 = .left) ∧
    (let c := machine.run 2 (startConfig B.val emptyWord emptyWord)
     (machine.step c.state (c.tape c.head)).2.2 = .stay) := by decide

set_option maxRecDepth 4000000 in
theorem check_singleton_probes : ∀ b c : Bool, ∀ B : Fin 2,
    let x : Bitstring 1 := ![b]
    let w : Bitstring 1 := ![c]
    (machine.run 3 (startConfig B.val x emptyWord)).state.val = 2 ∧
    (machine.run 3 (startConfig B.val x emptyWord)).head.val = 3 ∧
    (machine.run 3 (startConfig B.val x emptyWord)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair x emptyWord) ∧
    (let e := machine.run 3 (startConfig B.val x emptyWord)
     e.tape e.head = some true) ∧
    (machine.run 4 (startConfig B.val x emptyWord)).state.val = 5 ∧
    (machine.run 4 (startConfig B.val x emptyWord)).head.val = 2 ∧
    (machine.run 4 (startConfig B.val x emptyWord)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair x emptyWord) ∧
    (machine.run 5 (startConfig B.val x emptyWord)).state.val = 8 ∧
    (machine.run 5 (startConfig B.val x emptyWord)).head.val = 2 ∧
    (machine.run 5 (startConfig B.val x emptyWord)).tape = FixedPairSeparatorHole.holeTape B.val x emptyWord ∧
    (machine.run 13 (startConfig B.val x emptyWord)).state.val = 17 ∧
    (machine.run 13 (startConfig B.val x emptyWord)).head.val = 0 ∧
    (machine.run 13 (startConfig B.val x emptyWord)).tape = FixedPairTagRemoval.compactTape B.val x emptyWord ∧
    (machine.run 3 (startConfig B.val x w)).state.val = 2 ∧
    (machine.run 3 (startConfig B.val x w)).head.val = 3 ∧
    (machine.run 3 (startConfig B.val x w)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair x w) ∧
    (let e := machine.run 3 (startConfig B.val x w)
     e.tape e.head = some c) ∧
    (machine.run 4 (startConfig B.val x w)).state.val = 5 ∧
    (machine.run 4 (startConfig B.val x w)).head.val = 2 ∧
    (machine.run 4 (startConfig B.val x w)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair x w) ∧
    (machine.run 5 (startConfig B.val x w)).state.val = 8 ∧
    (machine.run 5 (startConfig B.val x w)).head.val = 2 ∧
    (machine.run 5 (startConfig B.val x w)).tape = FixedPairSeparatorHole.holeTape B.val x w ∧
    (machine.run 13 (startConfig B.val x w)).state.val = 17 ∧
    (machine.run 13 (startConfig B.val x w)).head.val = 0 ∧
    (machine.run 13 (startConfig B.val x w)).tape = FixedPairTagRemoval.compactTape B.val x w ∧
    (machine.run 1 (startConfig B.val emptyWord w)).state.val = 2 ∧
    (machine.run 1 (startConfig B.val emptyWord w)).head.val = 1 ∧
    (machine.run 1 (startConfig B.val emptyWord w)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair emptyWord w) ∧
    (let e := machine.run 1 (startConfig B.val emptyWord w)
     e.tape e.head = some c) ∧
    (machine.run 2 (startConfig B.val emptyWord w)).state.val = 5 ∧
    (machine.run 2 (startConfig B.val emptyWord w)).head.val = 0 ∧
    (machine.run 2 (startConfig B.val emptyWord w)).tape = FixedPairConcatSentinel.sentinelTape B.val (encodePair emptyWord w) ∧
    (machine.run 3 (startConfig B.val emptyWord w)).state.val = 8 ∧
    (machine.run 3 (startConfig B.val emptyWord w)).head.val = 0 ∧
    (machine.run 3 (startConfig B.val emptyWord w)).tape = FixedPairSeparatorHole.holeTape B.val emptyWord w ∧
    (machine.run 5 (startConfig B.val emptyWord w)).state.val = 17 ∧
    (machine.run 5 (startConfig B.val emptyWord w)).head.val = 0 ∧
    (machine.run 5 (startConfig B.val emptyWord w)).tape = FixedPairTagRemoval.compactTape B.val emptyWord w := by
  intro b c B
  cases b <;> cases c <;> fin_cases B <;> (dsimp only; repeat' apply And.intro) <;> decide

private def blankConfig (q : Fin 3) : Config leftMachine.stateCount 1 0 :=
  ⟨⟨q.val, by change q.val < 5; omega⟩, ⟨1, by decide⟩, ![some true, none]⟩

set_option maxRecDepth 4000000 in
theorem check_blank_reject_probes :
    (∀ q : Fin 3, let c := blankConfig q
     let e := machine.run 1 (leftMachine.seqEmbedRouted tailMachine c)
     e.state.val = 200 ∧ e.head = c.head ∧ e.tape = c.tape) ∧
    (let c : Config leftMachine.stateCount 1 0 :=
       ⟨FixedPairSeparatorCursor.qPeek, ⟨1, by decide⟩, ![some true, some false]⟩
     let e := machine.run 1 (leftMachine.seqEmbedRouted tailMachine c)
     e.state.val = 5 ∧ e.head.val = 0 ∧ e.tape = c.tape) := by decide

theorem check_blank_reject_persistence (q : Fin 3) (s : Nat) :
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine (blankConfig q)) =
      ⟨machine.reject, (blankConfig q).head, (blankConfig q).tape⟩ := by
  apply scanned_reject _ _ rfl
  fin_cases q <;> decide

set_option maxRecDepth 4000000 in
theorem check_malformed_sentinel_probes :
    (decodePair emptyWord = none ∧ decodePair (![false] : Bitstring 1) = none ∧
      decodePair (![false, false] : Bitstring 2) = none) ∧
    (∀ k : Fin 3, let raw : Bitstring k.val := fun _ => false
     let c := leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig 1 raw)
     (machine.run (k.val + 2) c).state.val = 200 ∧
     (machine.run (k.val + 2) c).head.val = k.val + 1 ∧
     (machine.run (k.val + 2) c).tape = FixedPairConcatSentinel.sentinelTape 1 raw) ∧
    (∀ k : Fin 3, ∀ s, let raw : Bitstring k.val := fun _ => false
     machine.run (k.val + 2 + s)
       (leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig 1 raw)) =
       ⟨machine.reject, ⟨k.val + 1, by unfold tapeLength; omega⟩,
         FixedPairConcatSentinel.sentinelTape 1 raw⟩) := by
  refine ⟨by decide, by decide, ?_⟩
  intro k s
  exact (malformed_sentinel_reject (fun _ => false)
    (by fin_cases k <;> decide) (by omega) s).2.2.2

set_option maxRecDepth 4000000 in
theorem check_zero_padding_counterexample :
    let c := leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig 0 emptyWord)
    List.ofFn c.tape = [some true] ∧
    (machine.step c.state (c.tape c.head)).2.2 = .right ∧
    (machine.run 1 c).state.val = 2 ∧ (machine.run 1 c).head.val = 0 ∧
    (machine.run 2 c).state.val = 5 ∧ (machine.run 2 c).head.val = 0 ∧
    (machine.run 2 c).tape = c.tape ∧ (machine.run 2 c).state ≠ machine.reject := by decide

set_option maxRecDepth 4000000 in
theorem check_raw_entry_counterexample :
    let raw := initialConfig machine 0 (encodePair emptyWord emptyWord)
    let localEntry := startConfig 0 emptyWord emptyWord
    List.ofFn raw.tape = [some true, none] ∧ List.ofFn localEntry.tape = [some true, some true] ∧
    raw.state = localEntry.state ∧ raw.head = localEntry.head ∧
    (machine.run 2 raw).state.val = 200 ∧ (machine.run 2 raw).head.val = 1 ∧
    (machine.run 2 localEntry).state.val = 5 ∧ (machine.run 2 localEntry).head.val = 0 := by decide

theorem check_inherited_clock_values : switchTime 8 = 18 ∧
    FixedPairTagRemoval.clock 8 = 106 ∧
    FixedPairOriginShiftAlignmentCountdown.switchTime 8 9 = 64 ∧
    FixedPairOriginShiftAlignmentCountdown.tailSwitchTime 8 9 = 1590 ∧
    cursorChainClock 18 8 9 4 0 24 = 2991 ∧ (2991 : Nat) = 18 + 2973 ∧ (22 : Nat) < 2991 := by decide

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 := ![false, false, false, false, true, true, false, false, true]

set_option maxRecDepth 40000 in
theorem check_inherited_endpoint_probes :
    (machine.run 18 (startConfig 22 tag physWord)).state.val = 5 ∧
    (machine.run 19 (startConfig 22 tag physWord)).state.val = 8 ∧
    (let e := machine.run 123 (startConfig 22 tag physWord)
     e.head.val = 0 ∧ (machine.step e.state (e.tape e.head)).2.2 = .left) ∧
    (machine.run 125 (startConfig 22 tag physWord)).state.val = 17 ∧
    (machine.run 189 (startConfig 22 tag physWord)).state.val = 24 ∧
    (let e := machine.run 1779 (startConfig 22 tag physWord)
     e.state.val = 50 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape 22 tag physWord) ∧
    (machine.run 1799 (startConfig 22 tag physWord)).state.val = 54 :=
  ⟨(handoff_exact tag physWord).2.2.2.2.1, (inherited_h3 tag physWord).2.1,
    inherited_origin_clamp tag physWord, (inherited_h4 tag physWord).2.1,
    inherited_switches tag physWord⟩

theorem check_witness_layout :
    tapeLength (pairLength 8 9) 22 = 49 ∧ borrow tag physWord 4 = 0 ∧
    (∀ i : Fin 49, 18 ≤ i.val → i.val ≤ 22 → loopTape 22 tag physWord 4 0 24 i = some false) ∧
    loopTape 22 tag physWord 4 0 24 ⟨23, by decide⟩ = none ∧
    (∀ i : Fin 49, 24 ≤ i.val → i.val ≤ 47 → loopTape 22 tag physWord 4 0 24 i = some true) ∧
    loopTape 22 tag physWord 4 0 24 ⟨48, by decide⟩ = none ∧
    List.ofFn (loopTape 22 tag physWord 4 0 24) =
      [true, false, true, true, false, false, true, false, false, false, false, false].map some ++
        List.replicate 4 none ++ [some true, none] ++ List.replicate 5 (some false) ++
        [none] ++ List.replicate 24 (some true) ++ [none] := by
  decide

set_option maxRecDepth 40000 in
/-- Derived execution nonvacuity with hand-supplied v = 24; all eight premises discharged.
This is neither ContentAccepts nonvacuity nor first arrival of composed accept. -/
theorem check_drained_literal_endpoint :
    let e := machine.run 2991 (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.state.val = 199 ∧ e.head.val = 23 ∧
      e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, 2991 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  have hc : cursorChainClock (3 * 4 + 6) 8 9 4 0 24 = 2991 := rfl
  obtain ⟨h1, h2, h3, h4⟩ :=
    separator_cursor_countdown_drained
      (q := FixedGammaPayloadDispatcher.qHasOne)
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

/-- Inherited deadlines and every later endpoint; these are not first-rejection claims. -/
theorem check_rejection_endpoint_probes :
    (∀ s, let e := machine.run (27 + s) (startConfig 0 emptyWord emptyWord)
     e.state = machine.reject ∧ e.state.val = 200 ∧ e.head.val = 0 ∧
     e.head = (FixedContentTagGate.finalConfig 0 emptyWord emptyWord).head ∧
     e.tape = FixedPairContentMarkerErase.contentTape 0 emptyWord emptyWord) ∧
    (∀ s, let e := machine.run (1012 + s) (startConfig 0 tag emptyWord)
     e.state = machine.reject ∧ e.state.val = 200 ∧ e.head.val = 8 ∧
     e.tape = FixedPairContentMarkerErase.contentTape 0 tag emptyWord) := by
  constructor
  · intro s
    obtain ⟨hq, hh, ht⟩ := (rejection_transport (B := 0) emptyWord emptyWord).2
      (by decide) (22 + s) (by change 22 ≤ 22 + s; omega)
    have he : switchTime 0 + (1 + (FixedPairTagRemoval.clock 0 + (22 + s))) = 27 + s := by
      change 2 + (1 + (2 + (22 + s))) = 27 + s; omega
    rw [he] at hq hh ht
    refine ⟨hq, ?_, ?_, hh, ht⟩
    · rw [hq]; rfl
    · rw [hh]; rfl
  · intro s
    obtain ⟨hq, hh, ht⟩ := (rejection_transport (B := 0) tag emptyWord).1
      (by decide) (by decide) (887 + s) (by change 887 ≤ 887 + s; omega)
    have he : switchTime 8 + (1 + (FixedPairTagRemoval.clock 8 + (887 + s))) = 1012 + s := by
      change 18 + (1 + (106 + (887 + s))) = 1012 + s; omega
    rw [he] at hq hh ht
    refine ⟨hq, ?_, hh, ht⟩
    rw [hq]; rfl


/-! Explicit type-check surfaces, in addition to the full proposition mirrors. -/
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailStartConfig
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inCursor
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inTail
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.route
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailStart
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursorChainClock
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tail_start_at_first_arrival
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursor_first_arrival
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.suffix
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.table_and_resource_pins
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.accept_rows_unique
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.reject_rows_unique
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.separator_cursor_countdown_drained
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.entry_pins
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.step_eq_rawStep
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.dead_left_verdicts
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.left_rows
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.h2_preterminal_and_no_clamp
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.h3_stationary
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h3
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h4
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_switches
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_origin_clamp
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.rejection_transport
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.scanned_reject
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.malformed_sentinel_reject
#check FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.clock_pins

end Pnp3.Tests.UniformV1FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
