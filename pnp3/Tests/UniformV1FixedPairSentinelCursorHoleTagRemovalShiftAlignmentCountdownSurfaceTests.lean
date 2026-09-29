import Complexity.Uniform.V1.FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown
namespace Pnp3.Tests.UniformV1FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
open Complexity.Uniform.V1
open PairEncoding
open FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt first_true_strict_first_terminal)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
set_option maxRecDepth 40000

/-! Infrastructure. Every public API has a named full-proposition mirror.
Small runs reduce independently; the closed drain uses the executed raw theorem. -/
theorem check_leftMachine : leftMachine = FixedPairConcatSentinel.machine := rfl
theorem check_tailMachine : tailMachine = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine := rfl
theorem check_machine : machine = leftMachine.seq tailMachine := rfl
theorem check_inSentinel (q : Fin leftMachine.stateCount) :
    inSentinel q = leftMachine.seqLeft tailMachine q := rfl
theorem check_inTail (q : Fin tailMachine.stateCount) :
    inTail q = leftMachine.seqRight tailMachine q := rfl
theorem check_route (q : Fin leftMachine.stateCount) :
    route q = leftMachine.seqRoute tailMachine q := rfl
theorem check_tailStart : tailStart = inTail tailMachine.start := rfl
theorem check_tailRawStart {R : Nat} (B : Nat) (raw : Bitstring R) :
    tailRawStart B raw = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRouted FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairSeparatorCursor.startConfig B raw) := rfl
theorem check_switchTime (R : Nat) : switchTime R = FixedPairConcatSentinel.clock R := rfl
theorem check_rawChainClock (C a m zeros d v : Nat) :
    rawChainClock C a m zeros d v = switchTime (pairLength a m) +
      FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursorChainClock C a m zeros d v := rfl

theorem check_entry_pins {R a m B : Nat} (raw : Bitstring R) (x : Bitstring a) (w : Bitstring m) :
    tailRawStart B raw = ⟨tailMachine.start, ⟨0, by simp [tapeLength]⟩,
      FixedPairConcatSentinel.sentinelTape B raw⟩ ∧
    tailRawStart B (encodePair x w) = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w ∧
    (initialConfig machine B raw).tape ⟨R, by unfold tapeLength; omega⟩ = none ∧
    (tailRawStart B raw).tape ⟨R, by unfold tapeLength; omega⟩ = some true :=
  entry_pins raw x w

theorem check_tail_start_at_first_arrival {R B : Nat} (raw : Bitstring R) :
    let g := leftMachine.run (switchTime R) (initialConfig leftMachine B raw)
    g = FixedPairConcatSentinel.sentinelConfig B raw ∧
    tailRawStart B raw = ⟨tailMachine.start, g.head, g.tape⟩ :=
  tail_start_at_first_arrival raw

theorem check_sentinel_first_arrival {R B : Nat} (raw : Bitstring R) :
    (∀ t, t < switchTime R →
      (leftMachine.run t (initialConfig leftMachine B raw)).state ≠ leftMachine.accept ∧
      (leftMachine.run t (initialConfig leftMachine B raw)).state ≠ leftMachine.reject) ∧
    (leftMachine.run (switchTime R) (initialConfig leftMachine B raw)).state = leftMachine.accept :=
  sentinel_first_arrival raw

theorem check_raw_suffix {R B : Nat} (raw : Bitstring R) (s : Nat) :
    machine.run (switchTime R + s) (initialConfig machine B raw) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailRawStart B raw)) :=
  raw_suffix raw s

theorem check_handoff_exact {R B : Nat} (raw : Bitstring R) :
    let c := initialConfig machine B raw
    (∀ t, t < switchTime R → (machine.run t c).state.val < 5) ∧
    (∀ t, t ≤ switchTime R →
      (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ switchTime R → machine.run t c =
      leftMachine.seqEmbedRouted tailMachine (leftMachine.run t (initialConfig leftMachine B raw))) ∧
    machine.run (switchTime R) c = leftMachine.seqEmbedRight tailMachine (tailRawStart B raw) ∧
    (machine.run (switchTime R) c).state = tailStart ∧
    (machine.run (switchTime R) c).state.val = 7 ∧
    (machine.run (switchTime R) c).head = ⟨0, by simp [tapeLength]⟩ ∧
    (machine.run (switchTime R) c).tape = FixedPairConcatSentinel.sentinelTape B raw ∧
    (∀ s, machine.run (switchTime R + s) c =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailRawStart B raw))) :=
  handoff_exact raw

theorem check_table_and_resource_pins :
    machine.stateCount = 208 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 624 ∧
    machine.start.val = 0 ∧ machine.accept.val = 206 ∧
    machine.reject.val = 207 ∧ tailStart.val = 7 ∧
    (∀ q, (inSentinel q).val = q.val) ∧
    (∀ q, (inTail q).val = 7 + q.val) ∧
    Function.Injective inSentinel ∧ Function.Injective inTail ∧
    (∀ p q, inSentinel p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inSentinel p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inSentinel q) s =
        (route (leftMachine.step q s).1,
          (leftMachine.step q s).2.1,
          (leftMachine.step q s).2.2)) ∧
    (∀ q s,
      machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1,
          (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) :=
  table_and_resource_pins

theorem check_step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s := step_eq_rawStep q s

theorem check_dead_left_verdicts :
    machine.start.val ≠ 5 ∧ machine.start.val ≠ 6 ∧
    (∀ q s, (machine.step q s).1.val ≠ 5 ∧ (machine.step q s).1.val ≠ 6) :=
  dead_left_verdicts

theorem check_accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      (q = FixedPairConcatSentinel.qStart ∨ q = FixedPairConcatSentinel.qBackF ∨ q = FixedPairConcatSentinel.qBackT) ∧ s = none :=
  accept_rows_unique q s ha hr

theorem check_reject_rows_absent (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 ≠ leftMachine.reject :=
  reject_rows_absent q s ha hr

theorem check_left_rows :
    machine.step (inSentinel FixedPairConcatSentinel.qStart) none = (tailStart, some true, .stay) ∧
    machine.step (inSentinel FixedPairConcatSentinel.qBackF) none = (tailStart, some false, .stay) ∧
    machine.step (inSentinel FixedPairConcatSentinel.qBackT) none = (tailStart, some true, .stay) ∧
    (∀ s, machine.step (inSentinel leftMachine.accept) s = (tailStart, s, .stay)) ∧
    (∀ s, machine.step (inSentinel leftMachine.reject) s = (machine.reject, s, .stay)) :=
  left_rows

theorem check_h1_no_clamp {R B : Nat} (raw : Bitstring R) (t : Nat) (ht : t < switchTime R) :
    let c := machine.run t (initialConfig machine B raw)
    ((machine.step c.state (c.tape c.head)).2.2 = .right → c.head.val + 1 < tapeLength R B) ∧
    ((machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) :=
  h1_no_clamp raw t ht

theorem check_inherited_h2 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let S0 := switchTime (pairLength a m)
    let T := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a
    let c := initialConfig machine B (encodePair x w)
    machine.run (S0 + T) c = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailStartConfig B x w)) ∧
    (machine.run (S0 + T) c).state.val = 12 ∧
    (machine.run (S0 + T) c).head.val = 2 * a ∧
    (machine.run (S0 + T) c).tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (∀ t, S0 ≤ t → t < S0 + T →
      7 ≤ (machine.run t c).state.val ∧ (machine.run t c).state.val < 12) ∧
    (∀ t, t ≤ S0 + T →
      (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
    (let p := machine.run (S0 + (2 * a + 1)) c
     p.state.val = 9 ∧ p.head.val = 2 * a + 1 ∧
     p.tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
     (∃ b : Bool, p.tape p.head = some b ∧
       machine.step p.state (p.tape p.head) = (⟨12, by decide⟩, some b, .left)) ∧
     0 < p.head.val) :=
  inherited_h2 x w

theorem check_raw_countdown_drained
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
    let D := rawChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (initialConfig machine B (encodePair x w))
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    e = ⟨machine.accept, ⟨a + m + 2 + zeros, by
      unfold tapeLength pairLength; omega⟩, loopTape B x w zeros 0 v⟩ ∧
    (∀ t, D ≤ t → machine.run t (initialConfig machine B (encodePair x w)) = e) :=
  raw_countdown_drained x w htag hg h hzeros hfence hroom hv hhigh

theorem check_malformed_raw_reject {R B : Nat} (raw : Bitstring R)
    (hdecode : decodePair raw = none) (hB : 0 < B) (s : Nat) :
    machine.run (switchTime R + (R + 2 + s)) (initialConfig machine B raw) =
      ⟨machine.reject, ⟨R + 1, by unfold tapeLength; omega⟩, FixedPairConcatSentinel.sentinelTape B raw⟩ :=
  malformed_raw_reject raw hdecode hB s

theorem check_rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (FixedContentTagGate.tagMatches (Fin.append x w) = true →
      gammaZeros? (Fin.append x w) = none →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).state = machine.reject ∧
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).head.val = a + m ∧
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).tape =
          FixedPairContentMarkerErase.contentTape B x w) ∧
    (FixedContentTagGate.tagMatches (Fin.append x w) = false →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).state = machine.reject ∧
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w))).tape =
          FixedPairContentMarkerErase.contentTape B x w) :=
  rejection_transport x w

theorem check_inherited_h3 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + 1)) (initialConfig machine B (encodePair x w))
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w))) ∧
    e.state.val = 15 ∧ e.head.val = 2 * a ∧ e.tape = FixedPairSeparatorHole.holeTape B x w :=
  inherited_h3 x w

theorem check_inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + FixedPairTagRemoval.clock a))) (initialConfig machine B (encodePair x w))
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w)))) ∧
    e.state.val = 24 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w :=
  inherited_h4 x w

theorem check_inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m)))
     ) (initialConfig machine B (encodePair x w))).state.val = 31 ∧
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m))))) (initialConfig machine B (encodePair x w))
     e.state.val = 57 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3))))))
     ) (initialConfig machine B (encodePair x w))).state.val = 61 :=
  inherited_switches x w

theorem check_inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a - 2)))) (initialConfig machine B (encodePair x w))
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left :=
  inherited_origin_clamp x w

theorem check_inherited_h5_h7_fields {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
      (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m))))
        (initialConfig machine B (encodePair x w))
     e.head.val = pairLength a m + Nat.min B 1 ∧
     e.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w) ∧
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
      (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3)))))))
        (initialConfig machine B (encodePair x w))
     e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w) :=
  inherited_h5_h7_fields x w

theorem check_clock_pins (C a m zeros d v R : Nat) :
    switchTime R = 2 * R + 1 ∧
    switchTime (pairLength a m) + FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a = 6 * a + 2 * m + 5 ∧
    switchTime (pairLength a m) + FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a ≤ 3 * pairLength a m + 2 ∧
    switchTime R + (R + 2) = 3 * R + 3 ∧
    rawChainClock C a m zeros d v = switchTime (pairLength a m) +
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + 1 + FixedPairTagRemoval.clock a +
      FixedPairOriginShiftAlignmentCountdown.switchTime a m +
      FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3) +
      (3 * (a + m) + 7) + (zeros + 1) + (2 * zeros + 5) + C +
      FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.bootChainClock
        (a + m) zeros d v) :=
  clock_pins C a m zeros d v R

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 := ![false, false, false, false, true, true, false, false, true]
private def emptyWord : Bitstring 0 := Fin.elim0
private def snapshot {R B : Nat} (c : Config machine.stateCount R B) :
    Nat × Nat × List (Option Bool) := (c.state.val, c.head.val, List.ofFn c.tape)

theorem check_empty_pair_literal_runs :
    ([0,1,2,3,4,5,6].map fun t => snapshot
      (machine.run t (initialConfig machine 0 (encodePair emptyWord emptyWord)))) =
      [(0,0,[some true,none]), (2,1,[none,none]), (4,0,[none,some true]),
       (7,0,[some true,some true]), (9,1,[some true,some true]),
       (12,0,[some true,some true]), (15,0,[none,some true])] ∧
    ([0,1,2,3,4,5,6].map fun t => snapshot
      (machine.run t (initialConfig machine 1 (encodePair emptyWord emptyWord)))) =
      [(0,0,[some true,none,none]), (2,1,[none,none,none]), (4,0,[none,some true,none]),
       (7,0,[some true,some true,none]), (9,1,[some true,some true,none]),
       (12,0,[some true,some true,none]), (15,0,[none,some true,none])] := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000000 in
theorem check_small_pair_boundaries :
    ∀ (a m B : Fin 2) (b c : Bool),
    let x : Bitstring a.val := fun _ => b
    let w : Bitstring m.val := fun _ => c
    let raw := encodePair x w
    let S0 := switchTime (pairLength a.val m.val)
    let T := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a.val
    let c := initialConfig machine B.val raw
    let tape := List.ofFn (FixedPairConcatSentinel.sentinelTape B.val raw)
    snapshot (machine.run (S0 - 1) c) =
      (if a.val = 0 then 4 else 3, 0, none :: tape.tail) ∧
    snapshot (machine.run S0 c) = (7, 0, tape) ∧
    snapshot (machine.run (S0 + (T - 1)) c) = (9, 2 * a.val + 1, tape) ∧
    snapshot (machine.run (S0 + T) c) = (12, 2 * a.val, tape) ∧
    snapshot (machine.run (S0 + (T + 1)) c) =
      (15, 2 * a.val, List.ofFn (FixedPairSeparatorHole.holeTape B.val x w)) := by decide

set_option maxRecDepth 4000000 in
theorem check_malformed_literal_runs :
    decodePair emptyWord = none ∧ decodePair (![false] : Bitstring 1) = none ∧
    decodePair (![false,false] : Bitstring 2) = none ∧ decodePair (![false,true] : Bitstring 2) = none ∧
    snapshot (machine.run 1 (initialConfig machine 1 emptyWord)) = (7,0,[some true,none]) ∧
    snapshot (machine.run 3 (initialConfig machine 1 emptyWord)) = (207,1,[some true,none]) ∧
    snapshot (machine.run 6 (initialConfig machine 1 (![false] : Bitstring 1))) =
      (207,2,[some false,some true,none]) ∧
    snapshot (machine.run 9 (initialConfig machine 1 (![false,false] : Bitstring 2))) =
      (207,3,[some false,some false,some true,none]) ∧
    snapshot (machine.run 9 (initialConfig machine 1 (![false,true] : Bitstring 2))) =
      (207,3,[some false,some true,some true,none]) := by
  repeat' apply And.intro
  all_goals decide

theorem check_malformed_persistence (s : Nat) :
    snapshot (machine.run (3 + s) (initialConfig machine 1 emptyWord)) =
      (207,1,[some true,none]) ∧
    snapshot (machine.run (6 + s) (initialConfig machine 1 (![false] : Bitstring 1))) =
      (207,2,[some false,some true,none]) ∧
    snapshot (machine.run (9 + s) (initialConfig machine 1 (![false,false] : Bitstring 2))) =
      (207,3,[some false,some false,some true,none]) ∧
    snapshot (machine.run (9 + s) (initialConfig machine 1 (![false,true] : Bitstring 2))) =
      (207,3,[some false,some true,some true,none]) := by
  have h0 := malformed_raw_reject (B := 1) emptyWord (by decide) (by decide) s
  have h1 := malformed_raw_reject (B := 1) (![false] : Bitstring 1) (by decide) (by decide) s
  have h2 := malformed_raw_reject (B := 1) (![false,false] : Bitstring 2) (by decide) (by decide) s
  have h3 := malformed_raw_reject (B := 1) (![false,true] : Bitstring 2) (by decide) (by decide) s
  simp only [switchTime, FixedPairConcatSentinel.clock_eq, ← Nat.add_assoc] at h0 h1 h2 h3
  norm_num only at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  decide

theorem check_zero_padding_and_raw_local_distinction :
    ([0,1,2,3].map fun t => snapshot (machine.run t (initialConfig machine 0 emptyWord))) =
      [(0,0,[none]), (7,0,[some true]), (9,0,[some true]), (12,0,[some true])] ∧
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.run 2 (initialConfig FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine 0 (encodePair emptyWord emptyWord))).state = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.reject ∧
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.run 2 (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig 0 emptyWord emptyWord)).state.val = 5 ∧
    snapshot (machine.run 5 (initialConfig machine 0 (encodePair emptyWord emptyWord))) =
      (12,0,[some true,some true]) := by decide

theorem check_clock_values :
    switchTime 26 = 53 ∧ rawChainClock 18 8 9 4 0 24 = 3044 ∧
    (3044 : Nat) = 53 + 2991 ∧ (22 : Nat) < 3044 ∧
    tapeLength (pairLength 8 9) 22 = 49 := by decide

theorem check_inherited_endpoint_probes :
    (machine.run 53 (initialConfig machine 22 (encodePair tag physWord))).state.val = 7 ∧
    (machine.run 71 (initialConfig machine 22 (encodePair tag physWord))).state.val = 12 ∧
    (machine.run 72 (initialConfig machine 22 (encodePair tag physWord))).state.val = 15 ∧
    (let e := machine.run 176 (initialConfig machine 22 (encodePair tag physWord))
     e.head.val = 0 ∧ (machine.step e.state (e.tape e.head)).2.2 = .left) ∧
    (machine.run 178 (initialConfig machine 22 (encodePair tag physWord))).state.val = 24 ∧
    (machine.run 242 (initialConfig machine 22 (encodePair tag physWord))).state.val = 31 ∧
    (let e := machine.run 1832 (initialConfig machine 22 (encodePair tag physWord))
     e.state.val = 57 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape 22 tag physWord) ∧
    (machine.run 1852 (initialConfig machine 22 (encodePair tag physWord))).state.val = 61 :=
  ⟨(handoff_exact (encodePair tag physWord)).2.2.2.2.2.1,
    (inherited_h2 tag physWord).2.1, (inherited_h3 tag physWord).2.1,
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

theorem check_drained_literal_endpoint :
    let e := machine.run 3044 (initialConfig machine 22 (encodePair tag physWord))
    e.state = machine.accept ∧ e.state.val = 206 ∧ e.head.val = 23 ∧
      e.tape = loopTape 22 tag physWord 4 0 24 ∧
      e = ⟨machine.accept, ⟨23, by decide⟩, loopTape 22 tag physWord 4 0 24⟩ ∧
      (∀ t, 3044 ≤ t → machine.run t (initialConfig machine 22 (encodePair tag physWord)) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  have hc : rawChainClock (3 * 4 + 6) 8 9 4 0 24 = 3044 := rfl
  obtain ⟨h1, h2, h3, hfull, h4⟩ :=
    raw_countdown_drained
      (q := FixedGammaPayloadDispatcher.qHasOne)
      (a := 8) (m := 9) (B := 22) (C := 3 * 4 + 6) (zeros := 4) (v := 24) (F := 24) tag physWord
      (by decide) (by decide)
      (first_true_strict_first_terminal (zeros := 4) tag physWord (by decide) (by decide)
        (by omega) (by decide) (by decide)).1
      (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 hfull h4
  rw [hc] at h1 h2 h3 hfull h4
  refine ⟨h1, ?_, h2, h3, hfull, h4⟩
  rw [h1]; decide

theorem check_rejection_endpoint_probes :
    (∀ s, let e := machine.run (30 + s) (initialConfig machine 0 (encodePair emptyWord emptyWord))
     e.state = machine.reject ∧ e.state.val = 207 ∧ e.head.val = 0 ∧
     e.head = (FixedContentTagGate.finalConfig 0 emptyWord emptyWord).head ∧
     e.tape = FixedPairContentMarkerErase.contentTape 0 emptyWord emptyWord) ∧
    (∀ s, let e := machine.run (1047 + s) (initialConfig machine 0 (encodePair tag emptyWord))
     e.state = machine.reject ∧ e.state.val = 207 ∧ e.head.val = 8 ∧
     e.tape = FixedPairContentMarkerErase.contentTape 0 tag emptyWord) := by
  constructor
  · intro s
    obtain ⟨hq, hh, ht⟩ := (rejection_transport (B := 0) emptyWord emptyWord).2
      (by decide) (22 + s) (by change 22 ≤ 22 + s; omega)
    have he : switchTime (pairLength 0 0) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime 0 + (1 + (FixedPairTagRemoval.clock 0 + (22 + s)))) = 30 + s := by
      change 3 + (2 + (1 + (2 + (22 + s)))) = 30 + s; omega
    rw [he] at hq hh ht
    refine ⟨hq, ?_, ?_, hh, ht⟩
    · rw [hq]; rfl
    · rw [hh]; rfl
  · intro s
    obtain ⟨hq, hh, ht⟩ := (rejection_transport (B := 0) tag emptyWord).1
      (by decide) (by decide) (887 + s) (by change 887 ≤ 887 + s; omega)
    have he : switchTime (pairLength 8 0) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime 8 + (1 + (FixedPairTagRemoval.clock 8 + (887 + s)))) = 1047 + s := by
      change 35 + (18 + (1 + (106 + (887 + s)))) = 1047 + s; omega
    rw [he] at hq hh ht
    refine ⟨hq, ?_, hh, ht⟩
    rw [hq]; rfl


theorem check_h5_h7_tapes :
    (let e := machine.run 242 (initialConfig machine 22 (encodePair tag physWord))
     e.head.val = 27 ∧ e.tape = FixedPairOriginShiftBootstrap.shiftedTape 22 tag physWord) ∧
    (let e := machine.run 1852 (initialConfig machine 22 (encodePair tag physWord))
     e.head.val = 17 ∧ e.tape = FixedPairContentMarkerErase.contentTape 22 tag physWord) :=
  inherited_h5_h7_fields tag physWord

#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inSentinel
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inTail
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.route
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tailStart
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tailRawStart
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.switchTime
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.rawChainClock
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.entry_pins
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tail_start_at_first_arrival
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.sentinel_first_arrival
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.raw_suffix
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.table_and_resource_pins
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.step_eq_rawStep
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.dead_left_verdicts
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.accept_rows_unique
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.reject_rows_absent
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.left_rows
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.h1_no_clamp
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h2
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.raw_countdown_drained
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.malformed_raw_reject
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.rejection_transport
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h3
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h4
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_switches
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_origin_clamp
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h5_h7_fields
#check FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.clock_pins

end Pnp3.Tests.UniformV1FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
