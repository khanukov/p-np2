import Complexity.Uniform.V1.SequentialComposition
import Complexity.Uniform.V1.FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown

/-! G3p Infrastructure: executed H2 into unchanged G3o. This phase-local start
does not execute H1 or raw input. No parser/verifier or P-vs-NP bridge. -/
namespace Pnp3.Complexity.Uniform.V1.FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

abbrev leftMachine : UniformTM := FixedPairSeparatorCursor.machine
abbrev tailMachine : UniformTM :=
  FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine

abbrev tailStartConfig {a m : Nat}
    (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w

def machine : UniformTM := leftMachine.seq tailMachine

def inCursor (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqLeft tailMachine q

def inTail (q : Fin tailMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqRight tailMachine q

def route (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqRoute tailMachine q

def tailStart : Fin machine.stateCount := inTail tailMachine.start

def startConfig {a m : Nat}
    (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  leftMachine.seqEmbedRouted tailMachine
    (FixedPairSeparatorCursor.startConfig B (encodePair x w))

def switchTime (a : Nat) : Nat := 2 * a + 2

def cursorChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime a +
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.holeChainClock C a m zeros d v

theorem tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run (switchTime a)
      (FixedPairSeparatorCursor.startConfig B (encodePair x w))
    g = FixedPairSeparatorCursor.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show leftMachine.run (switchTime a) (FixedPairSeparatorCursor.startConfig B (encodePair x w)) =
      FixedPairSeparatorCursor.finalConfig B x w from FixedPairSeparatorCursor.run_encoded_exact B x w]
  exact ⟨rfl, Config.ext_parts rfl rfl rfl⟩

theorem cursor_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < (switchTime a) →
      (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠ leftMachine.accept ∧
      (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠ leftMachine.reject) ∧
    (leftMachine.run (switchTime a) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state =
      leftMachine.accept ∧
    (∀ t, (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state ≠
      leftMachine.reject) := by
  refine ⟨fun t ht => FixedPairSeparatorCursor.noEarlyTerminal x w t ht,
    (congrArg Config.state (FixedPairSeparatorCursor.run_encoded_exact B x w)), fun t => ?_⟩
  by_cases ht : t < (switchTime a)
  · exact (FixedPairSeparatorCursor.noEarlyTerminal x w t ht).2
  · have hle : (FixedPairSeparatorCursor.clock a) ≤ t := Nat.le_of_not_gt ht
    rw [show t = (FixedPairSeparatorCursor.clock a) + (t - (FixedPairSeparatorCursor.clock a)) by omega,
      FixedPairSeparatorCursor.run_after_clock x w]
    exact leftMachine.accept_ne_reject

theorem suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (switchTime a + s) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailStartConfig B x w)) := by
  rw [(tail_start_at_first_arrival (B := B) x w).2]
  exact leftMachine.seq_handoff tailMachine (FixedPairSeparatorCursor.startConfig B (encodePair x w))
    (fun t ht => ((cursor_first_arrival (B := B) x w).1 t ht).1)
    (cursor_first_arrival (B := B) x w).2.1 s

set_option maxRecDepth 40000 in

theorem table_and_resource_pins :
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
          (tailMachine.step q s).2.2)) := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide,
    fun _ => rfl, fun _ => rfl, leftMachine.seqLeft_injective tailMachine,
    leftMachine.seqRight_injective tailMachine, leftMachine.seqLeft_ne_seqRight tailMachine,
    ?_, leftMachine.seq_step_left tailMachine, leftMachine.seq_step_right tailMachine⟩
  intro q
  have hcount : machine.stateCount = 5 + tailMachine.stateCount := rfl
  have hlt := q.isLt
  by_cases h : q.val < 5
  · exact Or.inl ⟨⟨q.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨q.val - 5, by omega⟩, Fin.ext (by show q.val = 5 + (q.val - 5); omega)⟩

theorem accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q = FixedPairSeparatorCursor.qPeek ∧ ∃ b : Bool, s = some b := by
  revert ha s q
  decide

theorem reject_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      (q = FixedPairSeparatorCursor.qTag ∨ q = FixedPairSeparatorCursor.qData ∨
        q = FixedPairSeparatorCursor.qPeek) ∧ s = none := by
  revert hr ha s q
  decide

theorem handoff_exact {a m B : Nat}
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
        (tailMachine.run s (tailStartConfig B x w))) := by
  intro cR c
  obtain ⟨hno, -, -⟩ := cursor_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ := leftMachine.seq_pins tailMachine
  have hleft := leftMachine.seq_run_left tailMachine cR (fun t ht => (hno t ht).1)
  have hC : machine.run (switchTime a) c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) := suffix x w 0
  have hCs : (machine.run (switchTime a) c).state = tailStart := by rw [hC]; rfl
  have hCa : (machine.run (switchTime a) c).state ≠ machine.accept := by rw [hCs]; decide
  have hCr : (machine.run (switchTime a) c).state ≠ machine.reject := by rw [hCs]; decide
  refine ⟨fun t ht => ?_, UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC,
    ?_, ?_, ?_, suffix x w⟩
  · have hrt : machine.run t c = leftMachine.seqEmbedRouted tailMachine
        (leftMachine.run t cR) := hleft t (Nat.le_of_lt ht)
    rw [hrt]
    show (leftMachine.seqRoute tailMachine (leftMachine.run t cR).state).val < 5
    rw [hrw _ (hno t ht).1 (hno t ht).2]
    exact (leftMachine.run t cR).state.isLt
  · rw [hCs]; decide
  · rw [hC]; rfl
  · rw [hC]; rfl

theorem separator_cursor_countdown_drained
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
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.separator_hole_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (cursorChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w) = leftMachine.seqEmbedRight tailMachine
        (tailMachine.run
          (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.holeChainClock C a m zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) := suffix x w _
  have hstate : (machine.run (cursorChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => machine.run_accept_of_le _ hstate ht⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3

theorem entry_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    pairLength a m = 2 * a + 1 + m ∧
    tapeLength (pairLength a m) B = 2 * a + m + B + 2 ∧
    (startConfig B x w).state.val = 0 ∧
    (startConfig B x w).head.val = 0 ∧
    (startConfig B x w).tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  unfold tapeLength pairLength
  omega

theorem step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s := leftMachine.seq_step_eq_rawStep tailMachine q s

theorem dead_left_verdicts :
    machine.start.val ≠ 3 ∧ machine.start.val ≠ 4 ∧
    (∀ q s, (machine.step q s).1.val ≠ 3 ∧ (machine.step q s).1.val ≠ 4) := by
  refine ⟨by decide, by decide, ?_⟩
  intro q s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcover, hl, hr⟩ := table_and_resource_pins
  rcases hcover q with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [hl]
    have h : ∀ p s, (route (leftMachine.step p s).1).val ≠ 3 ∧
        (route (leftMachine.step p s).1).val ≠ 4 := by decide
    exact h p s
  · rw [hr]
    change 5 + _ ≠ 3 ∧ 5 + _ ≠ 4
    omega

set_option maxRecDepth 40000 in
theorem left_rows :
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
    machine.step ⟨9, by decide⟩ none = (⟨17, by decide⟩, none, .stay) := by
  repeat' apply And.intro <;> decide

private theorem routed_live {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (t : Nat) (ht : t < switchTime a) :
    (machine.run t (startConfig B x w)).state =
      inCursor (leftMachine.run t (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state := by
  rw [(handoff_exact x w).2.2.1 t (Nat.le_of_lt ht)]
  exact (leftMachine.seq_pins tailMachine).2.2.2.2.2.2.2.2.2.2.2 _
    ((cursor_first_arrival x w).1 t ht).1 ((cursor_first_arrival x w).1 t ht).2

theorem h2_preterminal_and_no_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
        FixedPairConcatSentinel.sentinelTape B (encodePair x w)) := by
  have hp : 2 * a + 1 < switchTime a := by unfold switchTime; omega
  have hl := (handoff_exact (B := B) x w).2.2.1
  obtain ⟨hq, hh, ht⟩ := FixedPairSeparatorCursor.run_preterminal_exact (B := B) x w
  have hread : ∃ b : Bool,
      (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).tape
        (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).head = some b := by
    have he := (cursor_first_arrival (B := B) x w).2.1
    change (leftMachine.step
      (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).state
      ((leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).tape
        (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).head)).1 = leftMachine.accept at he
    rw [hq] at he
    cases hs : (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).tape
        (leftMachine.run (2 * a + 1) (FixedPairSeparatorCursor.startConfig B (encodePair x w))).head with
    | none => rw [hs] at he; contradiction
    | some b => exact ⟨b, rfl⟩
  refine ⟨by unfold switchTime; omega, ?_, (handoff_exact x w).2.2.2.2.2.1, ?_, ?_⟩
  · dsimp only
    have hq' := (routed_live (B := B) x w _ hp).trans (congrArg inCursor hq)
    obtain ⟨b, hb⟩ := hread
    have hb' : (machine.run (2 * a + 1) (startConfig B x w)).tape
        (machine.run (2 * a + 1) (startConfig B x w)).head = some b := by
      rw [hl _ (Nat.le_of_lt hp)]; exact hb
    refine ⟨hq', ?_, ?_, ⟨b, hb', ?_⟩, ?_⟩
    · rw [hl _ (Nat.le_of_lt hp)]; exact hh
    · rw [hl _ (Nat.le_of_lt hp)]; exact ht
    · rw [hq', hb']; exact left_rows.2.2.2.2.2.2.1 b
    · rw [hl _ (Nat.le_of_lt hp)]
      change 0 < (FixedPairSeparatorCursor.machine.run (2 * a + 1) _).head.val
      rw [hh]; omega
  · intro t ht
    dsimp only
    rw [routed_live x w t ht]
    rw [show machine.step (inCursor _) _ = _ from leftMachine.seq_step_left tailMachine _ _]
    rw [hl t (Nat.le_of_lt ht)]
    exact FixedPairSeparatorCursor.no_boundary_clamp_before_clock x w t ht
  · intro t ht
    rw [hl t ht]
    exact ⟨(FixedPairSeparatorCursor.phase_contract x w).2.2.1 t ht,
      (FixedPairSeparatorCursor.phase_contract x w).2.2.2.2.1 t ht⟩

theorem h3_stationary {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime a) (startConfig B x w)
    (machine.step c.state (c.tape c.head)).2.2 = .stay := by
  dsimp only
  rw [(handoff_exact x w).2.2.2.1]
  change ((leftMachine.seq tailMachine).step (leftMachine.seqRight tailMachine _ ) _).2.2 = _
  rw [UniformTM.seq_step_right]
  exact FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.h3_stationary x w

theorem inherited_h3 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a + 1) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w)) ∧
    e.state.val = 8 ∧ e.head.val = 2 * a ∧ e.tape = FixedPairSeparatorHole.holeTape B x w := by
  dsimp only
  rw [suffix]
  have he : tailMachine.run 1 (tailStartConfig B x w) = _ :=
    (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.1
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a + (1 + FixedPairTagRemoval.clock a)) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w))) ∧
    e.state.val = 17 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w := by
  dsimp only
  rw [suffix, (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.inherited_h4 x w).1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m)))
      (startConfig B x w)).state.val = 24 ∧
    (let e := machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m)))) (startConfig B x w)
     e.state.val = 50 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3))))))
      (startConfig B x w)).state.val = 54 := by
  obtain ⟨h5, h6, h7⟩ := FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.inherited_switches (B := B) x w
  dsimp only at h6 ⊢
  simp only [suffix, UniformTM.seqEmbedRight_state, UniformTM.seqEmbedRight_head, UniformTM.seqEmbedRight_tape]
  exact ⟨congrArg (5 + ·) h5, ⟨congrArg (5 + ·) h6.1, h6.2⟩, congrArg (5 + ·) h7⟩

theorem inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime a + (1 + (FixedPairTagRemoval.clock a - 2))) (startConfig B x w)
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left := by
  dsimp only
  rw [suffix]
  change _ ∧ ((leftMachine.seq tailMachine).step (leftMachine.seqRight tailMachine _) _).2.2 = _
  rw [UniformTM.seq_step_right]
  exact FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.inherited_origin_clamp x w

theorem rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
          FixedPairContentMarkerErase.contentTape B x w) := by
  constructor
  · intro htag hg s hle
    obtain ⟨hr, hh, ht⟩ := (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.rejection_transport (B := B) x w).1 htag hg s hle
    rw [suffix]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩
  · intro htag s hle
    obtain ⟨hr, hh, ht⟩ := (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.rejection_transport (B := B) x w).2 htag s hle
    rw [suffix]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩

theorem scanned_reject {N B : Nat} (cL : Config leftMachine.stateCount N B)
    (hstate : cL.state = FixedPairSeparatorCursor.qTag ∨ cL.state = FixedPairSeparatorCursor.qData ∨
      cL.state = FixedPairSeparatorCursor.qPeek)
    (hread : cL.tape cL.head = none) (s : Nat) :
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine cL) =
      ⟨machine.reject, cL.head, cL.tape⟩ := by
  have ha : leftMachine.step cL.state (cL.tape cL.head) = (leftMachine.reject, cL.tape cL.head, .stay) := by
    rw [hread]
    rcases hstate with h | h | h <;> rw [h] <;> rfl
  have he : leftMachine.run 1 cL = ⟨leftMachine.reject, cL.head, cL.tape⟩ := by
    change leftMachine.stepConfig cL = _
    simp only [UniformTM.stepConfig, ha]
    refine Config.ext_parts rfl rfl ?_
    funext i
    dsimp only
    split <;> simp_all
  have h := leftMachine.seq_reject_handoff tailMachine cL (congrArg Config.state he) s
  rw [he] at h
  exact h

theorem malformed_sentinel_reject {N B : Nat} (raw : Bitstring N)
    (hdecode : decodePair raw = none) (hB : 0 < B) (s : Nat) :
    let c := leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig B raw)
    let e := machine.run (N + 2 + s) c
    e.state = machine.reject ∧ e.head.val = N + 1 ∧
    e.tape = FixedPairConcatSentinel.sentinelTape B raw ∧
    e = ⟨machine.reject, ⟨N + 1, by unfold tapeLength; omega⟩,
      FixedPairConcatSentinel.sentinelTape B raw⟩ := by
  obtain ⟨hq, hh, ht⟩ := FixedPairSeparatorCursor.malformed_literal_fields raw hdecode hB
  dsimp only
  have he : machine.run (N + 2 + s)
      (leftMachine.seqEmbedRouted tailMachine (FixedPairSeparatorCursor.startConfig B raw)) = _ :=
    leftMachine.seq_reject_handoff tailMachine _ hq s
  rw [he]
  exact ⟨rfl, hh, ht, Config.ext_parts rfl (Fin.ext hh) ht⟩

theorem clock_pins (C a m zeros d v : Nat) :
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
        (a + m) zeros d v := by
  refine ⟨rfl, rfl, by unfold switchTime; omega, rfl, rfl, ?_⟩
  change (2 * a + 2) + (1 + (a * (a + 5) + 2 +
    ((4 * a + 3 * m + 5) + (((10 * a + 7) * (a + m + 1) + 3 * a) +
      ((a + m + 3) + ((3 * (a + m) + 7) + ((zeros + 1) + ((2 * zeros + 5) + (C + _))))))))) = _
  simp only [switchTime, FixedPairTagRemoval.clock, FixedPairOriginShiftAlignmentCountdown.switchTime,
    FixedPairOriginShiftAlignmentCountdown.tailSwitchTime,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime, Nat.add_assoc]

end Pnp3.Complexity.Uniform.V1.FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown
