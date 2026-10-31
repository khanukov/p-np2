import Complexity.Uniform.V1.FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown

/-! G3q Infrastructure: actual H1 execution from raw initialConfig into unchanged G3p.
All downstream drain premises remain explicit; no semantic or resource bridge. -/
namespace Pnp3.Complexity.Uniform.V1.FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown
open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

abbrev leftMachine : UniformTM := FixedPairConcatSentinel.machine
abbrev tailMachine : UniformTM := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine
def machine : UniformTM := leftMachine.seq tailMachine
def inSentinel (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqLeft tailMachine q
def inTail (q : Fin tailMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqRight tailMachine q
def route (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
  leftMachine.seqRoute tailMachine q
def tailStart : Fin machine.stateCount := inTail tailMachine.start
/-- Specification of the phase-local successor; never the raw initial configuration. -/
def tailRawStart {R : Nat} (B : Nat) (raw : Bitstring R) :
    Config tailMachine.stateCount R B :=
  FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRouted FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
    (FixedPairSeparatorCursor.startConfig B raw)
def switchTime (R : Nat) : Nat := FixedPairConcatSentinel.clock R
def rawChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime (pairLength a m) + FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursorChainClock C a m zeros d v

set_option maxRecDepth 40000
set_option maxHeartbeats 200000

theorem entry_pins {R a m B : Nat} (raw : Bitstring R) (x : Bitstring a) (w : Bitstring m) :
    tailRawStart B raw = ⟨tailMachine.start, ⟨0, by simp [tapeLength]⟩,
      FixedPairConcatSentinel.sentinelTape B raw⟩ ∧
    tailRawStart B (encodePair x w) = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w ∧
    (initialConfig machine B raw).tape ⟨R, by unfold tapeLength; omega⟩ = none ∧
    (tailRawStart B raw).tape ⟨R, by unfold tapeLength; omega⟩ = some true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [initialConfig]
  · simp [tailRawStart, UniformTM.seqEmbedRouted, FixedPairSeparatorCursor.startConfig,
      FixedPairConcatSentinel.sentinelTape]

theorem tail_start_at_first_arrival {R B : Nat} (raw : Bitstring R) :
    let g := leftMachine.run (switchTime R) (initialConfig leftMachine B raw)
    g = FixedPairConcatSentinel.sentinelConfig B raw ∧
    tailRawStart B raw = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp only
  rw [show leftMachine.run (switchTime R) (initialConfig leftMachine B raw) =
    FixedPairConcatSentinel.sentinelConfig B raw from FixedPairConcatSentinel.run_initialConfig_exact B raw]
  exact ⟨rfl, rfl⟩

theorem sentinel_first_arrival {R B : Nat} (raw : Bitstring R) :
    (∀ t, t < switchTime R →
      (leftMachine.run t (initialConfig leftMachine B raw)).state ≠ leftMachine.accept ∧
      (leftMachine.run t (initialConfig leftMachine B raw)).state ≠ leftMachine.reject) ∧
    (leftMachine.run (switchTime R) (initialConfig leftMachine B raw)).state = leftMachine.accept :=
  ⟨FixedPairConcatSentinel.noEarlyTerminal_initialConfig raw,
    congrArg Config.state (FixedPairConcatSentinel.run_initialConfig_exact B raw)⟩

theorem raw_suffix {R B : Nat} (raw : Bitstring R) (s : Nat) :
    machine.run (switchTime R + s) (initialConfig machine B raw) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailRawStart B raw)) := by
  rw [(tail_start_at_first_arrival (B := B) raw).2]
  exact leftMachine.seq_handoff tailMachine (initialConfig leftMachine B raw)
    (fun t ht => ((sentinel_first_arrival (B := B) raw).1 t ht).1)
    (sentinel_first_arrival (B := B) raw).2 s

theorem handoff_exact {R B : Nat} (raw : Bitstring R) :
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
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailRawStart B raw))) := by
  intro c
  have hno := (sentinel_first_arrival (B := B) raw).1
  have hl := leftMachine.seq_run_left tailMachine (initialConfig leftMachine B raw)
    (fun t ht => (hno t ht).1)
  have he : machine.run (switchTime R) c =
      leftMachine.seqEmbedRight tailMachine (tailRawStart B raw) := raw_suffix raw 0
  have hs : (machine.run (switchTime R) c).state = tailStart := by rw [he]; rfl
  refine ⟨?_, UniformTM.no_terminal_of_le machine c
    (by rw [hs]; decide) (by rw [hs]; decide), hl, he, hs,
    by rw [hs]; rfl, by rw [he]; rfl, by rw [he]; rfl, raw_suffix raw⟩
  intro t ht
  rw [show machine.run t c = _ from hl t (Nat.le_of_lt ht)]
  change (leftMachine.seqRoute tailMachine _).val < 5
  rw [(leftMachine.seq_pins tailMachine).2.2.2.2.2.2.2.2.2.2.2 _ (hno t ht).1 (hno t ht).2]
  exact FixedPairConcatSentinel.work_state_before_clock raw t ht

theorem table_and_resource_pins :
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
          (tailMachine.step q s).2.2)) := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide,
    fun _ => rfl, fun _ => rfl, leftMachine.seqLeft_injective tailMachine,
    leftMachine.seqRight_injective tailMachine, leftMachine.seqLeft_ne_seqRight tailMachine,
    ?_, leftMachine.seq_step_left tailMachine, leftMachine.seq_step_right tailMachine⟩
  intro q
  have hcount : machine.stateCount = 7 + tailMachine.stateCount := rfl
  have hlt := q.isLt
  by_cases h : q.val < 7
  · exact Or.inl ⟨⟨q.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨q.val - 7, by omega⟩, Fin.ext (by show q.val = 7 + (q.val - 7); omega)⟩

theorem step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s := leftMachine.seq_step_eq_rawStep tailMachine q s

theorem dead_left_verdicts :
    machine.start.val ≠ 5 ∧ machine.start.val ≠ 6 ∧
    (∀ q s, (machine.step q s).1.val ≠ 5 ∧ (machine.step q s).1.val ≠ 6) := by
  refine ⟨by decide, by decide, ?_⟩
  intro q s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcover, hl, hr⟩ := table_and_resource_pins
  rcases hcover q with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [hl]
    have h : ∀ p s, (route (leftMachine.step p s).1).val ≠ 5 ∧
        (route (leftMachine.step p s).1).val ≠ 6 := by decide
    exact h p s
  · rw [hr]
    change 7 + _ ≠ 5 ∧ 7 + _ ≠ 6
    omega

theorem accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      (q = FixedPairConcatSentinel.qStart ∨ q = FixedPairConcatSentinel.qBackF ∨ q = FixedPairConcatSentinel.qBackT) ∧ s = none := by
  revert hr ha s q
  decide

theorem reject_rows_absent (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 ≠ leftMachine.reject := by
  revert hr ha s q
  decide

theorem left_rows :
    machine.step (inSentinel FixedPairConcatSentinel.qStart) none = (tailStart, some true, .stay) ∧
    machine.step (inSentinel FixedPairConcatSentinel.qBackF) none = (tailStart, some false, .stay) ∧
    machine.step (inSentinel FixedPairConcatSentinel.qBackT) none = (tailStart, some true, .stay) ∧
    (∀ s, machine.step (inSentinel leftMachine.accept) s = (tailStart, s, .stay)) ∧
    (∀ s, machine.step (inSentinel leftMachine.reject) s = (machine.reject, s, .stay)) := by
  repeat' apply And.intro <;> decide

theorem h1_no_clamp {R B : Nat} (raw : Bitstring R) (t : Nat) (ht : t < switchTime R) :
    let c := machine.run t (initialConfig machine B raw)
    ((machine.step c.state (c.tape c.head)).2.2 = .right → c.head.val + 1 < tapeLength R B) ∧
    ((machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) := by
  dsimp only
  rw [(handoff_exact raw).2.2.1 t (Nat.le_of_lt ht)]
  have hn := (sentinel_first_arrival (B := B) raw).1 t ht
  have hr := (leftMachine.seq_pins tailMachine).2.2.2.2.2.2.2.2.2.2.2 _ hn.1 hn.2
  simp only [UniformTM.seqEmbedRouted_state, UniformTM.seqEmbedRouted_tape,
    UniformTM.seqEmbedRouted_head]
  rw [hr]
  simp only [machine, UniformTM.seq_step_left]
  exact FixedPairConcatSentinel.no_boundary_clamp_before_clock raw t ht

private theorem pair_suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (t : Nat) :
    machine.run (switchTime (pairLength a m) + t) (initialConfig machine B (encodePair x w)) =
      leftMachine.seqEmbedRight tailMachine
        (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.run t (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w)) :=
  raw_suffix (encodePair x w) t

theorem inherited_h2 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
     0 < p.head.val) := by
  dsimp only
  have he : machine.run (switchTime (pairLength a m) + FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a)
      (initialConfig machine B (encodePair x w)) = _ := raw_suffix (encodePair x w) _
  rw [show tailRawStart B (encodePair x w) = FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w from rfl,
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact x w).2.2.2.1] at he
  have hs : (machine.run (switchTime (pairLength a m) + FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a)
      (initialConfig machine B (encodePair x w))).state.val = 12 := by rw [he]; rfl
  refine ⟨he, hs, by rw [he]; rfl, by rw [he]; rfl, ?_, ?_, ?_⟩
  · intro t hlo hhi
    have ht : t = switchTime (pairLength a m) + (t - switchTime (pairLength a m)) := by omega
    rw [ht, pair_suffix]
    have hb := (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w).1
      (t - switchTime (pairLength a m)) (by omega)
    change 7 ≤ 7 + _ ∧ 7 + _ < 12
    exact ⟨by omega, by change _ < 5 at hb; omega⟩
  · apply UniformTM.no_terminal_of_le
    · intro h; have hv := congrArg Fin.val h; rw [hs] at hv; contradiction
    · intro h; have hv := congrArg Fin.val h; rw [hs] at hv; contradiction
  · obtain ⟨hq, hh, ht, ⟨b, hb, hr⟩, hp⟩ := (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.h2_preterminal_and_no_clamp (B := B) x w).2.1
    rw [pair_suffix]
    change (inTail _).val = 9 ∧ _
    refine ⟨?_, hh, ht, ⟨b, hb, ?_⟩, hp⟩
    · rw [hq]; rfl
    · change (leftMachine.seq tailMachine).step (leftMachine.seqRight tailMachine _) _ = _
      rw [UniformTM.seq_step_right]
      simp only [UniformTM.seqEmbedRight_tape, UniformTM.seqEmbedRight_head, tailMachine, hr]
      rfl

theorem raw_countdown_drained
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
    (∀ t, D ≤ t → machine.run t (initialConfig machine B (encodePair x w)) = e) := by
  obtain ⟨hs, hh, ht, -⟩ := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.separator_cursor_countdown_drained
    x w htag hg h hzeros hfence hroom hv hhigh
  have he := pair_suffix (B := B) x w
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursorChainClock C a m zeros (borrow x w zeros) v)
  generalize htail : FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.run
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.cursorChainClock C a m zeros (borrow x w zeros) v)
    (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.startConfig B x w) = ep at hs hh ht he
  change machine.run (rawChainClock C a m zeros (borrow x w zeros) v)
    (initialConfig machine B (encodePair x w)) = _ at he
  dsimp only
  generalize hraw : machine.run (rawChainClock C a m zeros (borrow x w zeros) v)
    (initialConfig machine B (encodePair x w)) = e at he ⊢
  have hstate : e.state = machine.accept :=
    (congrArg Config.state he).trans (congrArg (leftMachine.seqRight tailMachine) hs)
  have hhead : e.head.val = a + m + 2 + zeros :=
    (congrArg (fun c => c.head.val) he).trans hh
  have htape : e.tape = loopTape B x w zeros 0 v := (congrArg Config.tape he).trans ht
  refine ⟨hstate, hhead, htape, Config.ext_parts hstate (Fin.ext hhead) htape, ?_⟩
  intro t ht
  have ha : (machine.run (rawChainClock C a m zeros (borrow x w zeros) v)
      (initialConfig machine B (encodePair x w))).state = machine.accept := by
    rw [hraw]; exact hstate
  exact (machine.run_accept_of_le _ ha ht).trans hraw


theorem malformed_raw_reject {R B : Nat} (raw : Bitstring R)
    (hdecode : decodePair raw = none) (hB : 0 < B) (s : Nat) :
    machine.run (switchTime R + (R + 2 + s)) (initialConfig machine B raw) =
      ⟨machine.reject, ⟨R + 1, by unfold tapeLength; omega⟩, FixedPairConcatSentinel.sentinelTape B raw⟩ := by
  rw [raw_suffix]
  change leftMachine.seqEmbedRight tailMachine (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine.run _ _) = _
  unfold tailRawStart
  rw [(FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.malformed_sentinel_reject raw hdecode hB s).2.2.2]
  rfl

theorem rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
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
          FixedPairContentMarkerErase.contentTape B x w) := by
  constructor
  · intro htag hg s hle
    obtain ⟨hr, hh, ht⟩ := (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.rejection_transport (B := B) x w).1 htag hg s hle
    rw [raw_suffix]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩
  · intro htag s hle
    obtain ⟨hr, hh, ht⟩ := (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.rejection_transport (B := B) x w).2 htag s hle
    rw [raw_suffix]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩

theorem inherited_h3 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + 1)) (initialConfig machine B (encodePair x w))
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w))) ∧
    e.state.val = 15 ∧ e.head.val = 2 * a ∧ e.tape = FixedPairSeparatorHole.holeTape B x w := by
  dsimp only
  rw [pair_suffix, (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h3 x w).1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + FixedPairTagRemoval.clock a))) (initialConfig machine B (encodePair x w))
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w)))) ∧
    e.state.val = 24 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w := by
  dsimp only
  rw [pair_suffix, (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h4 x w).1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m)))
     ) (initialConfig machine B (encodePair x w))).state.val = 31 ∧
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m))))) (initialConfig machine B (encodePair x w))
     e.state.val = 57 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3))))))
     ) (initialConfig machine B (encodePair x w))).state.val = 61 := by
  obtain ⟨h5, h6, h7⟩ := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_switches (B := B) x w
  dsimp only at h6 ⊢
  simp only [pair_suffix, UniformTM.seqEmbedRight_state, UniformTM.seqEmbedRight_head, UniformTM.seqEmbedRight_tape]
  exact ⟨congrArg (7 + ·) h5, ⟨congrArg (7 + ·) h6.1, h6.2⟩, congrArg (7 + ·) h7⟩

theorem inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a + (1 + (FixedPairTagRemoval.clock a - 2)))) (initialConfig machine B (encodePair x w))
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left := by
  dsimp only
  rw [pair_suffix]
  change _ ∧ ((leftMachine.seq tailMachine).step (leftMachine.seqRight tailMachine _) _).2.2 = _
  rw [UniformTM.seq_step_right]
  exact FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.inherited_origin_clamp x w

private theorem after_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
      (1 + (FixedPairTagRemoval.clock a + s)))) (initialConfig machine B (encodePair x w)) =
    leftMachine.seqEmbedRight tailMachine
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine
          (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
            (FixedPairOriginShiftAlignmentCountdown.machine.run s (FixedPairOriginShiftAlignmentCountdown.startConfig B x w))))) := by
  rw [pair_suffix, FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.suffix, FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.suffix]
  exact congrArg (leftMachine.seqEmbedRight tailMachine)
    (congrArg (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine)
      (congrArg (FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine)
        ((FixedPairTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.2.2.2.2 s)))

theorem inherited_h5_h7_fields {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
      (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m))))
        (initialConfig machine B (encodePair x w))
     e.head.val = pairLength a m + Nat.min B 1 ∧
     e.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w) ∧
    (let e := machine.run (switchTime (pairLength a m) + (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
      (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3)))))))
        (initialConfig machine B (encodePair x w))
     e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w) := by
  constructor
  · dsimp only
    rw [after_h4]
    obtain ⟨-, -, -, -, -, -, hh, ht, -⟩ := FixedPairOriginShiftAlignmentCountdown.handoff_endpoint_pins (B := B) x w
    exact ⟨hh, ht⟩
  · dsimp only
    rw [after_h4, (FixedPairOriginShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.2]
    obtain ⟨-, -, -, hh, ht, -⟩ := FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.inherited_marker_erase_switch (B := B) x w
    exact ⟨hh, ht⟩

theorem clock_pins (C a m zeros d v R : Nat) :
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
        (a + m) zeros d v) := by
  refine ⟨FixedPairConcatSentinel.clock_eq R, ?_, ?_, ?_, ?_⟩
  all_goals try { simp only [switchTime, FixedPairConcatSentinel.clock_eq, FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime, pairLength]; omega }
  exact congrArg (switchTime (pairLength a m) + ·) (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.clock_pins C a m zeros d v).2.2.2.2.2

end Pnp3.Complexity.Uniform.V1.FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown
