import Complexity.Uniform.V1.SequentialComposition
import Complexity.Uniform.V1.FixedPairTagRemovalShiftAlignmentCountdown

/-! G3o Infrastructure: executed H3 into unchanged G3n. This phase-local start
does not execute H1–H2 or raw input. No parser/verifier or P-vs-NP bridge. -/
namespace Pnp3.Complexity.Uniform.V1.FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

abbrev leftMachine : UniformTM := FixedPairSeparatorHole.machine
abbrev tailMachine : UniformTM :=
  FixedPairTagRemovalShiftAlignmentCountdown.machine

abbrev tailStartConfig {a m : Nat}
    (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w

def machine : UniformTM := leftMachine.seq tailMachine

def inHole (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
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
    (FixedPairSeparatorHole.startConfig B x w)

def switchTime : Nat := 1

def holeChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime +
    FixedPairTagRemovalShiftAlignmentCountdown.removalChainClock C a m zeros d v

theorem tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run switchTime
      (FixedPairSeparatorHole.startConfig B x w)
    g = FixedPairSeparatorHole.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show leftMachine.run switchTime (FixedPairSeparatorHole.startConfig B x w) =
      FixedPairSeparatorHole.finalConfig B x w from FixedPairSeparatorHole.run_encoded_exact B x w]
  exact ⟨rfl, Config.ext_parts rfl rfl rfl⟩

theorem hole_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime →
      (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠ leftMachine.accept ∧
      (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠ leftMachine.reject) ∧
    (leftMachine.run switchTime (FixedPairSeparatorHole.startConfig B x w)).state =
      leftMachine.accept ∧
    (∀ t, (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠
      leftMachine.reject) := by
  refine ⟨fun t ht => FixedPairSeparatorHole.noEarlyTerminal x w t ht,
    (congrArg Config.state (FixedPairSeparatorHole.run_encoded_exact B x w)), fun t => ?_⟩
  by_cases ht : t < switchTime
  · exact (FixedPairSeparatorHole.noEarlyTerminal x w t ht).2
  · have hle : FixedPairSeparatorHole.clock ≤ t := Nat.le_of_not_gt ht
    rw [show t = FixedPairSeparatorHole.clock + (t - FixedPairSeparatorHole.clock) by omega,
      FixedPairSeparatorHole.run_after_clock x w]
    exact leftMachine.accept_ne_reject

theorem suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (1 + s) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailStartConfig B x w)) := by
  rw [(tail_start_at_first_arrival (B := B) x w).2]
  exact leftMachine.seq_handoff tailMachine (FixedPairSeparatorHole.startConfig B x w)
    (fun t ht => ((hole_first_arrival (B := B) x w).1 t ht).1)
    (hole_first_arrival (B := B) x w).2.1 s

set_option maxRecDepth 40000 in
/-- All 196 states and 588 rows are the unchanged two tables, with routed left targets. -/
theorem table_and_resource_pins :
    machine.stateCount = 196 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 588 ∧
    machine.start.val = 0 ∧ machine.accept.val = 194 ∧
    machine.reject.val = 195 ∧ tailStart.val = 3 ∧
    (∀ q, (inHole q).val = q.val) ∧
    (∀ q, (inTail q).val = 3 + q.val) ∧
    Function.Injective inHole ∧ Function.Injective inTail ∧
    (∀ p q, inHole p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inHole p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inHole q) s =
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
  have hcount : machine.stateCount = 3 + tailMachine.stateCount := rfl
  have hlt := q.isLt
  by_cases h : q.val < 3
  · exact Or.inl ⟨⟨q.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨q.val - 3, by omega⟩, Fin.ext (by show q.val = 3 + (q.val - 3); omega)⟩

/-- The sole live accepting row, excluding the absorbing accept source. -/
theorem accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q = FixedPairSeparatorHole.qStart ∧ s = some true := by
  revert ha s q
  decide

/-- The two live rejecting rows, excluding both verdict sources. -/
theorem reject_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      q = FixedPairSeparatorHole.qStart ∧ s ≠ some true := by
  revert hr ha s q
  decide

/-- H3 executes at the one-step hole clock, with no proposition premises or extra step.
The last conjunct transports every later G3n configuration, including its whole tape. -/
theorem handoff_exact {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let cR := FixedPairSeparatorHole.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime → (machine.run t c).state.val < 3) ∧
    (∀ t, t ≤ switchTime →
      (machine.run t c).state ≠ machine.accept ∧
      (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ switchTime →
      machine.run t c =
        leftMachine.seqEmbedRouted tailMachine (leftMachine.run t cR)) ∧
    machine.run switchTime c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
    (machine.run switchTime c).state.val = 3 ∧
    (machine.run switchTime c).head.val = 2 * a ∧
    (machine.run switchTime c).tape =
      FixedPairSeparatorHole.holeTape B x w ∧
    (∀ s, machine.run (switchTime + s) c =
      leftMachine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w))) := by
  intro cR c
  obtain ⟨hno, -, -⟩ := hole_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ := leftMachine.seq_pins tailMachine
  have hleft := leftMachine.seq_run_left tailMachine cR (fun t ht => (hno t ht).1)
  have hC : machine.run switchTime c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) := suffix x w 0
  have hCs : (machine.run switchTime c).state = tailStart := by rw [hC]; rfl
  have hCa : (machine.run switchTime c).state ≠ machine.accept := by rw [hCs]; decide
  have hCr : (machine.run switchTime c).state ≠ machine.reject := by rw [hCs]; decide
  refine ⟨fun t ht => ?_, UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC,
    ?_, ?_, ?_, suffix x w⟩
  · have hrt : machine.run t c = leftMachine.seqEmbedRouted tailMachine
        (leftMachine.run t cR) := hleft t (Nat.le_of_lt ht)
    rw [hrt]
    show (leftMachine.seqRoute tailMachine (leftMachine.run t cR).state).val < 3
    rw [hrw _ (hno t ht).1 (hno t ht).2]
    exact (leftMachine.run t cR).state.isLt
  · rw [hCs]; decide
  · rw [hC]; rfl
  · rw [hC]; rfl

/-- Exact execution and persistence, with G3n's eight hypotheses unchanged.
`v` is supplied in the theorem only; no decoding, runtime fence, or first arrival of
composed accept is claimed. `B` allocates tape and does not bound the run time. -/
theorem separator_hole_countdown_drained
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
    let D := holeChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedPairTagRemovalShiftAlignmentCountdown.tag_removal_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (holeChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w) = leftMachine.seqEmbedRight tailMachine
        (tailMachine.run
          (FixedPairTagRemovalShiftAlignmentCountdown.removalChainClock C a m zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) := suffix x w _
  have hstate : (machine.run (holeChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => machine.run_accept_of_le _ hstate ht⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3


/-- The phase-local entry ABI, for every allocation and both split lengths. -/
theorem entry_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    pairLength a m = 2 * a + 1 + m ∧
    tapeLength (pairLength a m) B = 2 * a + m + B + 2 ∧
    (startConfig B x w).state.val = 0 ∧
    (startConfig B x w).head.val = 2 * a ∧
    (startConfig B x w).tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (startConfig B x w).tape (startConfig B x w).head = some true := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, (FixedPairSeparatorHole.run_preterminal_exact (B := B) x w).2.2.2.2⟩
  unfold tapeLength pairLength
  omega

/-- Nine left rows, including the dead verdict copies, and the inherited H4 row. -/
theorem left_rows :
    machine.step (inHole FixedPairSeparatorHole.qStart) none = (machine.reject, none, .stay) ∧
    machine.step (inHole FixedPairSeparatorHole.qStart) (some false) =
      (machine.reject, some false, .stay) ∧
    machine.step (inHole FixedPairSeparatorHole.qStart) (some true) = (tailStart, none, .stay) ∧
    (∀ s, machine.step (inHole leftMachine.accept) s = (tailStart, s, .stay)) ∧
    (∀ s, machine.step (inHole leftMachine.reject) s = (machine.reject, s, .stay)) ∧
    machine.step ⟨4, by decide⟩ none = (⟨12, by decide⟩, none, .stay) := by
  decide

theorem step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s := leftMachine.seq_step_eq_rawStep tailMachine q s

/-- No target or start occupies either dead left verdict copy. -/
theorem dead_left_verdicts :
    machine.start.val ≠ 1 ∧ machine.start.val ≠ 2 ∧
    (∀ q s, (machine.step q s).1.val ≠ 1 ∧ (machine.step q s).1.val ≠ 2) := by
  refine ⟨by decide, by decide, ?_⟩
  intro q s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcover, hl, hr⟩ := table_and_resource_pins
  rcases hcover q with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [hl]
    have h : ∀ p s, (route (leftMachine.step p s).1).val ≠ 1 ∧
        (route (leftMachine.step p s).1).val ≠ 2 := by decide
    exact h p s
  · rw [hr]
    change 3 + _ ≠ 1 ∧ 3 + _ ≠ 2
    omega

/-- H3 is stationary even at zero allocation; this says nothing about later clamps. -/
theorem h3_stationary {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.step (startConfig B x w).state
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .stay := by
  rw [(entry_pins (B := B) x w).2.2.2.2.2]
  rfl

/-- Scanned-symbol rejection, for arbitrary source configurations, with unchanged whole tape. -/
theorem scanned_reject {N B : Nat} (cH : Config leftMachine.stateCount N B)
    (hstate : cH.state = FixedPairSeparatorHole.qStart)
    (hread : cH.tape cH.head ≠ some true) (s : Nat) :
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine cH) =
      ⟨machine.reject, cH.head, cH.tape⟩ := by
  have he : leftMachine.run 1 cH = ⟨leftMachine.reject, cH.head, cH.tape⟩ :=
    FixedPairSeparatorHole.stepConfig_start_non_separator cH hstate hread
  have h := leftMachine.seq_reject_handoff tailMachine cH (congrArg Config.state he) s
  rw [he] at h
  exact h

/-- Exact inherited H4 endpoint, including the complete configuration embedding. -/
theorem inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (1 + FixedPairTagRemoval.clock a) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w)) ∧
    e.state.val = 12 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w := by
  obtain ⟨-, -, -, he, hq, hh, ht, -⟩ :=
    FixedPairTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w
  have he' := (suffix (B := B) x w (FixedPairTagRemoval.clock a)).trans
    (congrArg (leftMachine.seqEmbedRight tailMachine) he)
  dsimp only
  rw [he']
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem suffix_g3m {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine
        (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
          FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
          (FixedPairOriginShiftAlignmentCountdown.machine.run s
            (FixedPairOriginShiftAlignmentCountdown.startConfig B x w))) := by
  exact (suffix (B := B) x w (FixedPairTagRemoval.clock a + s)).trans
    (congrArg (leftMachine.seqEmbedRight tailMachine)
      ((FixedPairTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.2.2.2.2 s))

/-- Inherited H5–H7 times each gain one; H6 retains head zero and the entire aligned tape. -/
theorem inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m))
      (startConfig B x w)).state.val = 19 ∧
    (let e := machine.run (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m))) (startConfig B x w)
     e.state.val = 45 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3)))))
      (startConfig B x w)).state.val = 49 := by
  have h5 := (FixedPairOriginShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.1
  obtain ⟨h6, -, -, hh, ht, -, -, h7⟩ :=
    FixedPairOriginShiftAlignmentCountdown.inherited_alignment_switch (B := B) x w
  refine ⟨?_, ?_, ?_⟩
  · rw [suffix_g3m, h5]; rfl
  · dsimp only
    rw [suffix_g3m]
    exact ⟨congrArg (fun n => 3 + (9 + n)) h6, hh, ht⟩
  · rw [suffix_g3m]
    exact congrArg (fun n => 3 + (9 + n)) h7

/-- The inherited origin clamp at global time 1 + (R - 2), separately from H4 at 1 + R. -/
theorem inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (1 + (FixedPairTagRemoval.clock a - 2)) (startConfig B x w)
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left := by
  have hpre : FixedPairTagRemoval.clock a - 2 < FixedPairTagRemoval.clock a := by
    unfold FixedPairTagRemoval.clock
    omega
  have hno := FixedPairTagRemoval.noEarlyTerminal (B := B) x w _ hpre
  have hl := (FixedPairTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.1
    _ (Nat.le_of_lt hpre)
  have hc := (FixedPairTagRemoval.boundary_clamps (B := B) x w).2.2
  dsimp only
  rw [suffix x w (FixedPairTagRemoval.clock a - 2), hl]
  let cR := FixedPairTagRemoval.machine.run (FixedPairTagRemoval.clock a - 2)
    (FixedPairTagRemoval.startConfig B x w)
  change cR.head.val = 0 ∧ ((leftMachine.seq tailMachine).step
    (leftMachine.seqRight tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqRoute
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine cR.state)) (cR.tape cR.head)).2.2 = .left
  rw [UniformTM.seq_step_right]
  change cR.head.val = 0 ∧
    ((FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seq
      FixedPairTagRemovalShiftAlignmentCountdown.tailMachine).step
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqRoute
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine cR.state) (cR.tape cR.head)).2.2 = .left
  rw [(FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seq_pins
    FixedPairTagRemovalShiftAlignmentCountdown.tailMachine).2.2.2.2.2.2.2.2.2.2.2 _ hno.1 hno.2,
    UniformTM.seq_step_left]
  exact hc

/-- Forward rejection guarantees only, measured from the inherited deadlines. -/
theorem rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (FixedContentTagGate.tagMatches (Fin.append x w) = true →
      gammaZeros? (Fin.append x w) = none →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).state = machine.reject ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).head.val = a + m ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) ∧
    (FixedContentTagGate.tagMatches (Fin.append x w) = false →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).state = machine.reject ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) := by
  constructor
  · intro htag hg s hle
    obtain ⟨hr, hh, ht⟩ :=
      (FixedPairOriginShiftAlignmentCountdown.malformed_reject_handoff x w htag hg).2 s hle
    rw [suffix_g3m]
    exact ⟨congrArg (fun q => leftMachine.seqRight tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine q)) hr, hh, ht⟩
  · intro htag s hle
    obtain ⟨hr, hh, ht⟩ :=
      FixedPairOriginShiftAlignmentCountdown.mismatched_tag_reject_handoff x w htag s hle
    rw [suffix_g3m]
    exact ⟨congrArg (fun q => leftMachine.seqRight tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine q)) hr, hh, ht⟩

end Pnp3.Complexity.Uniform.V1.FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown
