import Complexity.Uniform.V1.SequentialComposition
import Complexity.Uniform.V1.FixedPairOriginShiftAlignmentCountdown

/-! G3n Infrastructure: executed H4 into unchanged G3m. This phase-local start
does not execute H1–H3 or raw input. No parser/verifier or P-vs-NP bridge. -/
namespace Pnp3.Complexity.Uniform.V1.FixedPairTagRemovalShiftAlignmentCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

abbrev leftMachine : UniformTM := FixedPairTagRemoval.machine
abbrev tailMachine : UniformTM :=
  FixedPairOriginShiftAlignmentCountdown.machine

abbrev tailStartConfig {a m : Nat}
    (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedPairOriginShiftAlignmentCountdown.startConfig B x w

def machine : UniformTM := leftMachine.seq tailMachine

def inRemoval (q : Fin leftMachine.stateCount) : Fin machine.stateCount :=
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
    (FixedPairTagRemoval.startConfig B x w)

def switchTime (a : Nat) : Nat := a * (a + 5) + 2

def removalChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime a +
    FixedPairOriginShiftAlignmentCountdown.shiftChainClock C a m zeros d v

theorem tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run (switchTime a)
      (FixedPairTagRemoval.startConfig B x w)
    g = FixedPairTagRemoval.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show leftMachine.run (switchTime a) (FixedPairTagRemoval.startConfig B x w) =
      FixedPairTagRemoval.finalConfig B x w from FixedPairTagRemoval.run_encoded_exact B x w]
  exact ⟨rfl, Config.ext_parts rfl rfl rfl⟩

private theorem removal_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime a →
      (leftMachine.run t (FixedPairTagRemoval.startConfig B x w)).state ≠ leftMachine.accept ∧
      (leftMachine.run t (FixedPairTagRemoval.startConfig B x w)).state ≠ leftMachine.reject) ∧
    (leftMachine.run (switchTime a) (FixedPairTagRemoval.startConfig B x w)).state =
      leftMachine.accept ∧
    (∀ t, (leftMachine.run t (FixedPairTagRemoval.startConfig B x w)).state ≠
      leftMachine.reject) := by
  refine ⟨fun t ht => FixedPairTagRemoval.noEarlyTerminal x w t ht,
    (FixedPairTagRemoval.final_literal_fields x w).2.1, fun t => ?_⟩
  by_cases ht : t < switchTime a
  · exact (FixedPairTagRemoval.noEarlyTerminal x w t ht).2
  · have hle : FixedPairTagRemoval.clock a ≤ t := Nat.le_of_not_gt ht
    rw [show t = FixedPairTagRemoval.clock a + (t - FixedPairTagRemoval.clock a) by omega,
      FixedPairTagRemoval.run_after_clock x w]
    exact leftMachine.accept_ne_reject

private theorem suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (switchTime a + s) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailStartConfig B x w)) := by
  rw [(tail_start_at_first_arrival (B := B) x w).2]
  exact leftMachine.seq_handoff tailMachine (FixedPairTagRemoval.startConfig B x w)
    (fun t ht => ((removal_first_arrival (B := B) x w).1 t ht).1)
    (removal_first_arrival (B := B) x w).2.1 s

set_option maxRecDepth 40000 in
/-- All 193 states and 579 rows are the unchanged two tables, with routed left targets. -/
theorem table_and_resource_pins :
    machine.stateCount = 193 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 579 ∧
    machine.start.val = 0 ∧ machine.accept.val = 191 ∧
    machine.reject.val = 192 ∧ tailStart.val = 9 ∧
    (∀ q, (inRemoval q).val = q.val) ∧
    (∀ q, (inTail q).val = 9 + q.val) ∧
    Function.Injective inRemoval ∧ Function.Injective inTail ∧
    (∀ p q, inRemoval p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inRemoval p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inRemoval q) s =
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
  have hcount : machine.stateCount = 9 + tailMachine.stateCount := rfl
  have hlt := q.isLt
  by_cases h : q.val < 9
  · exact Or.inl ⟨⟨q.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨q.val - 9, by omega⟩, Fin.ext (by show q.val = 9 + (q.val - 9); omega)⟩

/-- The sole live accepting row; the accept source's absorbing rows are excluded. -/
theorem accept_rows_unique
    (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q.val = 1 ∧ s = none := by
  revert ha s q
  decide

/-- Exactly seven live rejecting rows, excluding both verdict source states. -/
theorem reject_rows_unique
    (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept)
    (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      (s ≠ none ∧ (q.val = 0 ∨ q.val = 4 ∨ q.val = 5)) ∨
      (q.val = 6 ∧ s = some true) := by
  revert hr ha s q
  decide

/-- H4 executes at the tag-removal clock, with no proposition premises or extra step.
The last conjunct transports every later G3m configuration, including its whole tape. -/
theorem handoff_exact {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let cR := FixedPairTagRemoval.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a → (machine.run t c).state.val < 9) ∧
    (∀ t, t ≤ switchTime a →
      (machine.run t c).state ≠ machine.accept ∧
      (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ switchTime a →
      machine.run t c =
        leftMachine.seqEmbedRouted tailMachine (leftMachine.run t cR)) ∧
    machine.run (switchTime a) c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
    (machine.run (switchTime a) c).state.val = 9 ∧
    (machine.run (switchTime a) c).head.val = 0 ∧
    (machine.run (switchTime a) c).tape =
      FixedPairTagRemoval.compactTape B x w ∧
    (∀ s, machine.run (switchTime a + s) c =
      leftMachine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w))) := by
  intro cR c
  obtain ⟨hno, -, -⟩ := removal_first_arrival (B := B) x w
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
    show (leftMachine.seqRoute tailMachine (leftMachine.run t cR).state).val < 9
    rw [hrw _ (hno t ht).1 (hno t ht).2]
    exact (leftMachine.run t cR).state.isLt
  · rw [hCs]; decide
  · rw [hC]; rfl
  · rw [hC]; rfl

/-- Exact execution and persistence, with G3m's eight hypotheses unchanged.
`v` is supplied in the theorem only; no decoding, runtime fence, or first arrival of
composed accept is claimed. `B` allocates tape and does not bound the run time. -/
theorem tag_removal_countdown_drained
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
    let D := removalChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedPairOriginShiftAlignmentCountdown.shift_alignment_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (removalChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w) = leftMachine.seqEmbedRight tailMachine
        (tailMachine.run
          (FixedPairOriginShiftAlignmentCountdown.shiftChainClock C a m zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) := suffix x w _
  have hstate : (machine.run (removalChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => machine.run_accept_of_le _ hstate ht⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3

end Pnp3.Complexity.Uniform.V1.FixedPairTagRemovalShiftAlignmentCountdown
