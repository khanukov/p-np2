import Complexity.Uniform.V1.FixedRawLengthFenceSuffix
import Complexity.Uniform.V1.FixedRawLengthFenceOverflowWitness

/-! G3t Infrastructure: full public propositions and actual raw executions. -/
namespace Pnp3.Tests.UniformV1FixedRawLengthFenceSuffixSurfaceTests
open Complexity.Uniform.V1 Complexity.Uniform.V1.PairEncoding Complexity.Uniform.V1.FixedRawLengthFence
open FixedGammaTargetRegisterDecrement (borrow decBit)

theorem check_raw_fenced_h17_exact {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w)) =
      fencedDecrementConfig x w hg hroom :=
  raw_fenced_h17_exact x w hroom htag hg hz hfirst

theorem check_raw_fenced_h17_trace {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    ∀ t, t ≤ contentClock a m+h17SuffixClock C (a+m) zeros (borrow x w zeros) →
      let c := prefixed.run (installClock (pairLength a m)+t) (initialConfig prefixed B (encodePair x w))
      c.head.val ≤ 3*(a+m) ∧
      (∀ p : Fin (tapeLength (pairLength a m) B), p.val = fencePos (pairLength a m) → c.tape p = some false) ∧
      c.state ≠ prefixed.accept ∧ c.state ≠ prefixed.reject :=
  raw_fenced_h17_trace x w hroom htag hg hz hfirst

theorem check_raw_fenced_h17_cells {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    let e := prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w))
    (∀ j : Nat, j ≤ zeros → a+m+1+j < tapeLength (pairLength a m) B ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+1+j →
        e.tape i = some (decBit x w zeros (borrow x w zeros) j)) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), (i.val = a+m ∨ i.val = a+m+2+zeros) → e.tape i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+zeros ≤ i.val → i.val < fencePos (pairLength a m) → e.tape i = none) :=
  raw_fenced_h17_cells x w hroom htag hg hz hfirst

theorem check_h17_clock_bound {a m zeros C d : Nat} (hwidth : 9+zeros ≤ a+m) (hz : 2 ≤ zeros)
    (hd : d ≤ zeros) (hC : C ≤ 2*(a+m)*(a+m)) :
    h17RawClock a m zeros C d ≤ h17Deadline (pairLength a m) :=
  h17_clock_bound hwidth hz hd hC

theorem check_raw_fenced_h17_allocated {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) (hz : 2 ≤ zeros) :
    let B := allocation (pairLength a m)
    ∃ (C : Nat) (q : Fin FixedGammaPayloadDispatcher.stateCount), C ≤ 2*(a+m)*(a+m) ∧
      FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q ∧
      h17RawClock a m zeros C (borrow x w zeros) ≤ h17Deadline (pairLength a m) ∧
      prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w)) =
        fencedDecrementConfig x w hg (resource_bounds (pairLength a m)).1 :=
  raw_fenced_h17_allocated x w htag hg hz

theorem check_suffix_head_bound {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    ∀ t, t ≤ h17SuffixClock C (a+m) zeros (borrow x w zeros) →
      (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run t
        (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)).head.val ≤ 3*(a+m) :=
  suffix_head_bound x w hroom htag hg hz hfirst

/-- The independently executed G3s endpoint, now reached by the new universal theorem. -/
theorem check_overflow_h17_from_generic :
    prefixed.run 2335 (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨⟨245,by decide⟩,⟨25,by decide⟩,overflowTape 62 0⟩ := by
  have h := raw_fenced_h17_exact (B := 45) overflowX overflowW (by decide)
    overflow_values.1 overflow_values.2.1 (by decide) overflow_values.2.2.1
  change prefixed.run 2335 _ = _ at h
  rw [h]; apply Config.ext_parts (by rfl) (by rfl); funext i
  fin_cases i <;> decide

private def emptyX : Bitstring 0 := Fin.elim0
private def physicalZero : Bitstring 13 := ![true,false,true,true,false,false,true,false,false,false,true,false,false]
private def virtualWord : Bitstring 11 := ![true,false,true,true,false,false,true,false,false,false,true]
private def pendingWord : Bitstring 13 := ![true,false,true,true,false,false,true,false,false,false,true,false,true]

/-- Width two, zero loop rounds, two physical zero payload bits, and a full two-cell borrow. -/
theorem check_width_two_physical_zero_payload :
    prefixed.run 1082 (initialConfig prefixed 30 (encodePair emptyX physicalZero)) =
      ⟨⟨245,by decide⟩,⟨14,by decide⟩,fencedDecTape 30 emptyX physicalZero 2⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.exhausted_strict_first_terminal
    (B := 30) (zeros := 2) emptyX physicalZero (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j <;> decide)).1
  exact raw_fenced_h17_exact (zeros := 2) (C := 30) emptyX physicalZero (by decide) (by decide) (by decide) (by decide) hf

/-- Width two with no physical payload, at both minimal and strictly larger allocations. -/
theorem check_width_two_virtual_payload :
    prefixed.run 842 (initialConfig prefixed 26 (encodePair emptyX virtualWord)) =
      ⟨⟨245,by decide⟩,⟨12,by decide⟩,fencedDecTape 26 emptyX virtualWord 2⟩ ∧
    prefixed.run 842 (initialConfig prefixed 40 (encodePair emptyX virtualWord)) =
      ⟨⟨245,by decide⟩,⟨12,by decide⟩,fencedDecTape 40 emptyX virtualWord 2⟩ := by
  constructor
  · exact raw_fenced_h17_exact (zeros := 2) (C := 12) emptyX virtualWord (by decide) (by decide) (by decide) (by decide)
      (FixedGammaPayloadDispatcherFirstArrival.first_virtual_strict_first_terminal
        (zeros := 2) emptyX virtualWord (by decide) (by decide) (by decide) (by decide)).1
  · exact raw_fenced_h17_exact (zeros := 2) (C := 12) emptyX virtualWord (by decide) (by decide) (by decide) (by decide)
      (FixedGammaPayloadDispatcherFirstArrival.first_virtual_strict_first_terminal
        (zeros := 2) emptyX virtualWord (by decide) (by decide) (by decide) (by decide)).1

/-- The second physical payload bit is true: the positive pending path k=1 really executes. -/
theorem check_pending_dispatcher_h17 :
    prefixed.run 1073 (initialConfig prefixed 30 (encodePair emptyX pendingWord)) =
      ⟨⟨245,by decide⟩,⟨16,by decide⟩,fencedDecTape 30 emptyX pendingWord 2⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 30) (zeros := 2) (k := 1) emptyX pendingWord (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j; decide) (by decide)).1
  exact raw_fenced_h17_exact (zeros := 2) (C := 23) emptyX pendingWord (by decide) (by decide) (by decide) (by decide) hf
end Pnp3.Tests.UniformV1FixedRawLengthFenceSuffixSurfaceTests
