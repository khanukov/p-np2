import Complexity.Uniform.V1.FixedRawLengthFenceContent
import Complexity.Uniform.V1.FixedGammaSuffixFootprint
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decClock decTape decBit register_decremented deadline clock_pins borrow_pins)
private abbrev Gate := FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine
private abbrev gateStart := @FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
-- Frozen numeric clocks (ordinary Nat subtraction).
def h17RawClock (a m z C d : Nat) := installClock (pairLength a m)+contentClock a m+h17SuffixClock C (a+m) z d

-- Actual suffix composition; no countdown iteration/value/room premise.
private theorem suffix_endpoint {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    Gate.run (h17SuffixClock C (a+m) zeros (borrow x w zeros)) (gateStart B x w) =
      ⟨⟨136, by decide⟩, ⟨a+m+1+zeros-borrow x w zeros, by
        have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
        simp only [tapeLength,pairLength] at *; omega⟩, decTape B x w zeros (borrow x w zeros)⟩ := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1; omega
  have hr : a+m+2+zeros < tapeLength (pairLength a m) B := by simp only [tapeLength,pairLength] at *; omega
  have hside := FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.side_premises_of_strictFirstTerminalAt x w htag hg hfirst
  have h0 := (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag).2.2.2
  have h1 := (FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg).2.2.2
  have h2 := (FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg).2.2.2
  have h3 := (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_of_first_terminal (B := B) x w hfirst hside.2 hside.1).2.2.2
  have h4 := (FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg).2.2.2
  have h5 := (FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg (by omega) (by omega)).2.2.2
  have h6 := (FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)).2.2.2
  have h7 := (FixedGammaTargetMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)).2.2.2
  have h8 := (FixedGammaTargetLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)).2.2.2
  have h9 := (FixedGammaTargetDecrementCountdown.handoff_exact (B := B) x w htag hg hz hr).2.2.1
  simp only [h17SuffixClock,h16SuffixClock,Nat.add_assoc]
  simp only [FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime,FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime,
    FixedContentGammaAnchor.successTime, FixedGammaTerminatorScratchBootstrap.exactClock,
    FixedGammaTargetFirstPayload.exactClock, if_neg (by omega : zeros ≠ 0),
    FixedGammaTargetSecondPayload.exactClock, if_pos hz, FixedGammaTargetPayloadLoopFoundation.exactClock] at h0 h1 h2 h4 h5 h6 h7
  simp only [Nat.add_assoc] at h0 h1 h2 h7
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  have hd := register_decremented x w htag hg hz hr
  have hdead := hd.2.2.2.2.2 (deadline (a+m)) ((clock_pins (a+m) zeros (borrow x w zeros)).2.2.2.2 hf (borrow_pins x w zeros).1)
  apply Config.ext_parts (by rfl)
  · apply Fin.ext
    change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a+m)) (FixedGammaTargetRegisterDecrement.startConfig B x w)).head.val = _
    rw [hdead]; simpa only [Nat.add_assoc] using hd.2.1
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a+m)) (FixedGammaTargetRegisterDecrement.startConfig B x w)).tape = _
    rw [hdead]; exact hd.2.2.1

private def liftH7 {R B : Nat} (c : Config Gate.stateCount R B) : Config prefixed.stateCount R B :=
  FixedRawLengthFence.machine.seqEmbedRight G (
  FixedPairConcatSentinel.machine.seqEmbedRight FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairSeparatorCursor.machine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairSeparatorHole.machine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairTagRemoval.machine.seqEmbedRight FixedPairTagRemovalShiftAlignmentCountdown.tailMachine (
  FixedPairOriginShiftBootstrap.machine.seqEmbedRight FixedPairOriginShiftAlignmentCountdown.tailMachine (
  FixedPairOriginAlignment.machine.seqEmbedRight FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailMachine (
  FixedPairContentMarkerErase.machine.seqEmbedRight FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailMachine (
  c))))))))
private theorem raw_h7_embedding {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2*pairLength a m+2 ≤ B) (s : Nat) :
    prefixed.run (installClock (pairLength a m)+contentClock a m+s) (initialConfig prefixed B (encodePair x w)) =
      liftH7 (Gate.run s {gateStart B x w with tape := fencedContentTape B x w}) := by
  rw [prefixed.run_add, raw_fenced_content_exact x w hroom]
  have he : (⟨⟨109, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
      fencedContentTape B x w⟩ : Config prefixed.stateCount (pairLength a m) B) =
      liftH7 {gateStart B x w with tape := fencedContentTape B x w} := by rfl
  rw [he]
  simp only [liftH7, prefixed,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairTagRemovalShiftAlignmentCountdown.machine,
    FixedPairOriginShiftAlignmentCountdown.machine,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    UniformTM.seq_run_right]


def h17Deadline (R : Nat) : Nat := 32*(R+1)^2

def fencedDecTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = fencePos (pairLength a m) then some false else decTape B x w zeros (borrow x w zeros) i

def fencedDecrementConfig {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : 2*pairLength a m+2 ≤ B) : Config prefixed.stateCount (pairLength a m) B :=
  ⟨⟨245, by decide⟩, ⟨a+m+1+zeros-borrow x w zeros, by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    simp only [tapeLength,pairLength] at *; omega⟩, fencedDecTape B x w zeros⟩

private def fenceIndex {R B : Nat} (hroom : 2*R+2 ≤ B) : Fin (tapeLength R B) :=
  ⟨fencePos R, by simp only [fencePos,tapeLength]; omega⟩

private theorem gate_fenced_run {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (t : Nat) (ht : t ≤ h17SuffixClock C (a+m) zeros (borrow x w zeros)) :
    Gate.run t {gateStart B x w with tape := fencedContentTape B x w} =
      {(Gate.run t (gateStart B x w)) with tape := Function.update (Gate.run t (gateStart B x w)).tape (fenceIndex hroom) (some false)} := by
  have he : {gateStart B x w with tape := fencedContentTape B x w} =
      {gateStart B x w with tape := Function.update (gateStart B x w).tape (fenceIndex hroom) (some false)} := by
    apply Config.ext_parts (by rfl) (by rfl); funext i
    change fencedContentTape B x w i = Function.update (FixedPairContentMarkerErase.contentTape B x w) _ _ i
    by_cases hi : i.val < a+m
    · have hn : i.val ≠ fencePos (pairLength a m) := by simp only [fencePos,pairLength]; omega
      simp [fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Fin.ext_iff,fenceIndex,hn]
    · simp [fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Function.update_apply,Fin.ext_iff,fenceIndex]
  rw [he]; apply Gate.run_update_of_unvisited
  intro r hr hp
  have hb := suffix_head_bound x w hroom htag hg hz hfirst r (by omega)
  have hv := congrArg Fin.val hp
  change (Gate.run r (gateStart B x w)).head.val = fencePos (pairLength a m) at hv
  have hpf : 3*(a+m) < fencePos (pairLength a m) := by simp only [fencePos,pairLength]; omega
  exact (ne_of_lt (lt_of_le_of_lt hb hpf)) hv

/-- Exact whole raw configuration at countdown entry; no countdown steps are asserted. -/
theorem raw_fenced_h17_exact {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w)) =
      fencedDecrementConfig x w hg hroom := by
  rw [h17RawClock,raw_h7_embedding x w hroom,gate_fenced_run x w hroom htag hg hz hfirst _ le_rfl,
    suffix_endpoint x w hroom htag hg hz hfirst]
  apply Config.ext_parts (by rfl) (by rfl); funext i
  change Function.update (decTape B x w zeros (borrow x w zeros)) (fenceIndex hroom) (some false) i = fencedDecTape B x w zeros i
  simp [Function.update_apply,fencedDecTape,Fin.ext_iff,fenceIndex]

theorem raw_fenced_h17_trace {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    ∀ t, t ≤ contentClock a m+h17SuffixClock C (a+m) zeros (borrow x w zeros) →
      let c := prefixed.run (installClock (pairLength a m)+t) (initialConfig prefixed B (encodePair x w))
      c.head.val ≤ 3*(a+m) ∧
      (∀ p : Fin (tapeLength (pairLength a m) B), p.val = fencePos (pairLength a m) → c.tape p = some false) ∧
      c.state ≠ prefixed.accept ∧ c.state ≠ prefixed.reject := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1; omega
  have he := raw_fenced_h17_exact x w hroom htag hg hz hfirst
  have hn := prefixed.no_terminal_of_le (initialConfig prefixed B (encodePair x w))
    (by rw [he]; change (⟨245, by decide⟩ : Fin prefixed.stateCount) ≠ prefixed.accept; decide)
    (by rw [he]; change (⟨245, by decide⟩ : Fin prefixed.stateCount) ≠ prefixed.reject; decide)
  intro t ht; dsimp only
  have htend : installClock (pairLength a m)+t ≤ h17RawClock a m zeros C (borrow x w zeros) := by unfold h17RawClock; omega
  refine ⟨?_,?_,(hn _ htend).1,(hn _ htend).2⟩
  · by_cases hpre : t ≤ contentClock a m
    · exact (raw_fenced_content_trace x w hroom t hpre).1.trans (by simp only [pairLength]; omega)
    · rw [show installClock (pairLength a m)+t = installClock (pairLength a m)+contentClock a m+(t-contentClock a m) by omega,
        raw_h7_embedding x w hroom,gate_fenced_run x w hroom htag hg hz hfirst _ (by omega)]
      exact suffix_head_bound x w hroom htag hg hz hfirst _ (by omega)
  · intro p hp
    by_cases hpre : t ≤ contentClock a m
    · have h := (raw_fenced_content_trace x w hroom t hpre).2.1
      rw [show p = fenceIndex hroom from Fin.ext hp]; exact h
    · rw [show installClock (pairLength a m)+t = installClock (pairLength a m)+contentClock a m+(t-contentClock a m) by omega,
        raw_h7_embedding x w hroom,gate_fenced_run x w hroom htag hg hz hfirst _ (by omega)]
      change Function.update (Gate.run (t-contentClock a m) (gateStart B x w)).tape (fenceIndex hroom) (some false) p = some false
      rw [show p = fenceIndex hroom from Fin.ext hp]; exact Function.update_self _ _ _

theorem raw_fenced_h17_cells {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    let e := prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w))
    (∀ j : Nat, j ≤ zeros → a+m+1+j < tapeLength (pairLength a m) B ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+1+j →
        e.tape i = some (decBit x w zeros (borrow x w zeros) j)) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), (i.val = a+m ∨ i.val = a+m+2+zeros) → e.tape i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+zeros ≤ i.val → i.val < fencePos (pairLength a m) → e.tape i = none) := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1; omega
  have hd := (borrow_pins x w zeros).1
  have hw := Nat.min_le_right zeros (a+m-9-zeros)
  have blank (i : Fin (tapeLength (pairLength a m) B)) (hi : i.val = a+m ∨ a+m+2+zeros ≤ i.val) :
      decTape B x w zeros (borrow x w zeros) i = none := by
    simp only [decTape,FixedGammaTargetPayloadExhaustion.finishTape,FixedGammaTargetPayloadExhaustion.termWalk,
      FixedGammaTargetPayloadLoopFoundation.walk,FixedPairContentMarkerErase.contentTape]
    split_ifs <;> first | rfl | omega
  dsimp only; rw [raw_fenced_h17_exact x w hroom htag hg hz hfirst]
  change (∀ j, _ → _ ∧ ∀ i, _ → fencedDecTape B x w zeros i = _) ∧
    (∀ i, _ → fencedDecTape B x w zeros i = none) ∧ (∀ i, _ → _ → fencedDecTape B x w zeros i = none)
  refine ⟨?_,?_,?_⟩
  · intro j hj
    refine ⟨by simp only [tapeLength,pairLength] at *; omega,fun i hi => ?_⟩
    rw [fencedDecTape,if_neg (by simp only [fencePos,pairLength]; omega)]
    exact (FixedGammaTargetRegisterDecrement.decTape_pins x w htag hg hd).1 j hj i hi
  · intro i hi; rw [fencedDecTape,if_neg (by simp only [fencePos,pairLength]; omega)]
    exact blank i (by omega)
  · intro i hi hp; rw [fencedDecTape,if_neg (by omega)]; exact blank i (by omega)

/-- A length-only quadratic bound for this valid-tag, width-at-least-two prefix. -/
theorem h17_clock_bound {a m zeros C d : Nat} (hwidth : 9+zeros ≤ a+m) (hz : 2 ≤ zeros)
    (hd : d ≤ zeros) (hC : C ≤ 2*(a+m)*(a+m)) :
    h17RawClock a m zeros C d ≤ h17Deadline (pairLength a m) := by
  have hR : 0 < pairLength a m := by simp [pairLength]
  have hw := Nat.min_le_left zeros (a+m-9-zeros)
  have hwalk := Nat.min_le_right zeros (a+m-9-zeros)
  have hsub : h17SuffixClock C (a+m) zeros d + zeros =
      2*(a+m)*zeros+6*(a+m)+9+d+min zeros (a+m-9-zeros)+C := by
    unfold h17SuffixClock h16SuffixClock decClock FixedGammaTargetPayloadExhaustion.totalClock
      FixedGammaTargetPayloadIteration.loopClock FixedGammaTargetPayloadRound.roundClock
      FixedGammaTargetPayloadExhaustion.exhaustClock FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    have h1 : zeros-2+2= zeros := by omega
    have h2 : 2*(a+m)-7+7=2*(a+m) := by omega
    have h3 : 2*(a+m)-11-zeros+11+zeros=2*(a+m) := by omega
    have h4 : 2*(a+m)+zeros-6+6=2*(a+m)+zeros := by omega
    have h5 : a+m+zeros+d-3+3=a+m+zeros+d := by omega
    nlinarith only [congrArg (fun v => v*(2*(a+m)-7)) h1, congrArg (fun v => zeros*v) h2, h2,h3,h4,h5]
  have hzL : zeros ≤ a+m := by omega
  have hprod : (a+m)*zeros ≤ (a+m)*(a+m) := Nat.mul_le_mul_left _ hzL
  have hs : h17SuffixClock C (a+m) zeros d ≤ 4*(a+m)^2+8*(a+m)+9 := by nlinarith
  simp only [h17RawClock,h17Deadline,installClock,if_neg (by omega : pairLength a m ≠ 0)]
  unfold contentClock pairLength at *
  nlinarith only [hs,Nat.zero_le (a*a),Nat.zero_le (a*m),Nat.zero_le (m*m)]

/-- The fixed allocation supplies room and the actual dispatcher witness. -/
theorem raw_fenced_h17_allocated {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) (hz : 2 ≤ zeros) :
    let B := allocation (pairLength a m)
    ∃ (C : Nat) (q : Fin FixedGammaPayloadDispatcher.stateCount), C ≤ 2*(a+m)*(a+m) ∧
      FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q ∧
      h17RawClock a m zeros C (borrow x w zeros) ≤ h17Deadline (pairLength a m) ∧
      prefixed.run (h17RawClock a m zeros C (borrow x w zeros)) (initialConfig prefixed B (encodePair x w)) =
        fencedDecrementConfig x w hg (resource_bounds (pairLength a m)).1 := by
  dsimp only
  obtain ⟨C,q,hC,hfirst,-⟩ := FixedGammaPayloadDispatcherFirstArrival.tagged_strict_first_terminal
    (B := allocation (pairLength a m)) x w htag
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1; omega
  exact ⟨C,q,hC,hfirst,h17_clock_bound hf hz (borrow_pins x w zeros).1 hC,
    raw_fenced_h17_exact x w (resource_bounds (pairLength a m)).1 htag hg hz hfirst⟩
end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
