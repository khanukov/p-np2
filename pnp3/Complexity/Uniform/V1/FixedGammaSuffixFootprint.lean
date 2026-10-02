import Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
import Complexity.Uniform.V1.BudgetTransport
import Complexity.Uniform.V1.FixedGammaTargetPayloadIteration

/-! G3t Infrastructure: coarse footprints of the actual suffix through countdown entry. -/
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding FixedGammaPayloadDispatcher FixedGammaPayloadDispatcherRounds
open FixedGammaPayloadDispatcherDeadline FixedGammaPayloadDispatcherFirstArrival

private theorem head_from (M : UniformTM) {N B s t : Nat}
    (c : Config M.stateCount N B) (hst : s ≤ t) :
    (M.run t c).head.val ≤ (M.run s c).head.val + (t-s) := by
  have h := M.run_head_le (steps := t-s) (M.run s c)
  rw [← M.run_add, Nat.add_sub_of_le hst] at h
  exact h

private theorem dispatcher_head_bound {a m B zeros C : Nat} {q : Fin stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : StrictFirstTerminalAt B x w C q) :
    ∀ t, t ≤ C → (machine.run t (startConfig B x w)).head.val ≤ 3*(a+m) := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  have h0 : (startConfig B x w).head.val = 8+zeros := by
    simp only [startConfig, FixedContentGammaAnchor.run_deadline x w htag,
      retagG2a, FixedContentGammaAnchor.finalConfig, FixedContentGammaTerminator.terminalIndex, hg]
    simp; omega
  have cut {D : Nat} {r : Fin stateCount} (h : StrictFirstTerminalAt B x w D r) : C ≤ D := by
    by_contra hn
    exact hfirst.2.2 D (by omega) (by rw [h.1]; exact h.2.1)
  have early : ∀ k, k ≤ zeros →
      (∀ j, 9+zeros ≤ j → j < 9+zeros+k →
        FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) →
      ∀ t, t ≤ (k+1)*(2*zeros+4) →
        (machine.run t (startConfig B x w)).head.val ≤ 3*(a+m) := by
    intro k; induction k with
    | zero =>
      intro hk hp t ht
      have h := machine.run_head_le (steps := t) (startConfig B x w)
      rw [h0] at h; simp only [Nat.zero_add, Nat.one_mul] at ht; omega
    | succ k ih =>
      intro hk hp t ht
      by_cases he : t ≤ (k+1)*(2*zeros+4)
      · exact ih (by omega) (by intro j hj hj'; exact hp j hj (by omega)) t he
      · have hcp := (boundary_exact (B := B) x w htag hg (k := k+1) (by omega) hk hp).2.1
        rw [boundaryArrivalClock_eq (by omega)] at hcp
        have h := head_from machine (startConfig B x w) (s := (k+1)*(2*zeros+4)) (by omega : (k+1)*(2*zeros+4) ≤ t)
        have hphys := FixedGammaPayloadRoundDriver.prefix_physical_bound x w (by omega : 1 ≤ k+1) hp
        rw [hcp] at h
        have hspan : (k+1+1)*(2*zeros+4) = (k+1)*(2*zeros+4)+(2*zeros+4) := by ring
        rw [hspan] at ht; omega
  obtain ⟨k, hkz, hp, he⟩ := gamma_payload_first_index (Fin.append x w) hg
  have hp' : ∀ j, 9+zeros ≤ j → j < 9+zeros+k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false := by
    intro j hj hj'; have h := hp (j-(9+zeros)) (by omega)
    simpa only [Nat.add_sub_of_le hj] using h
  intro t ht
  rcases he with he | ⟨hk, htrue⟩ | ⟨hk, hvirt⟩
  · subst k
    have hprefix : ∀ j, 9+zeros ≤ j → j < 9+2*zeros →
        FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false := by
      intro j hj hj'; exact hp' j hj (by omega)
    have hC := cut (exhausted_strict_first_terminal x w htag hg (by omega) hprefix).1
    by_cases he : t ≤ exhaustedArrivalClock zeros
    · apply early zeros (by omega) hp' t
      rw [exhaustedArrivalClock_eq (by omega)] at he; nlinarith
    · have h := head_from machine (startConfig B x w) (s := exhaustedArrivalClock zeros) (by omega : exhaustedArrivalClock zeros ≤ t)
      rw [(exhausted_start_exact x w htag hg (by omega) hprefix).2.1] at h
      have hphys := FixedGammaPayloadRoundDriver.prefix_physical_bound x w (by omega : 1 ≤ zeros) hp'
      simp only [zeroEndClock, FixedGammaPayloadZeroCleanup.cleanupClock] at hC; omega
  · have hphys : 9+zeros+k < a+m := by
      unfold FixedContentTagGate.physicalSymbol at htrue; split at htrue <;> simp_all
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.add_zero] at htrue hphys
      have htrue' : (Fin.append x w) ⟨9+zeros, by omega⟩ = true := by
        simpa [FixedContentTagGate.physicalSymbol, hphys] using htrue
      have hC := cut (first_true_strict_first_terminal x w htag hg (by omega) (by omega) htrue').1
      by_cases he : t ≤ 2*zeros+3
      · exact early 0 (by omega) hp' t (by omega)
      · have h := head_from machine (startConfig B x w) (s := 2*zeros+3) (by omega : 2*zeros+3 ≤ t)
        rw [(first_read_exact x w htag hg (by omega)).2] at h; omega
    · have hC := cut (pending_true_strict_first_terminal x w htag hg (by omega) hk hp' htrue).1
      by_cases he : t ≤ pendingArrivalClock zeros k
      · apply early k hkz hp' t; rwa [pendingArrivalClock_eq (by omega)] at he
      · have h := head_from machine (startConfig B x w) (s := pendingArrivalClock zeros k) (by omega : pendingArrivalClock zeros k ≤ t)
        rw [(pending_true_start_exact x w htag hg (by omega) hk hp' htrue).2.1] at h
        simp only [pendingEndClock, FixedGammaPayloadPendingCleanup.cleanupClock] at hC; omega
  · by_cases hk0 : k = 0
    · subst k
      have hC := cut (first_virtual_strict_first_terminal x w htag hg (by omega) (by omega)).1
      by_cases he : t ≤ 2*zeros+3
      · exact early 0 (by omega) hp' t (by omega)
      · have h := head_from machine (startConfig B x w) (s := 2*zeros+3) (by omega : 2*zeros+3 ≤ t)
        rw [(first_read_exact x w htag hg (by omega)).2] at h; omega
    · have hC := cut (pending_virtual_strict_first_terminal x w htag hg (by omega) hk hp' hvirt).1
      by_cases he : t ≤ pendingArrivalClock zeros k
      · apply early k hkz hp' t; rwa [pendingArrivalClock_eq (by omega)] at he
      · have h := head_from machine (startConfig B x w) (s := pendingArrivalClock zeros k) (by omega : pendingArrivalClock zeros k ≤ t)
        rw [(pending_virtual_start_exact x w htag hg (by omega) hk hp' hvirt).2.1] at h
        simp only [pendingEndClock, FixedGammaPayloadPendingCleanup.cleanupClock] at hC; omega

end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence

namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding FixedGammaTargetPayloadRound FixedGammaTargetPayloadLoopFoundation
open FixedGammaTargetPayloadIteration
private theorem iteration_head_bound {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a+m+1+zeros < tapeLength (pairLength a m) B) :
    ∀ t, t ≤ loopClock (a+m) zeros →
      (FixedGammaTargetPayloadRound.machine.run t (FixedGammaTargetPayloadRound.startConfig B x w)).head.val ≤ 3*(a+m) := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  have checkpoint (k : Nat) (hk : 2+k ≤ zeros) :
      (FixedGammaTargetPayloadRound.machine.run (k*roundClock (a+m)) (FixedGammaTargetPayloadRound.startConfig B x w)).head.val < a+m := by
    rw [(rounds_iterate x w htag hg hz hroom k hk).2.1]
    have hw := Nat.min_le_right (2+k) (a+m-9-zeros)
    unfold walk; omega
  intro t ht
  by_cases he : t = (zeros-2)*roundClock (a+m)
  · subst t; have h := checkpoint (zeros-2) (by omega); omega
  · have hr : 0 < roundClock (a+m) := by unfold roundClock; omega
    have hlt : t < (zeros-2)*roundClock (a+m) := by unfold loopClock at ht; omega
    have hk : t / roundClock (a+m) < zeros-2 := (Nat.div_lt_iff_lt_mul hr).2 hlt
    have hbase := Nat.div_mul_le_self t (roundClock (a+m))
    have h := head_from FixedGammaTargetPayloadRound.machine (FixedGammaTargetPayloadRound.startConfig B x w) hbase
    have hc := checkpoint (t / roundClock (a+m)) (by omega)
    have hm := Nat.mod_lt t hr
    have hdiv := Nat.mod_add_div t (roundClock (a+m))
    have heq : roundClock (a+m) = 2*(a+m)-7 := rfl
    rw [Nat.mul_comm (roundClock (a+m))] at hdiv
    omega
end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence

namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding FixedGammaTargetRegisterDecrement

def h16SuffixClock (C L zeros : Nat) : Nat :=
  (3*L+7)+(zeros+1)+(2*zeros+5)+C+(2*L-11-zeros)+(2*L+zeros-6)+(2*L-7)+(zeros+7)+FixedGammaTargetPayloadExhaustion.totalClock L zeros
def h17SuffixClock (C L zeros d : Nat) : Nat := h16SuffixClock C L zeros + decClock L zeros d

private theorem total_head_bound {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hf : 9+zeros ≤ a+m)
    (hr : a+m+1+zeros < tapeLength (pairLength a m) B) :
    ∀ t, t ≤ FixedGammaTargetPayloadExhaustion.totalClock (a+m) zeros →
      (FixedGammaTargetPayloadRound.machine.run t (FixedGammaTargetPayloadRound.startConfig B x w)).head.val ≤ 3*(a+m) := by
  intro t ht
  by_cases he : t ≤ FixedGammaTargetPayloadIteration.loopClock (a+m) zeros
  · exact iteration_head_bound x w htag hg hz hr t he
  · have h := head_from FixedGammaTargetPayloadRound.machine (FixedGammaTargetPayloadRound.startConfig B x w) (Nat.le_of_not_ge he)
    have hc := (FixedGammaTargetPayloadIteration.rounds_iterate x w htag hg hz hr (zeros-2) (by omega)).2.1
    change (FixedGammaTargetPayloadRound.machine.run (FixedGammaTargetPayloadIteration.loopClock (a+m) zeros) _).head.val = _ at hc
    rw [hc] at h
    have hw := Nat.min_le_right zeros (a+m-9-zeros)
    simp only [FixedGammaTargetPayloadExhaustion.totalClock, FixedGammaTargetPayloadExhaustion.exhaustClock,
      FixedGammaTargetPayloadExhaustion.termWalk, FixedGammaTargetPayloadLoopFoundation.walk,
      show 2+(zeros-2)=zeros by omega] at h ht
    omega

private theorem decrement_head_bound {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hf : 9+zeros ≤ a+m)
    (hr : a+m+2+zeros < tapeLength (pairLength a m) B) :
    ∀ t, t ≤ decClock (a+m) zeros (borrow x w zeros) →
      (machine.run t (startConfig B x w)).head.val ≤ 3*(a+m) := by
  have hp := FixedGammaTargetPayloadExhaustion.payload_exhausted x w htag hg hz (by omega : a+m+1+zeros < tapeLength (pairLength a m) B)
  have he := hp.2.2.2.2.2.2 (priorDeadline (a+m)) (prior_covers hf)
  have hh : (startConfig B x w).head.val = 7 := by change (FixedGammaTargetPayloadRound.machine.run _ _).head.val = _; rw [he]; exact hp.2.1
  have ht : (startConfig B x w).tape = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros := by
    change (FixedGammaTargetPayloadRound.machine.run _ _).tape = _; rw [he]; exact hp.2.2.1
  obtain ⟨hd,hlow,hstop⟩ := borrow_pins x w zeros
  have hs := decrement_schedule x w htag hg hr hd hlow hstop (startConfig B x w) rfl hh ht
  intro t htle
  by_cases heq : t = decClock (a+m) zeros (borrow x w zeros)
  · subst t; rw [(register_decremented x w htag hg hz hr).2.1]; omega
  · by_cases hnav : t ≤ a+m+zeros-5
    · rw [hs.1 t hnav]; omega
    · rw [hs.2.1 t (by omega) (by omega)]; omega

private theorem join_footprints {L R : UniformTM} {n B T U K : Nat}
    {c : Config (L.seq R).stateCount n B} {cL : Config L.stateCount n B} {cR : Config R.stateCount n B}
    (hl : ∀ t, t ≤ T → (L.seq R).run t c = L.seqEmbedRouted R (L.run t cL))
    (hr : ∀ s, (L.seq R).run (T+s) c = L.seqEmbedRight R (R.run s cR))
    (hL : ∀ t, t ≤ T → (L.run t cL).head.val ≤ K)
    (hR : ∀ t, t ≤ U → (R.run t cR).head.val ≤ K) :
    ∀ t, t ≤ T+U → ((L.seq R).run t c).head.val ≤ K := by
  intro t ht
  by_cases h : t ≤ T
  · rw [hl t h]; exact hL t h
  · rw [show t = T+(t-T) by omega, hr]; exact hR (t-T) (by omega)

/-- The entire actual gate suffix stays strictly left of the raw fence through H17. -/
theorem suffix_head_bound {a m B zeros C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hroom : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) :
    ∀ t, t ≤ h17SuffixClock C (a+m) zeros (borrow x w zeros) →
      (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run t
        (FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)).head.val ≤ 3*(a+m) := by
  have hf : 9+zeros ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1; omega
  have hr : a+m+2+zeros < tapeLength (pairLength a m) B := by simp only [tapeLength,pairLength] at *; omega
  have hside := FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.side_premises_of_strictFirstTerminalAt x w htag hg hfirst
  have h0 := FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag
  have h1 := FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg
  have h2 := FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg
  have h3 := FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_of_first_terminal (B := B) x w hfirst hside.2 hside.1
  have h4 := FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg
  have h5 := FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg (by omega) (by omega)
  have h6 := FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)
  have h7 := FixedGammaTargetMarkersLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)
  have h8 := FixedGammaTargetLoopDecrementCountdown.handoff_exact (B := B) x w htag hg hz (by omega)
  have h9 := FixedGammaTargetDecrementCountdown.handoff_exact (B := B) x w htag hg hz hr
  have b9 : ∀ t, t ≤ decClock (a+m) zeros (borrow x w zeros) →
      (FixedGammaTargetDecrementCountdown.machine.run t (FixedGammaTargetDecrementCountdown.startConfig B x w)).head.val ≤ 3*(a+m) := by
    intro t ht; rw [h9.2.1 t ht]; exact decrement_head_bound x w htag hg hz hf hr t ht
  have b8 := join_footprints h8.2.1 h8.2.2.2 (total_head_bound x w htag hg hz hf (by omega)) b9
  have b7 := join_footprints h7.2.1 h7.2.2.2 (fun t ht => by
    have h := FixedGammaTargetPayloadLoopFoundation.machine.run_head_le (steps := t) (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)
    have hh := (FixedGammaTargetSecondPayload.second_payload_exact x w htag hg hz (by omega : a+m+3 < tapeLength (pairLength a m) B)
      (FixedGammaTargetSecondPayload.deadline (a+m)) (FixedGammaTargetSecondPayload.exactClock_le_deadline (by omega))).2.1
    change (FixedGammaTargetPayloadLoopFoundation.startConfig B x w).head.val = 7 at hh
    rw [hh] at h; change t ≤ zeros+7 at ht; omega) b8
  have b6 := join_footprints h6.2.1 h6.2.2.2 (fun t ht => by
    have h := (FixedGammaTargetSecondPayload.positive_width_head_range x w htag hg hz (by omega : a+m+3 < tapeLength (pairLength a m) B) t).2; omega) b7
  have b5 := join_footprints h5.2.1 h5.2.2.2 (fun t ht => by
    have h := (FixedGammaTargetFirstPayload.footprint (B := B) x w htag hg (fun _ => by omega) t).2.1
    rw [if_neg (by omega : zeros ≠ 0)] at h; omega) b6
  have b4 := join_footprints h4.2.1 h4.2.2.2 (fun t ht => by
    have h := (FixedGammaTerminatorScratchBootstrap.footprint (B := B) x w htag hg t).2.1; omega) b5
  have b3 : ∀ t, t ≤ C+(FixedGammaTerminatorScratchBootstrap.exactClock (a+m) zeros + (FixedGammaTargetFirstPayload.exactClock (a+m) zeros + (FixedGammaTargetSecondPayload.exactClock (a+m) zeros + (FixedGammaTargetPayloadLoopFoundation.exactClock zeros + (FixedGammaTargetPayloadExhaustion.totalClock (a+m) zeros + decClock (a+m) zeros (borrow x w zeros)))))) →
      (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run t (FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)).head.val ≤ 3*(a+m) := by
    intro t ht
    by_cases hc : t ≤ C
    · rw [h3.2.1 t hc]; exact dispatcher_head_bound x w htag hg hz hfirst t hc
    · rw [show t = C+(t-C) by omega,h3.2.2.2]; exact b4 (t-C) (by omega)
  have b2 := join_footprints h2.2.1 h2.2.2.2 (fun t ht => by
    have h := ((FixedContentGammaAnchor.execution_safety x w htag).1 B t
      (ht.trans (FixedContentGammaAnchor.successTime_le_deadline x w hg))).2.1; omega) b3
  have b1 := join_footprints h1.2.1 h1.2.2.2 (fun t ht => by
    have h := (FixedContentGammaTerminator.phase_contract x w htag).1 B t (by
      change t ≤ a+m-7; change t ≤ zeros+1 at ht; omega); omega) b2
  have b0 := join_footprints h0.2.1 h0.2.2.2 (fun t ht => by
    have h := (FixedContentTagGate.phase_contract x w).1 B t ht; omega) b1
  intro t ht; apply b0 t
  simpa only [h17SuffixClock,h16SuffixClock,
FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime,FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime,
    FixedContentGammaAnchor.successTime, FixedGammaTerminatorScratchBootstrap.exactClock,
    FixedGammaTargetFirstPayload.exactClock, if_neg (by omega : zeros ≠ 0), FixedGammaTargetSecondPayload.exactClock,
    if_pos hz, FixedGammaTargetPayloadLoopFoundation.exactClock, Nat.add_assoc] using ht
end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
