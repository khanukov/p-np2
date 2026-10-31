import Complexity.Uniform.V1.TapeFrame
import Complexity.Uniform.V1.FixedRawLengthFenceHandoff

/-!
G3s Infrastructure, generic part. The seven existing phase footprints discharge
the locality premise; the installed fence survives through the content handoff.
The exact capstone starts from raw initialConfig at every sufficient physical
allocation, retains raw-length indices, and supplies state, head and whole tape.
The polynomial bound covers installation plus H1-H7 only. Generic fenced H8-H17,
countdown, parser/GN, model, global resources and ContentVerifierBridge stay open.
-/
namespace Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 40000
set_option maxHeartbeats 800000

namespace FixedRawLengthFence
open PairEncoding

def contentClock (a m : Nat) : Nat := 11*a*a + 10*a*m + 36*a + 13*m + 23

def fencedContentTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if h : i.val < a+m then some (Fin.append x w ⟨i.val,h⟩)
  else if i.val = fencePos (pairLength a m) then some false else none

private theorem join_footprints {L R : UniformTM} {n B T U K : Nat}
    {c : Config (L.seq R).stateCount n B} {cL : Config L.stateCount n B}
    {cR : Config R.stateCount n B}
    (hl : ∀ t, t ≤ T → (L.seq R).run t c = L.seqEmbedRouted R (L.run t cL))
    (hr : ∀ s, (L.seq R).run (T+s) c = L.seqEmbedRight R (R.run s cR))
    (hL : ∀ t, t ≤ T → (L.run t cL).head.val ≤ K)
    (hR : ∀ t, t ≤ U → (R.run t cR).head.val ≤ K) :
    ∀ t, t ≤ T+U → ((L.seq R).run t c).head.val ≤ K := by
  intro t ht
  by_cases h : t ≤ T
  · rw [hl t h]; exact hL t h
  · rw [show t = T+(t-T) by omega, hr]; exact hR (t-T) (by omega)

private theorem g3q_content_footprint {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    ∀ t, t ≤ contentClock a m →
      (G.run t (initialConfig G B (encodePair x w))).head.val ≤ pairLength a m + 1 := by
  have h1 := FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) (encodePair x w)
  have h2 := FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w
  have h3 := FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w
  have h4 := FixedPairTagRemovalShiftAlignmentCountdown.handoff_exact (B := B) x w
  have h5 := FixedPairOriginShiftAlignmentCountdown.handoff_exact (B := B) x w
  have h6 := FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w
  have h7 := FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_exact (B := B) x w
  have b7 : ∀ t, t ≤ a+m+3 →
      (FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine.run t
        (FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig B x w)).head.val ≤ pairLength a m+1 := by
    intro t ht
    rw [h7.2.1 t ht]
    change (FixedPairContentMarkerErase.machine.run t _).head.val ≤ _
    rw [(FixedPairContentMarkerErase.full_footprint x w).1 t ht]
    split <;> simp only [pairLength] <;> omega
  have b6 := join_footprints h6.2.2.1 h6.2.2.2.2 (fun t ht => by
    have hb := (FixedPairOriginAlignment.footprint_through_clock (B := B) x w).1 t ht
    exact hb.trans (Nat.add_le_add_left (Nat.min_le_right B 1) _)) b7
  have b5 := join_footprints h5.2.2.1 h5.2.2.2.2 (fun t ht => by
    have hb := (FixedPairOriginShiftBootstrap.footprint (B := B) x w).1 t ht
    exact hb) b6
  have b4 := join_footprints h4.2.2.1 h4.2.2.2.2.2.2.2 (fun t ht => by
    have hb := (FixedPairTagRemoval.footprint_through_clock (B := B) x w).1 t ht
    exact hb.trans (by simp only [pairLength]; omega)) b5
  have b3 := join_footprints h3.2.2.1 h3.2.2.2.2.2.2.2 (fun t ht => by
    have hb := (FixedPairSeparatorHole.head_fixed_through_clock (B := B) x w t ht).2
    exact le_of_eq_of_le hb (by simp only [pairLength]; omega)) b4
  have b2 := join_footprints h2.2.2.1 h2.2.2.2.2.2.2.2 (fun t ht => by
    have hb := FixedPairSeparatorCursor.head_le_separator_successor_through_clock (B := B) x w t ht
    exact hb.trans (by simp only [pairLength]; omega)) b3
  have b1 := join_footprints h1.2.2.1 h1.2.2.2.2.2.2.2.2 (fun t ht => by
    have hb := FixedPairConcatSentinel.head_le_input_through_clock (B := B) (encodePair x w) t ht
    exact hb.trans (by simp only [pairLength]; omega)) b2
  intro t ht
  apply b1 t
  convert ht using 1
  simp only [contentClock,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairOriginShiftAlignmentCountdown.switchTime,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime, pairLength,
    FixedPairConcatSentinel.clock]
  ring


private theorem content_clock_eq (a m : Nat) : contentClock a m =
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.switchTime (pairLength a m) +
      (FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime a +
        (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a+m+3)))))) := by
  simp only [contentClock,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairConcatSentinel.clock,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.switchTime,
    FixedPairTagRemoval.clock,
    FixedPairOriginShiftAlignmentCountdown.switchTime,
    FixedPairOriginShiftAlignmentCountdown.tailSwitchTime,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime,
    pairLength]
  ring

private theorem unfenced_content_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    G.run (contentClock a m) (initialConfig G B (encodePair x w)) =
      ⟨⟨61, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
  rw [content_clock_eq]
  have hs := (FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_switches (B := B) x w).2.2
  have hf := (FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.inherited_h5_h7_fields (B := B) x w).2
  exact Config.ext_parts (Fin.ext hs) (Fin.ext hf.1) hf.2

private theorem fenced_run {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) (t : Nat) (ht : t ≤ contentClock a m) :
    G.run t (g3qEntry B (encodePair x w)) =
      {G.run t (initialConfig G B (encodePair x w)) with
        tape := Function.update (G.run t (initialConfig G B (encodePair x w))).tape
          ⟨fencePos (pairLength a m), by dsimp [fencePos,tapeLength]; omega⟩ (some false)} := by
  let p : Fin (tapeLength (pairLength a m) B) :=
    ⟨fencePos (pairLength a m), by dsimp [fencePos,tapeLength]; omega⟩
  have entry : g3qEntry B (encodePair x w) =
      {initialConfig G B (encodePair x w) with
        tape := Function.update (initialConfig G B (encodePair x w)).tape p (some false)} := by
    refine Config.ext_parts (by rfl) (by rfl) ?_
    funext i
    by_cases hi : i = p
    · subst i
      simp [g3qEntry,fenceTape,p, fencePos,
        show ¬3 * pairLength a m + 2 < pairLength a m by omega]
    · have hv : i.val ≠ fencePos (pairLength a m) := fun h => hi (Fin.ext h)
      simp [g3qEntry,fenceTape,hi,initialConfig,hv]
  rw [entry]
  apply G.run_update_of_unvisited
  intro s hs hp
  have hb := g3q_content_footprint (B := B) x w s (by omega)
  have hv := congrArg Fin.val hp
  dsimp [p,fencePos] at hv
  omega

private theorem fenced_content_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) :
    G.run (contentClock a m) (g3qEntry B (encodePair x w)) =
      ⟨⟨61, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
        fencedContentTape B x w⟩ := by
  rw [fenced_run x w hroom _ (Nat.le_refl _), unfenced_content_exact]
  refine Config.ext_parts (by rfl) (by rfl) ?_
  funext i
  by_cases hi : i.val < a+m
  · have hn : i.val ≠ fencePos (pairLength a m) := by dsimp [fencePos,pairLength]; omega
    simp [fencedContentTape,
    FixedPairContentMarkerErase.contentTape,
      hi, Fin.ext_iff, hn]
  · simp [Function.update_apply, fencedContentTape,
    FixedPairContentMarkerErase.contentTape,
      hi, Fin.ext_iff]

theorem raw_fenced_content_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) :
    prefixed.run (installClock (pairLength a m) + contentClock a m)
        (initialConfig prefixed B (encodePair x w)) =
      ⟨⟨109, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
        fencedContentTape B x w⟩ := by
  rw [fence_handoff_exact _ hroom, fenced_content_exact x w hroom]
  rfl

theorem raw_fenced_content_trace {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) :
    ∀ t, t ≤ contentClock a m →
      let c := prefixed.run (installClock (pairLength a m)+t)
        (initialConfig prefixed B (encodePair x w))
      c.head.val ≤ pairLength a m+1 ∧
      c.tape ⟨fencePos (pairLength a m), by dsimp [fencePos,tapeLength]; omega⟩ = some false ∧
      c.state ≠ prefixed.accept ∧ c.state ≠ prefixed.reject := by
  have he := raw_fenced_content_exact x w hroom
  have hn := prefixed.no_terminal_of_le (initialConfig prefixed B (encodePair x w))
    (by rw [he]; change (⟨109, by decide⟩ : Fin prefixed.stateCount) ≠ prefixed.accept; decide)
    (by rw [he]; change (⟨109, by decide⟩ : Fin prefixed.stateCount) ≠ prefixed.reject; decide)
  intro t ht
  dsimp only
  refine ⟨?_,?_, (hn _ (Nat.add_le_add_left ht _)).1, (hn _ (Nat.add_le_add_left ht _)).2⟩
  · rw [fence_handoff_exact _ hroom, fenced_run x w hroom t ht]
    exact g3q_content_footprint x w t ht
  · rw [fence_handoff_exact _ hroom, fenced_run x w hroom t ht]
    exact Function.update_self _ _ _

theorem content_prefix_resources (a m : Nat) :
    2 * pairLength a m + 2 ≤ allocation (pairLength a m) ∧
    installClock (pairLength a m) + contentClock a m ≤ allocation (pairLength a m) := by
  refine ⟨(resource_bounds _).1, ?_⟩
  have hn : pairLength a m ≠ 0 := by simp only [pairLength]; omega
  rw [installClock,if_neg hn]
  simp only [contentClock,allocation,pairLength]
  nlinarith [Nat.zero_le (a*a), Nat.zero_le (a*m), Nat.zero_le (m*m)]

end FixedRawLengthFence
end Pnp3.Complexity.Uniform.V1
