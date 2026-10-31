import Complexity.Uniform.V1.FixedRawLengthFenceSuffix
import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration
import Complexity.Uniform.V1.TapeFrame

/-! G3u Infrastructure. Generic strict capacity for the unchanged raw fenced machine.
The local proofs frame the installed false cell using proved head bounds. The public
capstones start at raw initialConfig, through the actual G3t H17 predecessor. -/
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (qStart qLoop qRunEnd qDone qReject loopTape roundClock zeroClock)
open FixedGammaTargetUnaryCountdownIteration (roundsClock fullClock high_iff_lt)
private abbrev U := FixedGammaTargetUnaryCountdown.machine

private theorem high_sub {v z : Nat} (h : ∀ b, z < b → v.testBit b = false) (k : Nat) :
    ∀ b, z < b → (v-k).testBit b = false :=
  (high_iff_lt (v-k) z).2 (lt_of_le_of_lt (Nat.sub_le v k) ((high_iff_lt v z).1 h))

/-- Number of tally cells strictly before the installed raw-length fence. -/
def capacity (a m z : Nat) : Nat := fencePos (pairLength a m) - (a+m+3+z)
/-- Expected full tape, retaining the original installed false fence. -/
def countdownTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z v r : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = fencePos (pairLength a m) then some false else loopTape B x w z v r i

def countdownSuccessClock (a m z C d v : Nat) : Nat :=
  h17RawClock a m z C d + fullClock z d v
def countdownRejectClock (a m z C d : Nat) : Nat :=
  h17RawClock a m z C d + (d+2) + roundsClock z 0 (capacity a m z) +
    (2*z+capacity a m z+6)
def countdownDeadline (R : Nat) : Nat := 128*(R+1)^2

private theorem geometry {a m B z : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) :
    9+z ≤ a+m ∧ a+m+3+z+capacity a m z = fencePos (pairLength a m) ∧
    fencePos (pairLength a m) < tapeLength (pairLength a m) B := by
  have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1
  simp only [capacity,fencePos,pairLength,tapeLength] at *; omega

private def frame {n B : Nat} (p : Fin (tapeLength n B)) (c : Config U.stateCount n B) :=
  {c with tape := Function.update c.tape p (some false)}
private theorem frame_run {n B : Nat} (p : Fin (tapeLength n B))
    (c : Config U.stateCount n B) (T : Nat)
    (hb : ∀ t, t < T → (U.run t c).head.val < p.val) :
    U.run T (frame p c) = frame p (U.run T c) :=
  U.run_update_of_unvisited c p (some false) T
    (fun t ht he => (ne_of_lt (hb t ht)) (congrArg Fin.val he))

private theorem frame_source {a m B z v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (p : Fin (tapeLength (pairLength a m) B)) (hp : p.val = fencePos (pairLength a m))
    (c : Config U.stateCount (pairLength a m) B) (ht : c.tape = countdownTape B x w z v r) :
    frame p {c with tape := loopTape B x w z v r} = c := by
  apply Config.ext_parts (by rfl) (by rfl)
  rw [ht]; funext i
  simp [frame,Function.update_apply,countdownTape,Fin.ext_iff,hp]
private theorem frame_tape {a m B z v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (p : Fin (tapeLength (pairLength a m) B)) (hp : p.val = fencePos (pairLength a m))
    (c : Config U.stateCount (pairLength a m) B) (ht : c.tape = loopTape B x w z v r) :
    (frame p c).tape = countdownTape B x w z v r := by
  funext i
  simp [frame,ht,Function.update_apply,countdownTape,Fin.ext_iff,hp]

private theorem framed_execution {a m B z v r v' r' : Nat} (x : Bitstring a) (w : Bitstring m)
    (p : Fin (tapeLength (pairLength a m) B)) (hp : p.val = fencePos (pairLength a m))
    (c : Config U.stateCount (pairLength a m) B) (ht : c.tape = countdownTape B x w z v r)
    (T : Nat) (q : Fin U.stateCount) (h : Nat)
    (he : let e := U.run T {c with tape := loopTape B x w z v r}
      e.state = q ∧ e.head.val = h ∧ e.tape = loopTape B x w z v' r')
    (hb : ∀ t, t < T → (U.run t {c with tape := loopTape B x w z v r}).head.val < p.val) :
    let e := U.run T c
    e.state = q ∧ e.head.val = h ∧ e.tape = countdownTape B x w z v' r' := by
  have hf := frame_run p {c with tape := loopTape B x w z v r} T hb
  rw [frame_source x w p hp c ht] at hf
  rw [hf]
  exact ⟨he.1,he.2.1,frame_tape x w p hp _ he.2.2⟩

private theorem fenced_entry {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (c : Config U.stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+1+z-borrow x w z) (ht : c.tape = countdownTape B x w z v 0) :
    let e := U.run (borrow x w z+2) c
    e.state = qLoop ∧ e.head.val = a+m+2+z ∧ e.tape = countdownTape B x w z v 0 := by
  obtain ⟨hw,hp,hfit⟩ := geometry x w hg hr
  let p : Fin (tapeLength (pairLength a m) B) := ⟨fencePos (pairLength a m),hfit⟩
  let u := {c with tape := loopTape B x w z v 0}
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1
  have hl : ∀ b, b < borrow x w z → v.testBit b = true := by
    intro b hb
    have h := hv (z-b) (by omega)
    rw [show z-(z-b)=b by omega] at h
    rw [h]; unfold decBit; rw [if_neg (by omega),if_neg (by omega)]
  have hs : v.testBit (borrow x w z) = false := by
    have h := hv (z-borrow x w z) (by omega)
    rw [show z-(z-borrow x w z)=borrow x w z by omega] at h
    rw [h]; unfold decBit; rw [if_neg (by omega),if_pos rfl]
  have hroom : a+m+2+z < tapeLength (pairLength a m) B := by omega
  have he := FixedGammaTargetUnaryCountdown.entry_generic x w hroom hd hl hs u hq hh rfl
  have hb := FixedGammaTargetUnaryCountdown.entry_head_bound x w hroom hd hl hs u hq hh rfl
  have hf := frame_run p u (borrow x w z+2) (fun t ht => lt_of_le_of_lt (hb t (by omega)) (by dsimp [p]; omega))
  rw [frame_source x w p rfl c ht] at hf
  rw [hf]
  exact ⟨he.1,he.2.1,frame_tape x w p rfl _ he.2.2⟩

section
-- Prevent elaboration from expanding a symbolic run while matching the framing equation.
attribute [local irreducible] UniformTM.run
private theorem fenced_round {a m B z v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) (hcap : r < capacity a m z) (hv : 1 ≤ v)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (c : Config U.stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z v r) :
    let e := U.run (roundClock z r) c
    e.state = qLoop ∧ e.head.val = a+m+2+z ∧ e.tape = countdownTape B x w z (v-1) (r+1) := by
  obtain ⟨hw,hp,hfit⟩ := geometry x w hg hr
  let p : Fin (tapeLength (pairLength a m) B) := ⟨fencePos (pairLength a m),hfit⟩
  let u := {c with tape := loopTape B x w z v r}
  have he := FixedGammaTargetUnaryCountdown.round_traced (zeros := z) (v := v) (r := r) x w (by omega) hv hhigh u hq hh rfl
  exact framed_execution (z := z) (v := v) (r := r) (v' := v-1) (r' := r+1) x w p rfl c ht (roundClock z r) qLoop (a+m+2+z) he.1
    (fun t ht => lt_of_le_of_lt (he.2.2.2 t (by omega)) (by dsimp [p]; omega))

end

private theorem fenced_rounds {a m B z : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) :
    ∀ k v r, r+k ≤ capacity a m z → k ≤ v → (∀ b, z < b → v.testBit b = false) →
    ∀ c : Config U.stateCount (pairLength a m) B, c.state = qLoop →
    c.head.val = a+m+2+z → c.tape = countdownTape B x w z v r →
    let e := U.run (roundsClock z r k) c
    e.state = qLoop ∧ e.head.val = a+m+2+z ∧ e.tape = countdownTape B x w z (v-k) (r+k) := by
  intro k
  induction k with
  | zero => intro v r _ _ _ c hq hh ht; simpa [roundsClock] using And.intro hq (And.intro hh ht)
  | succ k ih =>
    intro v r hc hk hv c hq hh ht
    obtain ⟨heq,heh,het⟩ := fenced_round x w hg hr (by omega) (by omega) hv c hq hh ht
    have he := ih (v-1) (r+1) (by omega) (by omega) (high_sub hv 1) _ heq heh het
    have hclock : roundsClock z r (k+1) = roundClock z r + roundsClock z (r+1) k := by
      unfold roundsClock roundClock; ring
    dsimp only; rw [hclock,U.run_add]
    simpa only [show v-1-k=v-(k+1) by omega,show r+1+k=r+(k+1) by omega] using he

private theorem fenced_exhaust {a m B z r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B)
    (c : Config U.stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z 0 r) :
    let e := U.run (zeroClock z) c
    e.state = qDone ∧ e.head.val = a+m+2+z ∧ e.tape = countdownTape B x w z 0 r := by
  obtain ⟨hw,hp,hfit⟩ := geometry x w hg hr
  let p : Fin (tapeLength (pairLength a m) B) := ⟨fencePos (pairLength a m),hfit⟩
  let u := {c with tape := loopTape B x w z 0 r}
  have he := FixedGammaTargetUnaryCountdown.exhaust_traced x w (by omega) u hq hh rfl
  have hf := frame_run p u (zeroClock z) (fun t ht => lt_of_le_of_lt (he.2 t (by omega)) (by dsimp [p]; omega))
  rw [frame_source x w p rfl c ht] at hf
  rw [hf]
  exact ⟨he.1.1,he.1.2.1,frame_tape x w p rfl _ he.1.2.2.1⟩

private theorem fenced_overflow {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) (hv : 1 ≤ v)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (c : Config U.stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z v (capacity a m z)) :
    let e := U.run (2*z+capacity a m z+6) c
    e.state = qReject ∧ e.head.val = fencePos (pairLength a m) ∧
      e.tape = countdownTape B x w z (v-1) (capacity a m z) := by
  obtain ⟨hw,hp,hfit⟩ := geometry x w hg hr
  let p : Fin (tapeLength (pairLength a m) B) := ⟨fencePos (pairLength a m),hfit⟩
  let u := {c with tape := loopTape B x w z v (capacity a m z)}
  have he := FixedGammaTargetUnaryCountdown.round_traced (zeros := z) (v := v) (r := capacity a m z) x w (by omega) hv hhigh u hq hh rfl
  have hf := frame_run p u (2*z+5+capacity a m z) (fun t ht => by
    exact lt_of_lt_of_eq (he.2.2.1 t ht) hp)
  rw [frame_source x w p rfl c ht] at hf
  let e := U.run (2*z+5+capacity a m z) c
  have heq : e.state = qRunEnd := by rw [show e = _ from hf]; exact he.2.1.1
  have heh : e.head = p := by
    apply Fin.ext; rw [show e = _ from hf]; change (U.run _ u).head.val = _
    rw [he.2.1.2.1]; exact hp
  have het : e.tape = countdownTape B x w z (v-1) (capacity a m z) := by
    rw [show e = _ from hf]; exact frame_tape x w p rfl _ he.2.1.2.2
  have hread : e.tape e.head = some false := by rw [het,heh]; simp [countdownTape,p]
  have hstep : U.step e.state (e.tape e.head) = (qReject,some false,Move.stay) := by
    rw [heq,hread]; rfl
  change (U.run _ c).state = _ ∧ _
  rw [show 2*z+capacity a m z+6 = (2*z+5+capacity a m z)+1 by omega]
  change (U.stepConfig e).state = _ ∧ _
  refine ⟨hstep |> congrArg Prod.fst, ?_, ?_⟩
  · change (moveHead e.head (U.step e.state (e.tape e.head)).2.2).val = _
    rw [hstep]; exact congrArg Fin.val heh
  · funext i
    change (if i = e.head then (U.step e.state (e.tape e.head)).2.1 else e.tape i) = _
    rw [hstep]; split_ifs with hi
    · rw [hi,← het]; exact hread.symm
    · rw [het]

private def countdownEmbed {n B : Nat} (c : Config FixedGammaTargetUnaryCountdown.stateCount n B) :
    Config prefixed.stateCount n B :=
  machine.seqEmbedRight G (
  FixedPairConcatSentinel.machine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine (
  FixedPairSeparatorCursor.machine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine (
  FixedPairSeparatorHole.machine.seqEmbedRight FixedPairTagRemovalShiftAlignmentCountdown.machine (
  FixedPairTagRemoval.machine.seqEmbedRight FixedPairOriginShiftAlignmentCountdown.machine (
  FixedPairOriginShiftBootstrap.machine.seqEmbedRight FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedPairOriginAlignment.machine.seqEmbedRight FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedPairContentMarkerErase.machine.seqEmbedRight FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentTagGate.machine.seqEmbedRight FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentGammaTerminator.machine.seqEmbedRight FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentGammaAnchor.machine.seqEmbedRight FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.mergedDispatcher.seqEmbedRight FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetFirstPayload.machine.seqEmbedRight FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetSecondPayload.machine.seqEmbedRight FixedGammaTargetMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight FixedGammaTargetLoopDecrementCountdown.machine (
  FixedGammaTargetPayloadRound.machine.seqEmbedRight FixedGammaTargetDecrementCountdown.machine (
  FixedGammaTargetRegisterDecrement.machine.seqEmbedRight FixedGammaTargetUnaryCountdown.machine c)))))))))))))))))

private theorem countdown_run {n B : Nat} (t : Nat) (c : Config FixedGammaTargetUnaryCountdown.stateCount n B) :
    prefixed.run t (countdownEmbed c) =
      countdownEmbed (FixedGammaTargetUnaryCountdown.machine.run t c) := by
  simp only [countdownEmbed, prefixed,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairConcatSentinel.machine,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorCursor.machine,
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorHole.machine,
    FixedPairTagRemovalShiftAlignmentCountdown.machine,
    FixedPairTagRemoval.machine,
    FixedPairOriginShiftAlignmentCountdown.machine,
    FixedPairOriginShiftBootstrap.machine,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairOriginAlignment.machine,
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairContentMarkerErase.machine,
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentTagGate.machine,
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentGammaTerminator.machine,
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentGammaAnchor.machine,
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTerminatorScratchBootstrap.machine,
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetFirstPayload.machine,
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetSecondPayload.machine,
    FixedGammaTargetMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetPayloadLoopFoundation.machine,
    FixedGammaTargetLoopDecrementCountdown.machine,
    FixedGammaTargetPayloadRound.machine,
    FixedGammaTargetDecrementCountdown.machine,
    FixedGammaTargetRegisterDecrement.machine,
    UniformTM.seq_run_right]

private theorem countdown_embed_fields {n B : Nat} (c : Config FixedGammaTargetUnaryCountdown.stateCount n B) :
    (countdownEmbed c).state.val = 245+c.state.val ∧
    (countdownEmbed c).head = c.head ∧ (countdownEmbed c).tape = c.tape := by
  refine ⟨?_,rfl,rfl⟩
  change 48+(7+(5+(3+(9+(7+(26+(4+(15+(3+(6+(28+(9+(18+(14+(14+(22+(7+c.state.val))))))))))))))))) = _
  omega

private def h17Phase {a m B z : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) : Config U.stateCount (pairLength a m) B :=
  ⟨qStart,(fencedDecrementConfig x w hg hr).head,fencedDecTape B x w z⟩

set_option maxHeartbeats 800000 in
private theorem raw_tail {a m B z C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m) (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q) (t : Nat) :
    prefixed.run (h17RawClock a m z C (borrow x w z)+t) (initialConfig prefixed B (encodePair x w)) =
      countdownEmbed (U.run t (h17Phase x w hg hr)) := by
  rw [prefixed.run_add,raw_fenced_h17_exact x w hr htag hg hz hfirst]
  have he : fencedDecrementConfig x w hg hr = countdownEmbed (h17Phase x w hg hr) := by
    apply Config.ext_parts
    · apply Fin.ext; rw [(countdown_embed_fields _).1]; rfl
    · exact (countdown_embed_fields (h17Phase x w hg hr)).2.1.symm
    · exact (countdown_embed_fields (h17Phase x w hg hr)).2.2.symm
  rw [he,countdown_run]

private theorem actual_entry {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j) :
    let e := U.run (borrow x w z+2) (h17Phase x w hg hr)
    e.state = qLoop ∧ e.head.val = a+m+2+z ∧ e.tape = countdownTape B x w z v 0 := by
  apply fenced_entry x w hg hr hv _ rfl rfl
  change fencedDecTape B x w z = countdownTape B x w z v 0
  have ht := FixedGammaTargetUnaryCountdown.loopTape_zero_eq_decTape (B := B) x w htag hg hv
  funext i; simp only [fencedDecTape,countdownTape,ht]

set_option maxHeartbeats 800000 in
/-- Exact raw success, including the tight capacity case. The full zero register and
`tally = v` tape is retained for a subsequent parser/GN handoff; this is one phase. -/
theorem raw_fenced_countdown_success_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false) (hcap : v ≤ capacity a m z) (s : Nat) :
    prefixed.run (countdownSuccessClock a m z C (borrow x w z) v+s)
      (initialConfig prefixed B (encodePair x w)) =
    ⟨prefixed.accept,⟨a+m+2+z,by have := geometry x w hg hr; omega⟩,countdownTape B x w z 0 v⟩ := by
  obtain ⟨hq,hh,ht⟩ := actual_entry x w hr htag hg hv
  obtain ⟨hkq,hkh,hkt⟩ := fenced_rounds x w hg hr v v 0 (by omega) le_rfl hhigh _ hq hh ht
  simp only [Nat.sub_self,Nat.zero_add] at hkt
  obtain ⟨heq,heh,het⟩ := fenced_exhaust x w hg hr _ hkq hkh hkt
  have he : prefixed.run (countdownSuccessClock a m z C (borrow x w z) v)
      (initialConfig prefixed B (encodePair x w)) =
      ⟨prefixed.accept,⟨a+m+2+z,by have := geometry x w hg hr; omega⟩,countdownTape B x w z 0 v⟩ := by
    unfold countdownSuccessClock
    rw [raw_tail x w hr htag hg hz hfirst]
    unfold fullClock FixedGammaTargetUnaryCountdownIteration.drainClock
    rw [U.run_add,U.run_add]
    apply Config.ext_parts
    · apply Fin.ext
      rw [(countdown_embed_fields _).1,heq]; rfl
    · rw [(countdown_embed_fields _).2.1]; exact Fin.ext heh
    · rw [(countdown_embed_fields _).2.2]; exact het
  rw [prefixed.run_add,he,prefixed.run_accept _ rfl]

set_option maxHeartbeats 800000 in
/-- Exact raw overflow rejection. The final attempted round consumes one further
register unit before reading false, and preserves that false symbol at the fence. -/
theorem raw_fenced_countdown_reject_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false) (hcap : capacity a m z < v) (s : Nat) :
    prefixed.run (countdownRejectClock a m z C (borrow x w z)+s)
      (initialConfig prefixed B (encodePair x w)) =
    ⟨prefixed.reject,⟨fencePos (pairLength a m),(geometry x w hg hr).2.2⟩,
      countdownTape B x w z (v-capacity a m z-1) (capacity a m z)⟩ := by
  obtain ⟨hq,hh,ht⟩ := actual_entry x w hr htag hg hv
  obtain ⟨hkq,hkh,hkt⟩ := fenced_rounds x w hg hr (capacity a m z) v 0 (by omega) (by omega)
    hhigh _ hq hh ht
  simp only [Nat.zero_add] at hkt
  obtain ⟨heq,heh,het⟩ := fenced_overflow x w hg hr (by omega)
    (high_sub hhigh (capacity a m z)) _ hkq hkh hkt
  have he : prefixed.run (countdownRejectClock a m z C (borrow x w z))
      (initialConfig prefixed B (encodePair x w)) =
      ⟨prefixed.reject,⟨fencePos (pairLength a m),(geometry x w hg hr).2.2⟩,
        countdownTape B x w z (v-capacity a m z-1) (capacity a m z)⟩ := by
    unfold countdownRejectClock
    rw [Nat.add_assoc, Nat.add_assoc,raw_tail x w hr htag hg hz hfirst,U.run_add,U.run_add]
    apply Config.ext_parts
    · apply Fin.ext
      rw [(countdown_embed_fields _).1,heq]; rfl
    · rw [(countdown_embed_fields _).2.1]; exact Fin.ext heh
    · rw [(countdown_embed_fields _).2.2]; exact het
  rw [prefixed.run_add,he,prefixed.run_reject _ rfl]

/-- Branch-local quadratic deadlines and allocation; no all-input halting claim. -/
theorem countdown_clock_bound {a m z C d v : Nat} (hw : 9+z ≤ a+m) (hz : 2 ≤ z)
    (hd : d ≤ z) (hC : C ≤ 2*(a+m)*(a+m)) (hv : v ≤ capacity a m z) :
    countdownSuccessClock a m z C d v ≤ countdownDeadline (pairLength a m) ∧
    countdownRejectClock a m z C d ≤ countdownDeadline (pairLength a m) ∧
    allocation (pairLength a m) ≤ countdownDeadline (pairLength a m) := by
  have hpre := h17_clock_bound hw hz hd hC
  have hF : capacity a m z ≤ 3*pairLength a m+2 := by
    exact (Nat.sub_le _ _).trans (le_of_eq (by rfl))
  have hvR : v ≤ 3*pairLength a m+2 := hv.trans hF
  have hzR : z ≤ pairLength a m := by unfold pairLength; omega
  have hv2 := Nat.mul_self_le_mul_self hvR
  have hF2 := Nat.mul_self_le_mul_self hF
  have hvz := Nat.mul_le_mul hvR hzR
  have hFz := Nat.mul_le_mul hF hzR
  unfold countdownSuccessClock countdownRejectClock fullClock
    FixedGammaTargetUnaryCountdownIteration.drainClock roundsClock zeroClock
    countdownDeadline allocation at *
  unfold h17Deadline at hpre
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith [Nat.zero_le ((pairLength a m+1)^2)]

/-- The success tape exposes the H17 low content, zero register, separator,
exact tally, intervening blanks and the installed false fence. -/
theorem countdown_success_cells {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) (hv : v ≤ capacity a m z) :
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val < a+m →
      countdownTape B x w z 0 v i = FixedGammaTargetPayloadExhaustion.finishTape B x w z i) ∧
    (∀ j, j ≤ z → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+1+j →
      countdownTape B x w z 0 v i = some false) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+2+z →
      countdownTape B x w z 0 v i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+z ≤ i.val → i.val < a+m+3+z+v →
      countdownTape B x w z 0 v i = some true) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+z+v ≤ i.val → i.val < fencePos (pairLength a m) →
      countdownTape B x w z 0 v i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val = fencePos (pairLength a m) →
      countdownTape B x w z 0 v i = some false) := by
  obtain ⟨hw,hp,hfit⟩ := geometry x w hg hr
  have pins := FixedGammaTargetUnaryCountdown.loopTape_pins (B := B) (zeros := z) (v := 0) (r := v) x w
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i hi; rw [countdownTape,if_neg (by omega)]; exact pins.2.2.2.2.2 i hi
  · intro j hj i hi; rw [countdownTape,if_neg (by omega),pins.1 j hj i hi]; simp
  · intro i hi; rw [countdownTape,if_neg (by omega)]; exact pins.2.2.1 i hi
  · intro i hlo hhi; rw [countdownTape,if_neg (by omega)]; exact pins.2.2.2.1 i hlo hhi
  · intro i hlo hhi; rw [countdownTape,if_neg (by omega)]; exact pins.2.2.2.2.1 i hlo
  · intro i hi; simp [countdownTape,hi]
end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
