import RawFrontier.Base
namespace RawFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decBit)
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private abbrev U := FixedGammaTargetUnaryCountdown.machine
private def countMap (s : Fin U.stateCount) : Fin SmallIngress.producer.stateCount := SmallIngress.q (245+s.val)
private def oldCountMap (s : Fin U.stateCount) : Fin FixedRawLengthFence.prefixed.stateCount :=
  ⟨245+s.val,by have hs := s.isLt; change s.val < 11 at hs; change _ < 256; omega⟩
private theorem count_rows : ∀ (s : Fin U.stateCount) b,
    SmallIngress.producer.step (countMap s) b=(countMap (U.step s b).1,(U.step s b).2) := by decide
private theorem old_count_rows : ∀ (s : Fin U.stateCount) b,
    FixedRawLengthFence.prefixed.step (oldCountMap s) b=(oldCountMap (U.step s b).1,(U.step s b).2) := by decide
private theorem countdown_transport {a m z C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide : 2 ≤ z)
    (first : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      (FixedRawLengthFence.allocation (pairLength a m)) x w C q) (s : Nat) :
    SmallIngress.producer.run (FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+s)
      (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
    SmallIngress.liftOld (FixedRawLengthFence.prefixed.run
      (FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+s)
      (initialConfig FixedRawLengthFence.prefixed (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
  let B := FixedRawLengthFence.allocation (pairLength a m)
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  have old := FixedRawLengthFence.raw_fenced_h17_exact x w resource tag gamma wide first
  have safe : (FixedRawLengthFence.prefixed.run (FixedRawLengthFence.h17RawClock a m z C (borrow x w z))
      (initialConfig FixedRawLengthFence.prefixed B (encodePair x w))).state≠FixedRawLengthFence.prefixed.reject := by
    rw [old]
    change (⟨245,by decide⟩ : Fin 256)≠FixedRawLengthFence.prefixed.reject
    decide
  have pre := SmallIngress.preserves_nonreject _ _ safe
  change SmallIngress.producer.run _ (initialConfig SmallIngress.producer B (encodePair x w))=_ at pre
  rw [old] at pre
  let c : Config U.stateCount (pairLength a m) B :=
    ⟨U.start,(FixedRawLengthFence.fencedDecrementConfig x w gamma resource).head,
      (FixedRawLengthFence.fencedDecrementConfig x w gamma resource).tape⟩
  have newRun := Cursor.Transport.avoid_changed_rows U SmallIngress.producer countMap (fun _ => False)
    (fun _ h => False.elim h) (fun st _ => count_rows st) c s (fun h => h)
  have oldRun := Cursor.Transport.avoid_changed_rows U FixedRawLengthFence.prefixed oldCountMap (fun _ => False)
    (fun _ h => False.elim h) (fun st _ => old_count_rows st) c s (fun h => h)
  rw [UniformTM.run_add,pre,UniformTM.run_add,old]
  change SmallIngress.producer.run s ⟨countMap c.state,c.head,c.tape⟩=
    SmallIngress.liftOld (FixedRawLengthFence.prefixed.run s ⟨oldCountMap c.state,c.head,c.tape⟩)
  rw [newRun,oldRun]
  rfl
/-- Actual raw capacity overflow. Header bits identify v only in the proof;
the fixed table spends at most the physical capacity before reading its fence. -/
theorem capacity_reject (k : Nat) {a m z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide : 2 ≤ z)
    (digits : ∀ j, j ≤ z → v.testBit (z-j)=decBit x w z (borrow x w z) j)
    (high : ∀ b, z < b → v.testBit b=false) (overflow : FixedRawLengthFence.capacity a m z < v) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false ∧
      ((AllArityCursor.machine k).run t c).head.val=FixedRawLengthFence.fencePos (pairLength a m) ∧
      ((AllArityCursor.machine k).run t c).tape=FixedRawLengthFence.countdownTape B x w z
        (v-FixedRawLengthFence.capacity a m z-1) (FixedRawLengthFence.capacity a m z) := by
  dsimp only
  let B := FixedRawLengthFence.allocation (pairLength a m)
  obtain ⟨C,q,price,first,_end⟩ := FixedGammaPayloadDispatcherFirstArrival.tagged_strict_first_terminal (B := B) x w tag
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  have old := FixedRawLengthFence.raw_fenced_countdown_reject_exact x w resource tag gamma wide first digits high overflow 0
  let T := FixedRawLengthFence.countdownRejectClock a m z C (borrow x w z)
  simp only [Nat.add_zero] at old
  change FixedRawLengthFence.prefixed.run T
    (initialConfig FixedRawLengthFence.prefixed B (encodePair x w))=_ at old
  let d := (borrow x w z+2)+FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 (FixedRawLengthFence.capacity a m z)+
    (2*z+FixedRawLengthFence.capacity a m z+6)
  have clock : T=FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+d := by
    dsimp only [T,d,FixedRawLengthFence.countdownRejectClock]
    omega
  have sim := countdown_transport x w tag gamma wide first d
  rw [←clock,old] at sim
  have hit : (SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))).state=
      SmallIngress.producer.reject := by rw [sim]; rfl
  have hw := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have bound : T ≤ 128*(pairLength a m+1)^2 :=
    (FixedRawLengthFence.countdown_clock_bound (v := 0) (by omega : 9+z ≤ a+m) wide
      (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 price (Nat.zero_le _)).2.1
  obtain ⟨t,ht,reject,strict,safe,sound⟩ := producer_reject_frontier k x w T bound hit
  have raw := SmallIngress.producer.seq_reject_handoff (Cursor.machine k) _ hit 0
  change (AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) B (encodePair x w))=_ at raw
  have before : t ≤ T := by
    by_contra no
    exact (strict T (by omega)).1 (congrArg Config.state raw)
  have same := (AllArityCursor.machine k).run_reject_of_le _ reject before
  refine ⟨t,ht,reject,strict,safe,sound,?_,?_⟩
  · rw [←same,raw,sim]
    rfl
  · rw [←same,raw,sim]
    rfl
end RawFrontier
