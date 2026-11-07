import IngressAllocation.Target
namespace IngressAllocation.CountdownPrefix
open Pnp3.Complexity.Uniform.V1 PairEncoding
open FixedGammaTargetUnaryCountdown (stateCount qLoop qDone loopTape roundClock zeroClock)
open FixedGammaTargetUnaryCountdownIteration (roundsClock drainClock)
private abbrev U : UniformTM:=FixedGammaTargetUnaryCountdown.machine
attribute [local irreducible] UniformTM.run
private theorem rounds_heads {a m B z F : Nat} (x : Bitstring a) (w : Bitstring m)
    (room : z+2+F ≤ a+B) :
    ∀ k v r,r+k ≤ F → k ≤ v → (∀ b,z < b → v.testBit b=false) →
    ∀ c : Config stateCount (pairLength a m) B,c.state=qLoop →
      c.head.val=a+m+2+z → c.tape=loopTape B x w z v r →
      ∀ t,t ≤ roundsClock z r k → (U.run t c).head.val ≤ a+m+3+z+r+k := by
  intro k
  induction k with
  | zero =>
    intro v r _ _ _ c _ head _ t ht
    have eqt : t=0 := by simp only [roundsClock] at ht;omega
    subst t
    rw [UniformTM.run]
    change c.head.val ≤ _
    omega
  | succ k ih =>
    intro v r cap kv high c state head tape t ht
    have fit : a+m+3+z+r < tapeLength (pairLength a m) B :=
      (FixedGammaTargetUnaryCountdownIteration.lane_room cap room).1 0 (Nat.zero_le _)
    have step:=FixedGammaTargetUnaryCountdown.round_traced x w fit (by omega) high c state head tape
    have clock : roundsClock z r (k+1)=roundClock z r+roundsClock z (r+1) k := by
      unfold roundsClock roundClock;ring
    by_cases early : t ≤ roundClock z r
    · exact (step.2.2.2 t early).trans (by omega)
    · rw [show t=roundClock z r+(t-roundClock z r) by omega,UniformTM.run_add]
      have nextHigh : ∀ b,z < b → (v-1).testBit b=false :=
        (FixedGammaTargetUnaryCountdownIteration.high_iff_lt (v-1) z).2
          (lt_of_le_of_lt (Nat.sub_le v 1)
            ((FixedGammaTargetUnaryCountdownIteration.high_iff_lt v z).1 high))
      have bound:=ih (v-1) (r+1) (by omega) (by omega) nextHigh
        (U.run (roundClock z r) c) step.1.1 step.1.2.1 step.1.2.2
        (t-roundClock z r) (by rw [clock] at ht;omega)
      omega
private theorem drain_heads {a m B z v r F : Nat} (x : Bitstring a) (w : Bitstring m)
    (cap : r+v ≤ F) (room : z+2+F ≤ a+B)
    (high : ∀ b,z < b → v.testBit b=false)
    (c : Config stateCount (pairLength a m) B) (state : c.state=qLoop)
    (head : c.head.val=a+m+2+z) (tape : c.tape=loopTape B x w z v r) :
    ∀ t,t ≤ drainClock z r v → (U.run t c).head.val ≤ a+m+3+z+r+v := by
  intro t ht
  by_cases early : t ≤ roundsClock z r v
  · exact rounds_heads x w room v v r cap le_rfl high c state head tape t early
  · obtain ⟨sq,sh,st⟩:=FixedGammaTargetUnaryCountdownIteration.iterate_generic x w room
      v v r cap le_rfl high c state head tape
    rw [Nat.sub_self] at st
    have exhausted:=FixedGammaTargetUnaryCountdown.exhaust_traced x w
      (FixedGammaTargetUnaryCountdownIteration.lane_room cap room).2
      (U.run (roundsClock z r v) c) sq sh st
    rw [show t=roundsClock z r v+(t-roundsClock z r v) by omega,UniformTM.run_add]
    exact (exhausted.2 (t-roundsClock z r v) (by dsimp only [drainClock] at ht;omega)).trans (by omega)
/-- The installed false fence is never visited, at every microstep of the whole drain. -/
private theorem fenced_drain_heads {a m B z v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room : 2*pairLength a m+2 ≤ B) (cap : r+v < FixedRawLengthFence.capacity a m z)
    (high : ∀ b,z < b → v.testBit b=false)
    (c : Config stateCount (pairLength a m) B) (state : c.state=qLoop)
    (head : c.head.val=a+m+2+z) (tape : c.tape=FixedRawLengthFence.countdownTape B x w z v r) :
    ∀ t,t ≤ drainClock z r v → (U.run t c).head.val < FixedRawLengthFence.fencePos (pairLength a m) := by
  have width : 9+z ≤ a+m := by
    have valid:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    omega
  have geometry : a+m+3+z+FixedRawLengthFence.capacity a m z=FixedRawLengthFence.fencePos (pairLength a m) := by
    simp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at *;omega
  have fenceFit : FixedRawLengthFence.fencePos (pairLength a m) < tapeLength (pairLength a m) B := by
    simp only [FixedRawLengthFence.fencePos,tapeLength];omega
  let p : Fin (tapeLength (pairLength a m) B):=⟨FixedRawLengthFence.fencePos (pairLength a m),fenceFit⟩
  let unframed : Config stateCount (pairLength a m) B:={c with tape:=loopTape B x w z v r}
  have space : z+2+FixedRawLengthFence.capacity a m z ≤ a+B := by
    simp only [tapeLength,pairLength,FixedRawLengthFence.fencePos] at *;omega
  have bound:=drain_heads x w (Nat.le_of_lt cap) space high unframed state head rfl
  have same : {unframed with tape:=Function.update unframed.tape p (some false)}=c := by
    apply Config.ext_parts
    · rfl
    · rfl
    · rw [tape]
      funext i
      simp only [unframed,FixedRawLengthFence.countdownTape,Function.update_apply,Fin.ext_iff,p]
  intro t ht
  have frameRun:=U.run_update_of_unvisited unframed p (some false) t
    (by
      intro u hu bad
      have strict : (U.run u unframed).head.val < p.val :=
        lt_of_le_of_lt (bound u (by omega)) (by dsimp only [p];omega)
      exact (ne_of_lt strict) (congrArg Fin.val bad))
  rw [same] at frameRun
  rw [frameRun]
  exact lt_of_le_of_lt (bound t ht) (by omega)
end IngressAllocation.CountdownPrefix
