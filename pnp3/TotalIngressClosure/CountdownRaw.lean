import TotalIngressClosure.CountdownHeads
import IngressAllocation.Bootstrap
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedRawLengthFence
private abbrev U : UniformTM:=FixedGammaTargetUnaryCountdown.machine
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,isTheorem) in [
      ("Complexity.Uniform.V1.FixedRawLengthFenceCountdown","Pnp3.Complexity.Uniform.V1.FixedRawLengthFence","h17Phase","phase",false),
      ("Complexity.Uniform.V1.FixedRawLengthFenceCountdown","Pnp3.Complexity.Uniform.V1.FixedRawLengthFence","actual_entry","actualEntry",true),
      ("Complexity.Uniform.V1.FixedRawLengthFenceCountdown","Pnp3.Complexity.Uniform.V1.FixedRawLengthFence","raw_tail","rawTail",true),
      ("TotalIngressClosure.CountdownHeads","TotalIngressClosure","fenced_rounds_heads","roundsHeads",true),
      ("TotalIngressClosure.CountdownHeads","TotalIngressClosure","fenced_overflow_heads","overflowHeads",true),
      ("Complexity.Uniform.V1.FixedRawLengthFenceCountdown","Pnp3.Complexity.Uniform.V1.FixedRawLengthFence","fenced_rounds","fencedRounds",true),
      ("IngressAllocation.Bootstrap","IngressAllocation","bootstrap_price","bootstrapPrice",true)] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      let actualTheorem:=match ci with | .thmInfo _=>true | _=>false
      unless actualTheorem=isTheorem do throwError "Wrong declaration kind {n}"
      logInfo m!"private-term|{n}|isTheorem={isTheorem}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique physical countdown interface {mod}/{key}: {found.map Prod.fst}"
private theorem fence_envelope (R : Nat) : fencePos R ≤ 12*(R+1)^2 := by
  unfold fencePos
  nlinarith only [Nat.zero_le (R*R),Nat.zero_le R]
/-- Every actual raw prefix up to the successful unary installation, including each borrow/return edge. -/
private theorem raw_countdown_heads {a m z C v : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (hz : 2 ≤ z)
    (first : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      (FixedRawLengthFence.allocation (pairLength a m)) x w C q)
    (digits : ∀ j,j ≤ z → v.testBit (z-j)=decBit x w z (borrow x w z) j)
    (high : ∀ b,z < b → v.testBit b=false) :
    ∀ t,t ≤ (if v ≤ capacity a m z then countdownSuccessClock a m z C (borrow x w z) v
      else countdownRejectClock a m z C (borrow x w z)) →
      (prefixed.run t (initialConfig prefixed (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val
        ≤ 12*(pairLength a m+1)^2 := by
  have room:=(resource_bounds (pairLength a m)).1
  have width : 9+z ≤ a+m := by
    have valid:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    omega
  have pair : a+m ≤ pairLength a m := by simp only [pairLength];omega
  have fence:=fence_envelope (pairLength a m)
  intro t ht
  by_cases installing : t ≤ installClock (pairLength a m)
  · have price:=bootstrapPrice a m
    exact (prefixed.run_initialConfig_head_le (encodePair x w)).trans (by omega)
  · by_cases early : t ≤ h17RawClock a m z C (borrow x w z)
    · have bound:=raw_fenced_h17_trace x w room tag gamma hz first (t-installClock (pairLength a m))
        (by unfold h17RawClock at early;omega)
      have eqt : installClock (pairLength a m)+(t-installClock (pairLength a m))=t := by omega
      rw [eqt] at bound
      exact bound.1.trans (by dsimp only [fencePos] at fence;omega)
    · rw [show t=h17RawClock a m z C (borrow x w z)+(t-h17RawClock a m z C (borrow x w z)) by omega,
        rawTail x w room tag gamma hz first]
      change (U.run (t-h17RawClock a m z C (borrow x w z)) (phase x w gamma room)).head.val ≤ _
      by_cases entering : t-h17RawClock a m z C (borrow x w z) ≤ borrow x w z+2
      · have dist:=U.run_head_le (steps:=t-h17RawClock a m z C (borrow x w z)) (phase x w gamma room)
        have start : (phase x w gamma room).head.val=a+m+1+z-borrow x w z := rfl
        have d:=(FixedGammaTargetRegisterDecrement.borrow_pins x w z).1
        rw [start] at dist
        have small : a+m+1+z-borrow x w z+(t-h17RawClock a m z C (borrow x w z)) ≤ fencePos (pairLength a m) := by
          dsimp only [fencePos];omega
        exact dist.trans (small.trans fence)
      · have initialEntry:=actualEntry x w room tag gamma digits
        let e:=U.run (borrow x w z+2) (phase x w gamma room)
        let k:=min v (capacity a m z)
        let steps:=t-h17RawClock a m z C (borrow x w z)-(borrow x w z+2)
        have afterEntry : U.run (t-h17RawClock a m z C (borrow x w z)) (phase x w gamma room)=U.run steps e:=by
          rw [show t-h17RawClock a m z C (borrow x w z)=borrow x w z+2+steps by dsimp only [steps];omega,
            UniformTM.run_add]
        rw [afterEntry]
        by_cases running:steps ≤ FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k
        · exact (roundsHeads x w gamma room k v 0 (by dsimp only [k];omega)
            (by dsimp only [k];exact Nat.min_le_left _ _) high e
            initialEntry.1 initialEntry.2.1 initialEntry.2.2 steps running).trans fence
        · obtain ⟨sq,sh,st⟩:=fencedRounds x w gamma room k v 0 (by dsimp only [k];omega)
            (by dsimp only [k];exact Nat.min_le_left _ _) high e
            initialEntry.1 initialEntry.2.1 initialEntry.2.2
          let u:=steps-FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k
          rw [show steps=FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k+u by dsimp only [u];omega,
            UniformTM.run_add]
          by_cases fits:v ≤ capacity a m z
          · have ke:k=v:=Nat.min_eq_left fits
            have time:u ≤ FixedGammaTargetUnaryCountdown.zeroClock z:=by
              rw [if_pos fits] at ht
              dsimp only [u,steps,k] at *
              rw [Nat.min_eq_left fits] at *
              unfold countdownSuccessClock FixedGammaTargetUnaryCountdownIteration.fullClock
                FixedGammaTargetUnaryCountdownIteration.drainClock at ht
              omega
            have bound:=U.run_head_le (steps:=u) (U.run (FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k) e)
            have bound':(U.run u (U.run (FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k) e)).head.val ≤ a+m+2+z+u:=by
              simpa only [sh] using bound
            have sourceWidth:9+z ≤ a+m:=width
            have limit:a+m+2+z+u ≤ 12*(pairLength a m+1)^2:=by
              unfold FixedGammaTargetUnaryCountdown.zeroClock at time
              nlinarith only [time,sourceWidth,pair,Nat.zero_le ((pairLength a m)^2)]
            exact bound'.trans limit
          · have ke:k=capacity a m z:=Nat.min_eq_right (by omega)
            have time:u ≤ 2*z+capacity a m z+6:=by
              rw [if_neg fits] at ht
              dsimp only [u,steps] at *
              unfold countdownRejectClock at ht
              rw [ke]
              omega
            have highSub:∀ b,z < b → (v-k).testBit b=false:=
              (FixedGammaTargetUnaryCountdownIteration.high_iff_lt (v-k) z).2
                (lt_of_le_of_lt (Nat.sub_le v k)
                  ((FixedGammaTargetUnaryCountdownIteration.high_iff_lt v z).1 high))
            have stateTape:(U.run (FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 k) e).tape=
                countdownTape (FixedRawLengthFence.allocation (pairLength a m)) x w z (v-k) (capacity a m z):=by
              simpa only [Nat.zero_add,ke] using st
            exact (overflowHeads x w gamma room (by omega) highSub _ sq sh stateTape u time).trans fence
end TotalIngressClosure
