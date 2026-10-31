import IngressAllocation.Countdown
import IngressAllocation.Bootstrap
namespace IngressAllocation.CountdownPrefix
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
      ("IngressAllocation.Countdown","IngressAllocation.CountdownPrefix","fenced_drain_heads","drainHeads",true),
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
private theorem raw_success_heads {a m z C v : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (hz : 2 ≤ z)
    (first : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      (FixedRawLengthFence.allocation (pairLength a m)) x w C q)
    (digits : ∀ j,j ≤ z → v.testBit (z-j)=decBit x w z (borrow x w z) j)
    (high : ∀ b,z < b → v.testBit b=false) (cap : v < capacity a m z) :
    ∀ t,t ≤ countdownSuccessClock a m z C (borrow x w z) v →
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
        have runBound:=drainHeads x w gamma room (by simpa using cap) high e
          initialEntry.1 initialEntry.2.1 initialEntry.2.2
          (t-h17RawClock a m z C (borrow x w z)-(borrow x w z+2))
          (by unfold countdownSuccessClock FixedGammaTargetUnaryCountdownIteration.fullClock at ht;omega)
        rw [show t-h17RawClock a m z C (borrow x w z)=borrow x w z+2+
          (t-h17RawClock a m z C (borrow x w z)-(borrow x w z+2)) by omega,UniformTM.run_add]
        exact (Nat.le_of_lt runBound).trans fence
end IngressAllocation.CountdownPrefix
