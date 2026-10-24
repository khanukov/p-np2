import TotalIngressClosure.SupportedLift
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
open FixedGammaTargetUnaryCountdown (stateCount qLoop qDone loopTape roundClock zeroClock)
open FixedGammaTargetUnaryCountdownIteration (roundsClock)
private abbrev U : UniformTM:=FixedGammaTargetUnaryCountdown.machine
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("geometry","fenceGeometry"),("frame_source","frameSource"),
      ("fenced_round","fencedRound"),("fenced_rounds","fencedRounds"),("fenced_overflow","fencedOverflow")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith
      "_private.Complexity.Uniform.V1.FixedRawLengthFenceCountdown." &&
      n.toString.endsWith (".Pnp3.Complexity.Uniform.V1.FixedRawLengthFence."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique actual fenced arithmetic path {key}: {found.map Prod.fst}"
private theorem fenced_round_heads {a m B z v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room:2*pairLength a m+2 ≤ B) (cap:r < FixedRawLengthFence.capacity a m z)
    (positive:1 ≤ v) (high:∀ b,z < b → v.testBit b=false)
    (c:Config stateCount (pairLength a m) B) (state:c.state=qLoop)
    (head:c.head.val=a+m+2+z) (tape:c.tape=FixedRawLengthFence.countdownTape B x w z v r) :
    ∀ u,u ≤ roundClock z r → (U.run u c).head.val ≤ a+m+3+z+r:=by
  obtain ⟨_width,geometry,fit⟩:=fenceGeometry x w gamma room
  let p:Fin (tapeLength (pairLength a m) B):=⟨FixedRawLengthFence.fencePos (pairLength a m),fit⟩
  let plain:Config stateCount (pairLength a m) B:={c with tape:=loopTape B x w z v r}
  have trace:=FixedGammaTargetUnaryCountdown.round_traced x w (by omega) positive high plain state head rfl
  have same:{plain with tape:=Function.update plain.tape p (some false)}=c:=frameSource x w p rfl c tape
  intro u hu
  have frameRun:=U.run_update_of_unvisited plain p (some false) u (by
    intro t ht bad
    have bound:(U.run t plain).head.val ≤ a+m+3+z+r:=trace.2.2.2 t (by omega)
    have strict:(U.run t plain).head.val < p.val:=lt_of_le_of_lt bound (by dsimp only [p];omega)
    exact (ne_of_lt strict) (congrArg Fin.val bad))
  rw [same] at frameRun
  rw [frameRun]
  exact trace.2.2.2 u hu
private theorem fenced_rounds_heads {a m B z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room:2*pairLength a m+2 ≤ B) :
    ∀ k v r,r+k ≤ FixedRawLengthFence.capacity a m z → k ≤ v →
      (∀ b,z < b → v.testBit b=false) →
      ∀ c:Config stateCount (pairLength a m) B,c.state=qLoop →
        c.head.val=a+m+2+z → c.tape=FixedRawLengthFence.countdownTape B x w z v r →
        ∀ u,u ≤ roundsClock z r k → (U.run u c).head.val ≤ FixedRawLengthFence.fencePos (pairLength a m):=by
  intro k
  induction k with
  | zero=>
    intro v r cap _ _ c _ head _ u hu
    have zero:u=0:=by simp only [roundsClock] at hu;omega
    subst u
    rw [UniformTM.run]
    have geometry:=(fenceGeometry x w gamma room).2.1
    omega
  | succ k ih=>
    intro v r cap kv high c state head tape u hu
    obtain ⟨nextState,nextHead,nextTape⟩:=fencedRound x w gamma room (by omega) (by omega) high c state head tape
    have clock:roundsClock z r (k+1)=roundClock z r+roundsClock z (r+1) k:=by
      unfold roundsClock roundClock;ring
    by_cases early:u ≤ roundClock z r
    · have bound:=fenced_round_heads x w gamma room (by omega) (by omega) high c state head tape u early
      have geometry:=(fenceGeometry x w gamma room).2.1
      omega
    · rw [show u=roundClock z r+(u-roundClock z r) by omega,UniformTM.run_add]
      have nextHigh:∀ b,z < b → (v-1).testBit b=false:=
        (FixedGammaTargetUnaryCountdownIteration.high_iff_lt (v-1) z).2
          (lt_of_le_of_lt (Nat.sub_le v 1) ((FixedGammaTargetUnaryCountdownIteration.high_iff_lt v z).1 high))
      exact ih (v-1) (r+1) (by omega) (by omega) nextHigh _ nextState nextHead nextTape
        (u-roundClock z r) (by rw [clock] at hu;omega)
/-- Even huge binary operands execute only the physically capped number of
unary rounds; this is a bound on every literal head, not elapsed-as-allocation. -/
private theorem fenced_overflow_heads {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room:2*pairLength a m+2 ≤ B) (positive:1 ≤ v) (high:∀ b,z < b → v.testBit b=false)
    (c:Config stateCount (pairLength a m) B) (state:c.state=qLoop)
    (head:c.head.val=a+m+2+z)
    (tape:c.tape=FixedRawLengthFence.countdownTape B x w z v (FixedRawLengthFence.capacity a m z)) :
    ∀ u,u ≤ 2*z+FixedRawLengthFence.capacity a m z+6 →
      (U.run u c).head.val ≤ FixedRawLengthFence.fencePos (pairLength a m):=by
  obtain ⟨_width,geometry,fit⟩:=fenceGeometry x w gamma room
  let cap:=FixedRawLengthFence.capacity a m z
  let p:Fin (tapeLength (pairLength a m) B):=⟨FixedRawLengthFence.fencePos (pairLength a m),fit⟩
  let plain:Config stateCount (pairLength a m) B:={c with tape:=loopTape B x w z v cap}
  have trace:=FixedGammaTargetUnaryCountdown.round_traced x w (by omega) positive high plain state head rfl
  have same:{plain with tape:=Function.update plain.tape p (some false)}=c:=frameSource x w p rfl c tape
  intro u hu
  by_cases early:u ≤ 2*z+5+cap
  · have frameRun:=U.run_update_of_unvisited plain p (some false) u (by
      intro t ht bad
      have strict:(U.run t plain).head.val < a+m+3+z+cap:=trace.2.2.1 t (by omega)
      have capGeom:a+m+3+z+cap=FixedRawLengthFence.fencePos (pairLength a m):=geometry
      rw [capGeom] at strict
      exact (ne_of_lt strict) (congrArg Fin.val bad))
    rw [same] at frameRun
    rw [frameRun]
    change (U.run u plain).head.val ≤ _
    have bound:(U.run u plain).head.val ≤ a+m+3+z+cap:=trace.2.2.2 u (by unfold roundClock;omega)
    exact bound.trans_eq geometry
  · have last:u=2*z+cap+6:=by omega
    subst u
    exact (fencedOverflow x w gamma room positive high c state head tape).2.1.le
end TotalIngressClosure
