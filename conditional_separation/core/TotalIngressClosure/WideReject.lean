import TotalIngressClosure.CountdownRaw
import RepairedFrontier.Producer
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
open FixedGammaTargetRegisterDecrement (borrow decBit)
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.CountdownRaw","TotalIngressClosure","raw_countdown_heads","rawHeads"),
      ("RepairedFrontier.Producer","RepairedFrontier","countdown_path","countdownPath")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique bounded huge-header path {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem wide_reject {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide:2 ≤ z)
    (cap:FixedRawLengthFence.capacity a m z < n) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig SmallIngress.producer B (encodePair x w)
    ∃ t,t ≤ 128*(R+1)^2 ∧ (SmallIngress.producer.run t c).state=SmallIngress.producer.reject ∧
      (∀ u,u ≤ t → (SmallIngress.producer.run u c).head.val ≤ 12*(R+1)^2):=by
  intro R B c
  obtain ⟨z',other,_len,_lower,_upper,_borrow,digits,high⟩:=decremented_register_digits x w header
  have equal:z'=z:=Option.some.inj (other.symm.trans gamma)
  subst z'
  obtain ⟨C,q,price,first,_time,atH17⟩:=FixedRawLengthFence.raw_fenced_h17_allocated x w tag gamma wide
  have room:=(FixedRawLengthFence.resource_bounds R).1
  have bits:∀ j,j ≤ z → n.testBit (z-j)=decBit x w z (borrow x w z) j:=fun j hj=>(digits j hj).symm
  let T:=FixedRawLengthFence.countdownRejectClock a m z C (borrow x w z)
  let P:=FixedRawLengthFence.h17RawClock a m z C (borrow x w z)
  let old:=initialConfig FixedRawLengthFence.prefixed B (encodePair x w)
  have safeH17:(FixedRawLengthFence.prefixed.run P old).state≠FixedRawLengthFence.prefixed.reject:=by
    rw [atH17]
    change (⟨245,by decide⟩ : Fin 256) ≠ FixedRawLengthFence.prefixed.reject
    decide
  have before(u : Nat)(hu:u ≤ P):(FixedRawLengthFence.prefixed.run u old).state≠FixedRawLengthFence.prefixed.reject:=by
    intro bad
    have stay:=FixedRawLengthFence.prefixed.run_reject_of_le old bad hu
    exact safeH17 ((congrArg Config.state stay).trans bad)
  have tx(u : Nat)(_hu:u ≤ T):SmallIngress.producer.run u c=
      SmallIngress.liftOld (FixedRawLengthFence.prefixed.run u old):=by
    by_cases early:u ≤ P
    · exact SmallIngress.preserves_nonreject old u (before u early)
    · have path:=countdownPath x w tag gamma wide first (u-P)
      have eq:P+(u-P)=u:=by omega
      rw [eq] at path
      exact path
  have oldEnd:=FixedRawLengthFence.raw_fenced_countdown_reject_exact x w room tag gamma wide first bits high cap 0
  simp only [Nat.add_zero] at oldEnd
  have clock:T ≤ 128*(R+1)^2:=
    (FixedRawLengthFence.countdown_clock_bound (v:=0)
      (by have h:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1;omega)
      wide (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 price (Nat.zero_le _)).2.1
  refine ⟨T,clock,?_,?_⟩
  · rw [tx T le_rfl,oldEnd]
    rfl
  · intro u hu
    rw [tx u hu]
    have bound:=rawHeads x w tag gamma wide first bits high u
    rw [if_neg (by omega : ¬n ≤ FixedRawLengthFence.capacity a m z)] at bound
    exact bound hu
end TotalIngressClosure
