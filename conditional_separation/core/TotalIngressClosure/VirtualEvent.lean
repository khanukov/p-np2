import TotalIngressClosure.WeightTotal
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("LengthTotal","physical_length_heads","lengthRaw"),
      ("WeightTotal","physical_weight_heads","weightRaw")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") &&
      n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique generic actual arithmetic event {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem virtual_event (k : Nat) {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (over:a+m-min (9+2*z+2^n) (a+m) < Cursor.Target.W k n) :
    let B:=FixedRawLengthFence.allocation (pairLength a m)
    let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ t,(∀ u,u < t → ((AllArityCursor.machine k).run u c).state.val < 288+430+93*k) ∧
      (((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250) ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304) ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k))) := by
  intro B c
  by_cases fits:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m)
  · obtain ⟨t,_price,_heads,before,outcome⟩:=weightRaw k x w header tag gamma firstPhysical cap rows physical fits
    rcases outcome with ⟨fitsW,_⟩|⟨v2,v3,v4,v5,d0,_cap,_h,done⟩
    · exact False.elim (Nat.not_lt_of_ge fitsW over)
    · exact ⟨t,before,Or.inr (Or.inr (congrArg Config.state done))⟩
  · obtain ⟨t,_h,_price,done,_heads,before⟩:=lengthRaw k x w header tag gamma firstPhysical cap rows physical
    have state:=congrArg Config.state done
    simp only [if_neg fits] at state
    refine ⟨t,fun u hu=>(before u (Nat.le_of_lt hu)).trans_lt (by omega),?_⟩
    by_cases odd:(a+m-min (9+2*z+2^n) (a+m)+1)%2=1
    · exact Or.inl (by simpa only [if_pos odd] using state)
    · exact Or.inr (Or.inl (by simpa only [if_neg odd] using state))
end TotalIngressClosure
