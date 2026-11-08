import TotalIngressClosure.VirtualEvent
import TotalIngressClosure.VirtualCuts
import TotalIngressClosure.CursorTable
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("CarryReadyCompletion.Virtual","CarryReadyCompletion","After","After"),
      ("TotalIngressClosure.VirtualCuts","TotalIngressClosure","never_cuts","neverCuts"),
      ("TotalIngressClosure.VirtualEvent","TotalIngressClosure","virtual_event","virtualEvent"),
      ("TotalIngressClosure.CursorTable","TotalIngressClosure","table_first","tableFirst")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique actual source control-event trap {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem virtual_cuts (k : Nat) {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (branch:min (9+2*z+2^n) (a+m)=a+m ∨
      (min (9+2*z+2^n) (a+m) < a+m ∧ a+m-min (9+2*z+2^n) (a+m) < Cursor.Target.W k n)) :
    ∀ u,∀ j,j=430 ∨ j=613 → ((CanonicalLeaf.machine k).run u (initialConfig (CanonicalLeaf.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
        VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k))) := by
  have trapped:∃ t,(∀ u,u < t → ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val < 288+430+93*k) ∧
      After k (VirtualLeaf.embed k (((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state)):=by
    rcases branch with eof | ⟨phys,over⟩
    · obtain ⟨t,_hH,_hp,_price,done,_first,low,_heads⟩:=tableFirst k x w header tag gamma physical cap rows
      refine ⟨t,fun u hu=>(low u (Nat.le_of_lt hu)).trans_le (by omega),?_⟩
      have state:=congrArg Config.state done
      simp only [eof,if_pos] at state
      rw [state]
      exact Or.inr ⟨57,by decide,rfl⟩
    · obtain ⟨t,before,event⟩:=virtualEvent k x w header tag gamma physical cap rows phys over
      refine ⟨t,before,?_⟩
      rcases event with at250|at304|atCap
      · rw [at250];exact Or.inr ⟨250,by decide,rfl⟩
      · rw [at304];exact Or.inr ⟨304,by decide,rfl⟩
      · rw [atCap];exact Or.inl (Or.inr (Or.inr ⟨798,by decide,rfl⟩))
  obtain ⟨t,before,after⟩:=trapped
  have allCuts:=neverCuts k x w z tag gamma physical t before after
  intro u j hj
  rcases hj with rfl|rfl
  · exact (allCuts u).1
  · exact (allCuts u).2
end TotalIngressClosure
