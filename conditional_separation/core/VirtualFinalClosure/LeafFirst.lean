import VirtualFinalClosure.BodyTrap
import VirtualFinalClosure.LeafFinish
namespace VirtualFinalClosure.LeafFirst
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LeafFive","VirtualFinalClosure.LeafFive","prepared","five",(1:Nat)),
      ("VirtualFinalClosure.LeafFinish","VirtualFinalClosure.LeafFinish","prepared","six",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","result","result",0),
      ("VirtualFinalClosure.BodyTrap","VirtualFinalClosure.BodyTrap","leaf_outside","outside",1),
      ("VirtualFinalClosure.BodyTrap","VirtualFinalClosure.BodyTrap","safe","prefixSafe",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong canonical literal first-FINAL term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique canonical literal first-FINAL term {mod}/{key}"
/-- Strict GLOBAL first verdict/BODY exclusion for a genuinely reached ready
configuration. The pre-final canonical work state is outside the actual BODY
transition trap; the sixth row is the literal terminal edge. No inert deadline
is substituted for the caller's actual execution witness. -/
private theorem after_prefix (k N B P L n s : Nat) (m : Fin 144) (T : Nat → Option Bool)
    (beta : Fin n → Bool) (c : Config (machine k).stateCount N B)
    (pos : 0<n) (fit : L+n+1≤P) (finite : P<tapeLength N B)
    (sep : T L=none) (last : T (L+n+1)=none)
    (digits : ∀ j : Fin n,T (L+n-j.val)=some (beta j))
    (before : ∀ u,u≤s → ((machine k).run u c).head.val≤P)
    (arrived : (machine k).run s c=⟨ready k m,⟨L+n+1,lt_of_le_of_lt fit finite⟩,fun j=>T j.val⟩) :
    (machine k).run (s+6) c=
      ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
        ⟨L+n+1,lt_of_le_of_lt fit finite⟩,
        fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩ ∧
      (∀ u,u<s+6 → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u≤s+6 → ((machine k).run u c).head.val≤P):=by
  let hH:=lt_of_le_of_lt fit finite
  let start : Config (machine k).stateCount N B:=⟨ready k m,⟨L+n+1,hH⟩,fun j=>T j.val⟩
  have path:=five k P L n m T beta fit sep last digits
  rw [dif_pos pos] at path
  have atFive : (machine k).run 5 start=
      ⟨result k m (beta ⟨0,pos⟩),⟨L+n+1,hH⟩,
        fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩:=execute path finite
  obtain ⟨done,_safe,heads⟩:=six k N B P L n m T beta pos fit finite sep last digits
  have final := done
  have fiveRaw : (machine k).run (s+5) c=
      ⟨result k m (beta ⟨0,pos⟩),⟨L+n+1,hH⟩,
        fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩:=by
    rw [UniformTM.run_add,arrived]
    exact atFive
  have clean:=prefixSafe k c (s+5) (by rw [fiveRaw];exact outside k _ m)
  refine ⟨?_,?_,?_⟩
  · rw [UniformTM.run_add,arrived]
    exact final
  · intro u hu
    exact clean u (by omega)
  · intro u hu
    by_cases early : u≤s
    · exact before u early
    · rw [show u=s+(u-s) by omega,UniformTM.run_add,arrived]
      exact heads (u-s) (by omega)
#print axioms after_prefix
end VirtualFinalClosure.LeafFirst
