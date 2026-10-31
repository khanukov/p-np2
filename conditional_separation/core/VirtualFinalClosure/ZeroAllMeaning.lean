import VirtualFinalClosure.ZeroMeaning
import VirtualFinalClosure.GuardZeroSemantics
import VirtualFinalClosure.GuardAddresses
import VirtualFinalClosure.MarkerState
namespace VirtualFinalClosure.ZeroAllMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardZeroSemantics","VirtualFinalClosure.GuardZeroSemantics","zero_suffix","zeroSuffix",(1:Nat)),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","address","address",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_fields","modeFields",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong original rho seen0 interpretation term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original rho seen0 interpretation term {mod}/{key}"
private theorem relation {a m n z : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m) (f : Fin 4)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (virtual : a+m ≤ Cursor.Target.M k n z)
    (zero : ∀ i,9+2*z+2^n ≤ i → i < a+m → padRead (Fin.append x w) i=false)
    (meaning : f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔ 0<n ∧ f.val%2=1:=by
  have start : tagLen+(2*z+1)=9+2*z:=by change 8+(2*z+1)=9+2*z;omega
  have semantics:=zeroSuffix k x w canonical header tag (by rw [address k _ header];exact virtual) (by
    intro i lo hi
    apply zero i _ hi
    change tagLen+(2*z+1)+2^n ≤ i at lo
    rw [start] at lo
    exact lo)
  constructor
  · intro accepted
    obtain ⟨positive,table⟩:=semantics.mp accepted
    refine ⟨positive,meaning.mpr ?_⟩
    intro j
    simpa only [start] using table j
  · rintro ⟨positive,matched⟩
    apply semantics.mpr
    refine ⟨positive,?_⟩
    intro j
    simpa only [start] using (meaning.mp matched) j
#print axioms relation
end VirtualFinalClosure.ZeroAllMeaning
