import VirtualFinalClosure.GuardZeroSemantics
import VirtualFinalClosure.GuardAddresses
import VirtualFinalClosure.MarkerState
namespace VirtualFinalClosure.ZeroMeaning
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
private theorem physical_zero {S p : Nat} (word : Bitstring S) (T : Nat → Option Bool)
    (source : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (word ⟨i,hi⟩))
    (zero : ∀ j,j < S-p → (T (S-1-j)).getD false=false) :
    ∀ i,p ≤ i → i < S → padRead word i=false:=by
  intro i lo hi
  have bit:=zero (S-1-i) (by omega)
  have same : S-1-(S-1-i)=i:=by omega
  rw [same,source i lo hi] at bit
  change word ⟨i,hi⟩=false at bit
  dsimp only [padRead]
  rw [dif_pos hi]
  exact bit
/-- Finite marker states retain the paid flag and clean bad-bit. This lemma
interprets their actual construction; it never retags a runtime state. -/
private theorem mode_test (f : Fin 4) (bits : Nat → Bool) (r : Nat) :
    (flag (modes (8+f.val) bits r)%2=1 ∧ bad (modes (8+f.val) bits r)=0) ↔ f.val%2=1:=by
  rw [(modeFields (8+f.val) bits r).1,(modeFields (8+f.val) bits r).2.2]
  fin_cases f <;> decide
private theorem relation {a m n z : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m) (f : Fin 4)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (positive : 0 < n) (virtual : a+m ≤ Cursor.Target.M k n z)
    (zero : ∀ i,9+2*z+2^n ≤ i → i < a+m → padRead (Fin.append x w) i=false)
    (meaning : f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔ f.val%2=1:=by
  have start : tagLen+(2*z+1)=9+2*z:=by change 8+(2*z+1)=9+2*z;omega
  have semantics:=zeroSuffix k x w canonical header tag (by rw [address k _ header];exact virtual) (by
    intro i lo hi
    apply zero i _ hi
    change tagLen+(2*z+1)+2^n ≤ i at lo
    rw [start] at lo
    exact lo)
  constructor
  · intro accepted
    obtain ⟨_positive,table⟩:=semantics.mp accepted
    apply meaning.mpr
    intro j
    simpa only [start] using table j
  · intro matched
    apply semantics.mpr
    refine ⟨positive,?_⟩
    intro j
    simpa only [start] using (meaning.mp matched) j
#print axioms physical_zero
#print axioms mode_test
#print axioms relation
end VirtualFinalClosure.ZeroMeaning
