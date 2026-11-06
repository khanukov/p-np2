import VirtualFinalClosure.GuardDecision
import VirtualFinalClosure.GuardValue
import VirtualFinalClosure.GuardPayloadMeaning
import VirtualFinalClosure.GuardAddresses
namespace VirtualFinalClosure.GuardFinalMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardDecision","VirtualFinalClosure.GuardDecision","virtual_test","virtualTest",(1:Nat)),
      ("VirtualFinalClosure.GuardValue","VirtualFinalClosure.GuardValue","read","valueRead",1),
      ("VirtualFinalClosure.GuardPayloadMeaning","VirtualFinalClosure.GuardPayloadMeaning","exact_window","exactWindow",1),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","address","address",1),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","width","width",1),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","index_width","indexWidth",1),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","index_start","indexStart",1),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong original rho/native guard interpretation {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original rho/native guard interpretation {mod}/{key}"
/-- Interpret the actual BE-quota/scan branch and paid table flag. Every
predicate is a conclusion of the physical components at its raw caller; this
lemma installs no input, counter or runtime semantic operation. -/
private theorem relation {a m n z : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m) (f : Fin 4) (mm : Nat)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (physical : 9+2*z+2^n < a+m) (virtual : a+m ≤ Cursor.Target.M k n z)
    (flagEq : flag mm=f.val)
    (table : f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0)
    (guard :
      (value (padRead (Fin.append x w)) (a+m) (9+2*z+2^n) (bitLength (Cursor.Target.W k n)) 0 ≤ Cursor.Target.W k n ∧
        (bad mm=0 ↔ ∀ j,min (9+2*z+2^n+bitLength (Cursor.Target.W k n)) (a+m) ≤ j →
          j < a+m → padRead (Fin.append x w) j=false)) ∨
      (Cursor.Target.W k n < value (padRead (Fin.append x w)) (a+m) (9+2*z+2^n) (bitLength (Cursor.Target.W k n)) 0 ∧ bad mm≠0)) :
    (0<n ∧ flag mm%2=1 ∧ bad mm=0) ↔ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true:=by
  let p:=9+2*z+2^n
  let W:=Cursor.Target.W k n
  let ell:=bitLength W
  let i:=value (padRead (Fin.append x w)) (a+m) p ell 0
  have addressEq:=address k (Fin.append x w) header
  have read:=valueRead (Fin.append x w) (M:=Cursor.Target.M k n z) p ell (by
    change p+ell ≤ p+ell+W
    exact Nat.le_add_right _ _)
  rw [Nat.min_eq_left physical.le] at read
  have sourceRead : readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some i:=by
    rw [addressEq,indexStart,indexWidth]
    exact read
  have semantic:=virtualTest k x w canonical header tag sourceRead (by rw [addressEq];exact virtual)
  have payload:=exactWindow (Fin.append x w) p ell W virtual
  have tableStart : tagLen+(2*z+1)=9+2*z:=by change 8+(2*z+1)=9+2*z;omega
  have semanticExact : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      0<n ∧ i ≤ W ∧ (∀ j,min (p+ell) (a+m) ≤ j → j < a+m → padRead (Fin.append x w) j=false) ∧
        f.val%2=1:=by
    rw [width,indexWidth,tableStart] at semantic
    constructor
    · intro accepted
      obtain ⟨positive,fits,zero,whole⟩:=semantic.mp accepted
      exact ⟨positive,fits,payload.mp zero,table.mpr whole⟩
    · rintro ⟨positive,fits,zero,whole⟩
      exact semantic.mpr ⟨positive,fits,payload.mpr zero,table.mp whole⟩
  rw [flagEq]
  rcases guard with ⟨fits,clean⟩|⟨outside,dirty⟩
  · rw [clean]
    constructor
    · rintro ⟨positive,whole,zero⟩
      exact semanticExact.mpr ⟨positive,fits,zero,whole⟩
    · intro accepted
      obtain ⟨positive,_fits,zero,whole⟩:=semanticExact.mp accepted
      exact ⟨positive,whole,zero⟩
  · constructor
    · rintro ⟨_positive,_whole,clean⟩
      exact (dirty clean).elim
    · intro accepted
      have fits:=(semanticExact.mp accepted).2.1
      exact (Nat.not_lt_of_ge fits outside).elim
#print axioms relation
end VirtualFinalClosure.GuardFinalMeaning
