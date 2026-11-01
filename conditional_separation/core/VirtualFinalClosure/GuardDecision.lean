import VirtualFinalClosure.GuardTagMeaning
import VirtualFinalClosure.GuardNecessity
namespace VirtualFinalClosure.GuardDecision
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.GuardTagMeaning","VirtualFinalClosure.GuardTagMeaning","tag_read","tagRead"),
      ("VirtualFinalClosure.GuardNecessity","VirtualFinalClosure.GuardNecessity","necessary","necessary")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original relation/BE semantic term {mod}/{key}"
/-- Exact ORIGINAL relation partition on a virtual witness. Parser success and
both active-prefix/inactive-padding conditions are conclusions of the checked
native predicates, not premises added to the machine's raw contract. -/
private theorem virtual_test {a m n consumed index : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (indexRead : readNatBE (padWord (Fin.append x w)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n))
      (tagLen+consumed+Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)=some index)
    (virtual : a+m ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      0<n ∧ index ≤ (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n ∧
      (∀ j : Fin ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n),
        padRead (Fin.append x w) (tagLen+consumed+Pnp3.Models.Partial.tableLen n+
          idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n+j.val)=false) ∧
      ∀ j : Fin (2^n),padRead (Fin.append x w) (tagLen+consumed+j.val)=Nat.testBit j.val 0 := by
  have validTag:=tagRead (Fin.append x w) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n)
    (by unfold treeMCSPPrefixM;omega) tag
  constructor
  · intro accepted
    obtain ⟨positive,fits,zero⟩:=necessary k x w header indexRead virtual accepted
    refine ⟨positive,fits,zero,?_⟩
    exact (GuardMeaning.checked_guard_acceptance k x w canonical positive header validTag indexRead fits zero virtual).mp accepted
  · rintro ⟨positive,fits,zero,table⟩
    exact (GuardMeaning.checked_guard_acceptance k x w canonical positive header validTag indexRead fits zero virtual).mpr table
#print axioms virtual_test
end VirtualFinalClosure.GuardDecision
