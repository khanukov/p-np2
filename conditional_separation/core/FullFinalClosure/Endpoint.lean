import FullFinalClosure.Clock
import FullFinalClosure.Witnesses
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`FullFinalClosure.Raw,["raw_complete"]),(`FullFinalClosure.Clock,["clock_complete","concrete_verifier"]),
      (`FullFinalClosure.Witnesses,["original_witnesses"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `FullFinalClosure) leaf
      let some (.thmInfo ci):=e.find? n | throwError "Missing exact concrete class interface {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing concrete class owner"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong concrete class owner"
      logInfo m!"registered-interface|{owner}|{n}|theorem|{(repr ci.type).pretty 1000000000}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private theorem full_endpoint (k : Nat) : Target.Full k := by
  have v:=concrete_verifier k
  have w:=original_witnesses k
  have np:UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))):=
    ⟨PartAEndpoint.thresholdContentWitnessRelation k,machine k,degree k,1,v,w⟩
  exact ⟨raw_complete k,clock_complete k,v,w,np,
    UniformClassBridgeClosure.verifier (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) v,
    UniformClassBridgeClosure.np_lift _ np⟩
#print axioms full_endpoint
end FullFinalClosure
