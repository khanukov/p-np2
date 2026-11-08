import CertificateGuardClosure.Raw
import TotalIngressClosure.Fixtures
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Pnp4.Frontier.ContractExpansion Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.CertificateGuardClosure." || n.toString.startsWith "_private.TotalIngressClosure.Fixtures."
  for (mod,ns,key,aliasName) in [("CertificateGuardClosure.Raw","CertificateGuardClosure","room","tapeRoom"),("CertificateGuardClosure.Raw","CertificateGuardClosure","parser_room","parserRoom"),("CertificateGuardClosure.Raw","CertificateGuardClosure","total_price","totalPrice"),("CertificateGuardClosure.GuardRun","CertificateGuardClosure","guard_run","guardRun"),("CertificateGuardClosure.Sequence","CertificateGuardClosure","gate_entry","gateEntry"),("CertificateGuardClosure.Sequence","CertificateGuardClosure","include_suffix","includeSuffix"),("TotalIngressClosure.Fixtures","TotalIngressClosure","tiny_connected","tinyConnected")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique same-word nonvacuity interface {mod}/{key}: {found.map Prod.fst}"
private theorem tiny_raw :
    let x:Bitstring 7:=fun i=>i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w:Bitstring 8:=fun i=>i.val==2 || i.val==5
    PartAEndpoint.thresholdContentWitnessRelation 0 7 8 x w=true ∧
      ∃ t,t ≤ deadline 0 (pairLength 7 8) ∧
        ((machine 0).run t (initialConfig (machine 0) (allocation 0 (pairLength 7 8)) (encodePair x w))).state=
          old 0 (TotalIngressClosure.old 0 (BodyIngress.old 0 (CarryWindow.embed 0 (CanonicalLeaf.result 0 false)))) := by
  intro x w
  obtain ⟨accepted,t,price,result⟩:=tinyConnected
  refine ⟨accepted,?_⟩
  let N:=pairLength 7 8;let y:=encodePair x w;let B:=allocation 0 N
  let M:=machine 0;let O:=TotalIngressClosure.machine 0
  obtain ⟨h,hprice,_heads,first,done⟩:=guardRun (B:=B) x w (tapeRoom 0 N)
  rw [if_pos (show 8=7+1 by decide)] at done
  have entry:M.run (FixedPairParser.clock N+h) (initialConfig M B y)=config 0 (initialConfig O B y):=
    gateEntry O y (parserRoom 0 N) _ (decodePair_roundtrip x w) (fun u hu=>(first u hu).1) done
  have hp:h ≤ 64*(N+1)^2 := hprice
  have gp:=Nat.add_le_add_left hp (FixedPairParser.clock N)
  refine ⟨(FixedPairParser.clock N+h)+t,totalPrice 0 N _ t gp price,?_⟩
  rw [UniformTM.run_add,entry]
  have suffix:M.run t (config 0 (initialConfig O B y))=config 0 (O.run t (initialConfig O B y)):=
    includeSuffix O (initialConfig O B y) t
  change (M.run t (config 0 (initialConfig O B y))).state=_
  rw [suffix]
  change old 0 ((O.run t (initialConfig O B y)).state)=_
  exact congrArg (old 0) result
#print axioms tiny_raw
end CertificateGuardClosure
