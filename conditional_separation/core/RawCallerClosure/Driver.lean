import RawCallerClosure.IngressResult
import RawCallerClosure.RowsRun
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf,aliasName) in [(`RawCallerClosure.Prefix,"prefix_facts","prefixFacts"),
    (`RawCallerClosure.IngressResult,"ingress_result","ingressResult"),
    (`RawCallerClosure.RowsRun,"rows_run","rowsRun"),(`RawCallerClosure.RowsRun,"rows_terminal","rowsTerminal"),
    (`RawCallerClosure.Work,"no_work_to_finish","noWorkToFinish"),(`RawCallerClosure.Arithmetic,"raw_rows_price","rawRowsPrice")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "RawCallerClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact connected raw proof term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong connected raw owner"
    logInfo m!"ordinary-raw-driver|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
/-- Every raw word executes the fixed guard/ingress/caller composite to its
strict first reject, preserved virtual WORK, or complete normal all-row result. -/
theorem raw (k : Nat) : Target.Raw k := by
  intro N y
  let B:=allocation k N
  let C:=initialConfig (machine k) B y
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G B y
  obtain ⟨pre,front⟩:=CertificateGuardClosure.raw k N y
  have front:Target.Prelude k N y pre:=front
  obtain ⟨same,safe,first⟩:=prefixFacts k N y pre front
  have preprice:pre≤137438953472*(k+1)*(N+1)^6:=front.1
  have earlyPrice:pre≤deadline k N:=by
    simpa only [Nat.add_zero] using rawRowsPrice k N pre 0 preprice (by omega)
  rcases ingressResult k N y pre front (same pre le_rfl) with ⟨rejected,bad⟩|⟨b,work⟩|normal
  · exact ⟨pre,pre,front,le_rfl,earlyPrice,same,safe,first,Or.inl ⟨rfl,rejected,same pre le_rfl,bad⟩⟩
  · exact ⟨pre,pre,front,le_rfl,earlyPrice,same,safe,first,Or.inr (Or.inl ⟨rfl,⟨b,work⟩,same pre le_rfl⟩)⟩
  · rcases normal with ⟨a,m,x,w,hN,parsed,word,length,n,z,tag,gamma,header,physical,ellFits,wFits,capacity,arena,layout,hH,handoff⟩
    let S:=a+m
    let r:=S-min (9+2*z+2^n) S
    let W:=Cursor.Target.W k n
    let address:=Cursor.Target.M k n z
    obtain ⟨elapsed,localPrice,rows⟩:=rowsRun k B N S z n r (n^k+k) W address (9+2*z) (2^n) (Fin.append x w) _
      layout hH C pre handoff safe (fun u hu=>⟨(first u hu).1,(first u hu).2.1⟩)
    have terminal:=rowsTerminal k B N S z n r (n^k+k) W address (9+2*z) (2^n) (Fin.append x w) _ hH C (pre+elapsed) rows
    have noVirtual:=noWorkToFinish k C terminal
    refine ⟨pre,pre+elapsed,front,by omega,rawRowsPrice k N pre elapsed preprice localPrice,same,rows.1,?_,Or.inr (Or.inr ?_)⟩
    · intro u hu
      exact ⟨(rows.2.1 u hu).1,(rows.2.1 u hu).2,noVirtual u hu.le⟩
    · exact ⟨a,m,x,w,hN,parsed,word,length,n,z,tag,gamma,header,physical,ellFits,wFits,capacity,arena,hH,handoff,rows⟩
#print axioms raw
end RawCallerClosure
