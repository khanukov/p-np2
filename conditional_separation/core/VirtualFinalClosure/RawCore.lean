import VirtualFinalClosure.SupportedRun
import VirtualFinalClosure.RejectedRaw
import VirtualFinalClosure.OldEarlyReject
import VirtualFinalClosure.OldGuardReject
namespace VirtualFinalClosure.RawCore
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.SupportedRun","VirtualFinalClosure.SupportedRun","classified","supported"),
      ("VirtualFinalClosure.RejectedRaw","VirtualFinalClosure.RejectedRaw","raw_reject","rawReject"),
      ("VirtualFinalClosure.OldEarlyReject","VirtualFinalClosure.OldEarlyReject","early","earlyReject"),
      ("VirtualFinalClosure.OldGuardReject","VirtualFinalClosure.OldGuardReject","malformed_prefix","malformedPrefix"),
      ("VirtualFinalClosure.OldGuardReject","VirtualFinalClosure.OldGuardReject","wrong_prefix","wrongPrefix"),
      ("TotalIngressClosure.FrontPartition","TotalIngressClosure","front_partition","frontPartition"),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique unconditional exact raw branch component {mod}/{key}"
/-- Complete execution on the frozen finite elastic table, for arbitrary raw
Option-Bool encoded input. No semantic, parse, fit, frame or desired-run premise
is supplied by the caller. Every case consumes its real first-arrival witness. -/
private theorem raw_core (k : Nat) : Target.Raw k:=by
  intro N y
  cases parsed:decodePair y with
  | none=>
    obtain ⟨t,tp,hit,heads,low⟩:=malformedPrefix k N y parsed
    obtain ⟨T,price,bounds,first,rejected⟩:=rawReject k N t y tp heads low hit
      (encodedRelationLanguage_malformed (PartAEndpoint.thresholdContentWitnessRelation k) y parsed)
    exact ⟨T,price,bounds,first,Or.inl rejected⟩
  | some decoded=>
    rcases decoded with ⟨⟨a,x⟩,⟨m,w⟩⟩
    have packed:(⟨N,y⟩:EncodedWord)=⟨pairLength a m,encodePair x w⟩:=(decodePair_eq_some_iff y _).1 parsed
    have length:N=pairLength a m:=congrArg Sigma.fst packed
    subst N
    have word:y=encodePair x w:=by cases packed;rfl
    subst y
    by_cases canonical:m=a+1
    · rcases frontPartition k x w with early|⟨n,z,tag,gamma,header,firstPhysical,cap,rows⟩
      · obtain ⟨t,tp,hit,heads,low⟩:=early
        obtain ⟨semantic,s,sp,oldHit,oldHeads,oldLow⟩:=earlyReject k x w canonical t tp hit heads low
        have sound:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) (pairLength a m) (encodePair x w)=false:=by
          simpa only [encodedRelationLanguage_encodePair] using semantic
        obtain ⟨T,price,bounds,first,rejected⟩:=rawReject k (pairLength a m) s (encodePair x w) sp oldHeads oldLow oldHit sound
        exact ⟨T,price,bounds,first,Or.inl rejected⟩
      · obtain ⟨T,hH,price,bounds,first,outcome⟩:=supported k x w canonical header tag gamma firstPhysical cap rows
        obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
        obtain ⟨arena,_source,_eof,_reg,_sep,_assn,_last,_marks,_gap,_fence⟩:=cells
        refine ⟨T,price,bounds,first,Or.inr ⟨a,m,x,w,rfl,rfl,rfl,canonical,
          n,z,hH,tag,gamma,header,cap,arena,?_⟩⟩
        rcases outcome with normal|virtual
        · exact Or.inl normal
        · right
          simpa only [encodedRelationLanguage_encodePair] using virtual
    · obtain ⟨t,tp,hit,heads,low⟩:=wrongPrefix k x w canonical
      have sound:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) (pairLength a m) (encodePair x w)=false:=by
        simpa only [encodedRelationLanguage_encodePair] using CertificateGuardClosure.wrong_length k x w canonical
      obtain ⟨T,price,bounds,first,rejected⟩:=rawReject k (pairLength a m) t (encodePair x w) tp heads low hit sound
      exact ⟨T,price,bounds,first,Or.inl rejected⟩
#print axioms raw_core
end VirtualFinalClosure.RawCore
