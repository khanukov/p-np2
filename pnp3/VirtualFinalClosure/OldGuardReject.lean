import VirtualFinalClosure.PairPrefix
import CertificateGuardClosure.Raw
namespace VirtualFinalClosure.OldGuardReject
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [
      ("GuardRun","guard_run","guardRun"),("Sequence","gate_low","gateLow"),
      ("Sequence","gate_heads","gateHeads"),("Sequence","gate_reject","gateReject"),
      ("Sequence","parser_low","parserLow"),("Raw","parser_room","parserRoom"),
      ("Raw","room","room"),("Raw","total_price","totalPrice"),
      ("Raw","head_envelope","headEnvelope"),("Raw","malformed","malformed")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private.CertificateGuardClosure."++mod++".") && name.toString.endsWith (".CertificateGuardClosure."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact physical pair/length rejection {mod}/{key}"
private theorem malformed_prefix (k N : Nat) (y : Bitstring N) (bad:decodePair y=none) :
    let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k N
    let c:=initialConfig O C y
    ∃ t,t ≤ CertificateGuardClosure.deadline k N ∧ (O.run t c).state=O.reject ∧
      (∀ u,u ≤ t → (O.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (O.run u c).state.val < 625):=by
  intro O C c
  obtain ⟨t,tp,heads,_safe,_first,clock,done⟩:=malformed k N y bad
  have hit : (O.run t c).state=O.reject:=congrArg (fun q=>q.state) done
  refine ⟨t,tp,hit,heads,?_⟩
  intro u hu
  by_cases early:u < t
  · have low:=parserLow (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k)) y (parserRoom k N) u (by omega)
    change (O.run u c).state.val < 10 at low
    omega
  · have atTime:u=t:=by omega
    rw [atTime,hit]
    change 415 < 625
    decide
private theorem wrong_prefix (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (bad:m≠a+1) :
    let N:=pairLength a m;let y:=encodePair x w
    let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k N
    let c:=initialConfig O C y
    ∃ t,t ≤ CertificateGuardClosure.deadline k N ∧ (O.run t c).state=O.reject ∧
      (∀ u,u ≤ t → (O.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (O.run u c).state.val < 625):=by
  intro N y O C c
  have parsed:decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair):=decodePair_roundtrip x w
  obtain ⟨h,hp,heads,first,done⟩:=guardRun (B:=C) x w (room k N)
  rw [if_neg bad] at done
  let t:=FixedPairParser.clock N+h
  have hit : O.run t c=⟨O.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩:=
    gateReject (TotalIngressClosure.machine k) y (parserRoom k N) _ parsed (fun u hu=>(first u hu).1) done
  have bound:t ≤ FixedPairParser.clock N+64*(N+1)^2:=Nat.add_le_add_left hp _
  refine ⟨t,totalPrice k N t 0 bound (by omega),congrArg (fun q=>q.state) hit,?_,?_⟩
  · intro u hu
    exact (gateHeads (TotalIngressClosure.machine k) y (parserRoom k N) _ parsed
      (fun v hv=>(first v hv).1) heads (by omega) u hu).trans (headEnvelope N)
  · intro u hu
    by_cases early:u < t
    · have low:=gateLow (TotalIngressClosure.machine k) y (parserRoom k N) _ parsed first u early
      change (O.run u c).state.val < 77 at low
      omega
    · have atTime:u=t:=by omega
      rw [atTime,hit]
      change 415 < 625
      decide
#print axioms malformed_prefix
#print axioms wrong_prefix
end VirtualFinalClosure.OldGuardReject
