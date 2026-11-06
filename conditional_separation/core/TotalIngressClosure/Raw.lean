import TotalIngressClosure.CanonicalTransport
import TotalIngressClosure.Malformed
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("CanonicalTransport","canonical_raw","canonicalRaw"),("Malformed","malformed_branch","malformedBranch")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique arbitrary-word final assembly {mod}/{key}: {found.map Prod.fst}"
/-- Every raw word reaches the first ingress consumer, under the frozen
length-only allocation and clock. Work leaf results retain their value semantics. -/
theorem raw (k:Nat) : Target.Raw k:=by
  intro N y
  cases parsed:decodePair y with
  | none=>
    obtain ⟨t,price,heads,safe,first,clock,done,negative⟩:=malformedBranch k y parsed
    exact ⟨t,price,heads,safe,first,Or.inl ⟨rfl,clock,done,negative⟩⟩
  | some p=>
    rcases p with ⟨⟨a,x⟩,⟨m,w⟩⟩
    have packed: (⟨N,y⟩:EncodedWord)=⟨pairLength a m,encodePair x w⟩:=(decodePair_eq_some_iff y _).1 parsed
    have length:N=pairLength a m:=congrArg Sigma.fst packed
    subst N
    have word:y=encodePair x w:=by cases packed;rfl
    subst y
    obtain ⟨t,price,heads,safe,first,d,clock,suffixRun,hBudget,initial,foot,room,trace,done,outcome⟩:=canonicalRaw k x w
    exact ⟨t,price,heads,safe,first,Or.inr ⟨a,m,x,w,rfl,rfl,rfl,d,clock,suffixRun,hBudget,initial,foot,room,trace,done,outcome⟩⟩
end TotalIngressClosure
