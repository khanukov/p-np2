import TotalIngressClosure.Header
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("parser_room","parserRoom"),("prefix_heads","parserHeads"),
      ("prefix_states","parserStates"),("malformed","parserReject")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.TotalIngressClosure.Gate." && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique exact parser theorem {key}: {found.map Prod.fst}"
private theorem parser_clock (k N : Nat) : FixedPairParser.clock N ≤ deadline k N := by
  have small:FixedPairParser.clock N ≤ 16*(N+1)^2:=by
    change 2*N+1 ≤ 16*(N+1)^2
    nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
  have p:(N+1)^2 ≤ (N+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  exact small.trans (Nat.mul_le_mul (by omega:16 ≤ 68719476736*(k+1)) p)
private theorem head_envelope (N : Nat) : N ≤ 12*(N+1)^2:=by
  nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
private theorem malformed_branch (k : Nat) {N : Nat} (y : Bitstring N)
    (bad:PairEncoding.decodePair y=none) :
    let M:=machine k;let c:=initialConfig M (allocation k N) y
    ∃ t,t ≤ deadline k N ∧
      (∀ u,u ≤ t → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (M.run u c).state ≠ M.accept) ∧
      (∀ u,u < t → (M.run u c).state ≠ M.reject ∧
        (∀ b,(M.run u c).state ≠ old k (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))) ∧
        (∀ mode:Fin 3,(M.run u c).state ≠ old k (BodyIngress.body k (SerializedBody.entry mode)))) ∧
      t=FixedPairParser.clock N ∧
      M.run t c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false := by
  let M:=machine k;let B:=allocation k N;let c:=initialConfig M B y
  have room:=parserRoom k N
  have done:=parserReject k y room bad
  have rejected:(M.run (FixedPairParser.clock N) c).state=M.reject:=congrArg Config.state done
  refine ⟨FixedPairParser.clock N,parser_clock k N,?_,?_,?_,rfl,done,?_⟩
  · intro u hu
    exact (parserHeads k y room u hu).trans (head_envelope N)
  · intro u hu accepted
    have same:=M.run_accept_of_le c accepted hu
    have equal:=congrArg Config.state same
    rw [rejected,accepted] at equal
    exact M.accept_ne_reject equal.symm
  · intro u hu
    have low : (M.run u c).state.val < 10:=parserStates k y room u hu
    have absent(q : Fin (BodyIngress.machine k).stateCount):(M.run u c).state ≠ old k q:=by
      intro hit
      have value:=congrArg Fin.val hit
      change (M.run u c).state.val=10+q.val at value
      omega
    exact ⟨absent (BodyIngress.machine k).reject,fun b=>absent _,fun mode=>absent _⟩
  · exact encodedRelationLanguage_malformed _ y bad
end TotalIngressClosure
