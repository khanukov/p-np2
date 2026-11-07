import FullFinalClosure.Raw
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`FullFinalClosure.Raw,"raw_complete"),(`FullFinalClosure.Arithmetic,"clock_allocation")] do
    let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `FullFinalClosure) leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact concrete clock interface {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing concrete clock owner"
    unless e.header.moduleNames[i]! == owner do throwError "Wrong concrete clock owner"
    logInfo m!"registered-interface|{owner}|{n}|theorem|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private theorem clock_complete (k : Nat) : Target.Clock k := by
  refine ⟨clock_allocation k 0,clock_allocation k,?_⟩
  intro N y
  obtain ⟨d,t,_dt,price,_history,_firstA,_first,room,ending,_coupling⟩:=raw_complete k N y
  let C:=allocation k N
  let M:=machine k
  let P:=polyClock (degree k) N
  have time:t≤P:=by
    have cp:=clock_allocation k N
    unfold allocation at cp
    dsimp only [P]
    omega
  have extension:∀ (B : Nat) (h:C≤B),∀ u,u≤t → FixedPairParser.ConfigExtension h
      (M.run u (initialConfig M C y)) (M.run u (initialConfig M B y)):=by
    intro B h u hu
    exact FixedPairParser.run_extension M h (FixedPairParser.initialConfig_extension M h y) u
      (fun v hv=>room v (by omega))
  have large:(M.run t (initialConfig M P y)).state=
      (if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y then M.accept else M.reject):=
    (extension P (clock_allocation k N) t le_rfl).1.symm.trans ending
  have stable:M.run P (initialConfig M P y)=M.run t (initialConfig M P y):=by
    calc M.run P (initialConfig M P y)=M.run (t+(P-t)) (initialConfig M P y):=
           congrArg (fun steps=>M.run steps (initialConfig M P y)) (by omega)
         _ = M.run (P-t) (M.run t (initialConfig M P y)):=M.run_add _ _ _
         _ = M.run t (initialConfig M P y):=by
           cases answer:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
           · rw [answer] at large
             exact M.run_reject _ large _
           · rw [answer] at large
             exact M.run_accept _ large _
  have decides:DecidesAt M P P y (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y):=by
    cases answer:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
    · change (M.run P (initialConfig M P y)).state=M.reject
      rw [stable]
      simpa only [answer,Bool.false_eq_true,if_false] using large
    · change (M.run P (initialConfig M P y)).state=M.accept
      rw [stable]
      simpa only [answer,if_true] using large
  exact ⟨t,price,extension,stable,decides,(decidesAt_budget_iff_decidesWithin M y _).mp decides⟩
private theorem concrete_verifier (k : Nat) :
    VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) := by
  intro N y
  obtain ⟨_t,_price,_extension,_stable,_at,within⟩:=(clock_complete k).2.2 N y
  exact within
end FullFinalClosure
