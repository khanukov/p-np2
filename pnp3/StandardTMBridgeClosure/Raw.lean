import StandardTMBridgeClosure.Facts
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing Lean Elab Command
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`StandardTMBridgeClosure.Simulation,"steps_prefix"),
      (`StandardTMBridgeClosure.Simulation,"ready_reflect"),
      (`StandardTMBridgeClosure.Facts,"virtual_fresh"),(`StandardTMBridgeClosure.Facts,"ready_halt")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "StandardTMBridgeClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact raw bridge interface {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing raw bridge owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong raw bridge owner"
    logInfo m!"typed-private-interface|{owner}|{n}|kind=theorem|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
/-- The connected original-raw NORMAL → actual standard unbounded-tape TM0
execution theorem. The compiler receives only the unchanged finite machine. -/
theorem raw (k : Nat) : Target.Raw k := by
  intro N y M G c start virtual
  obtain ⟨d,t,_growth,order,price,_sharp,clock,room,_ambient,_decision,history,oldSafe,oldFirst,first,outcome⟩:=
    NormalClockClosure.bridge k N y
  have source:Target.Source k N y d t:=⟨order,price,history,oldSafe,oldFirst,first,outcome⟩
  have safe:∀ u,u < t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject:=
    fun u hu=>⟨(first u hu).1,(first u hu).2.1⟩
  have rightRoom:∀ u,u < t → (M.step (M.run u c).state ((M.run u c).tape (M.run u c).head)).2.2=Move.right →
      (M.run u c).head.val+1 < tapeLength N G:=fun u hu _=>room u hu.le
  obtain ⟨macros,_midpoints⟩:=simulation M N G t y safe rightRoom
  obtain ⟨last,trace,rep⟩:=macros t le_rfl
  have budget:1+2*t ≤ polyClock (degree k) N:=by
    calc 1+2*t ≤ 1+2*polyClock (NormalClockClosure.degree k) N:=by have p:=price.trans clock;omega
         _ ≤ polyClock (degree k) N:=degree_bound k N
  refine ⟨d,t,last,source,budget,trace,rep,macros,?_,?_,?_⟩
  · intro j hj
    exact steps_prefix M (1+2*t) j start last trace hj
  · intro j jt v hv
    refine ⟨?_,?_,fun b=>?_⟩
    · intro hit
      obtain ⟨u,ut,eq⟩:=ready_reflect M N G t y safe rightRoom j jt v hv M.accept hit
      exact (first u ut).1 eq.symm
    · intro hit
      obtain ⟨u,ut,eq⟩:=ready_reflect M N G t y safe rightRoom j jt v hv M.reject hit
      exact (first u ut).2.1 eq.symm
    · intro hit
      obtain ⟨u,ut,eq⟩:=ready_reflect M N G t y safe rightRoom j jt v hv (virtual b) hit
      exact (first u ut).2.2 b eq.symm
  · rcases outcome with ⟨_td,⟨b,work⟩,ending⟩|⟨_td,rejected,failed,ending⟩|normal
    · have state:(M.run t c).state=virtual b:=by
        rw [ending]
        change NormalFinalClosure.old2 k _=virtual b
        rw [work]
      have label:last.q=some (virtual b,0):=rep.1.trans (congrArg (fun q=>some (q,0)) state)
      refine Or.inl ⟨b,label,?_⟩
      intro halt
      have bad:virtual b=M.accept ∨ virtual b=M.reject:=(ready_halt M last (virtual b) label).mp halt
      rcases bad with bad|bad
      · exact (virtual_fresh k b).1 bad
      · exact (virtual_fresh k b).2 bad
    · have state:(M.run t c).state=M.reject:=by
        rw [ending]
        change NormalFinalClosure.old2 k _=M.reject
        rw [rejected]
        rfl
      have label:last.q=some (M.reject,0):=rep.1.trans (congrArg (fun q=>some (q,0)) state)
      exact Or.inr ⟨false,failed.symm,label,(ready_halt M last M.reject label).mpr (Or.inr rfl)⟩
    · rcases normal with ⟨a,m,x,w,hN,_decoded,_word,_length,n,z,_tag,_gamma,_header,
          _physical,_ell,_window,_rows,hH,_head,answer,encoded,_rho,_prefix,ending⟩
      have state:(M.run t c).state=(if answer then M.accept else M.reject):=congrArg Config.state ending
      have label:last.q=some ((if answer then M.accept else M.reject),0):=
        rep.1.trans (congrArg (fun q=>some (q,0)) state)
      refine Or.inr ⟨answer,encoded,label,(ready_halt M last _ label).mpr ?_⟩
      cases answer with
      | false=>exact Or.inr rfl
      | true=>exact Or.inl rfl
end StandardTMBridgeClosure
