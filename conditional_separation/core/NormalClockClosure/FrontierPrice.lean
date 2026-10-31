import NormalClockClosure.CallerPrice
import RawCallerClosure.Driver
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName) in [
      (`RawCallerClosure.Prefix,`RawCallerClosure,"prefix_facts","prefixFacts"),
      (`RawCallerClosure.IngressResult,`RawCallerClosure,"ingress_result","ingressResult"),
      (`RawCallerClosure.Rows,`RawCallerClosure,"old_reject","oldReject"),
      (`RawCallerClosure.Rows,`RawCallerClosure,"caller_run","callerRun"),
      (`RawCallerClosure.Work,`RawCallerClosure,"caller_reject","callerReject"),
      (`NormalClockClosure.CallerPrice,`NormalClockClosure,"cheap_caller","cheapCaller"),
      (`NormalClockClosure.Arithmetic,`NormalClockClosure,"front_price","frontPrice")] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact raw price theorem {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing raw price owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong raw price owner"
    logInfo m!"raw-price-interface|{owner}|{n}|kind=theorem|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def OldBoundary (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount) : Prop :=
    q=(RawCallerClosure.machine k).reject ∨
    q=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) ∨
    ∃ b,q=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
/-- Unconditional raw origin; an actual bounded terminal/WORK execution, with
all rejected syntactic/length/header/cap arms retained. No caller parse premise. -/
private theorem cheap_frontier (k N : Nat) (y : Bitstring N) :
    ∃ t,t ≤ 274877906944*(k+1)*(N+1)^7 ∧
      OldBoundary k ((RawCallerClosure.machine k).run t
        (initialConfig (RawCallerClosure.machine k) (RawCallerClosure.allocation k N) y)).state := by
  let B:=RawCallerClosure.allocation k N
  let O:=RawCallerClosure.machine k
  let C:=initialConfig O B y
  obtain ⟨pre,front⟩:=CertificateGuardClosure.raw k N y
  have front:RawCallerClosure.Target.Prelude k N y pre:=front
  obtain ⟨same,_safe,_first⟩:=prefixFacts k N y pre front
  have pp:pre ≤ 137438953472*(k+1)*(N+1)^6:=front.1
  rcases ingressResult k N y pre front (same pre le_rfl) with ⟨reject,_falseLanguage⟩|⟨b,work⟩|normal
  · refine ⟨pre,?_,Or.inl ?_⟩
    · simpa only [Nat.add_zero] using frontPrice k N pre 0 pp (by omega)
    · have state:=congrArg Config.state (same pre le_rfl)
      change (O.run pre C).state=RawCallerClosure.old k _ at state
      rw [reject,oldReject] at state
      exact state
  · refine ⟨pre,?_,Or.inr (Or.inr ⟨b,?_⟩)⟩
    · simpa only [Nat.add_zero] using frontPrice k N pre 0 pp (by omega)
    · have state:=congrArg Config.state (same pre le_rfl)
      change (O.run pre C).state=RawCallerClosure.old k _ at state
      exact state.trans (congrArg (RawCallerClosure.old k) work)
  · rcases normal with ⟨a,m,x,w,_hN,_decoded,_word,_length,n,z,_tag,_gamma,_header,
        _physical,_ell,_window,_capacity,_arena,layout,hH,handoff⟩
    have hhEq:a+m+z+2+n+1=a+m+z+n+3:=by omega
    simp only [hhEq] at hH handoff
    have hH':a+m+z+n+3 < tapeLength N B:=hH
    obtain fail|done:=cheapCaller k B N (a+m) z n _ (n^k+k) (Cursor.Target.W k n)
      (Cursor.Target.M k n z) (9+2*z) (2^n) (Fin.append x w) _ layout hH'
    · obtain ⟨u,up,ending⟩:=fail
      refine ⟨pre+u,frontPrice k N pre u pp up,Or.inl ?_⟩
      rw [UniformTM.run_add,handoff,callerRun]
      change RawCallerClosure.callerState k _=O.reject
      exact (congrArg (RawCallerClosure.callerState k) ending).trans (callerReject k)
    · obtain ⟨u,up,ending⟩:=done
      refine ⟨pre+u,frontPrice k N pre u pp up,Or.inr (Or.inl ?_)⟩
      rw [UniformTM.run_add,handoff,callerRun]
      change RawCallerClosure.callerState k _=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
      exact congrArg (RawCallerClosure.callerState k) ending
/-- FIRSTness identifies the same actual time; no unrelated witness/deadline
is silently substituted for the sealed raw frontier. -/
private theorem first_frontier_price (k N : Nat) (y : Bitstring N) (d : Nat)
    (first:∀ u,u < d → ¬OldBoundary k ((RawCallerClosure.machine k).run u
      (initialConfig (RawCallerClosure.machine k) (RawCallerClosure.allocation k N) y)).state) :
    d ≤ 274877906944*(k+1)*(N+1)^7 := by
  obtain ⟨u,bound,actual⟩:=cheap_frontier k N y
  have order:d ≤ u:=by by_contra bad;exact first u (by omega) actual
  exact order.trans bound
end NormalClockClosure
