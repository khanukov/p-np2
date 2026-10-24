import TotalIngressClosure.TableReject
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("LiftLow","earlyEmbed","lowEmbed"),("LiftLow","lift_low_prefix","liftLow"),
      ("TableReject","low_value","lowValue")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") &&
      n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique repaired missing-FIRST lift {key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem missing_first (k : Nat) {a m z : Nat} (x:Bitstring a) (w:Bitstring m)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (positive:0 < z) (short:a+m=9+z) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ∃ t,t ≤ 12*(R+1)^2 ∧ ((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).state.val < 352):=by
  intro R B c
  let repaired:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  obtain ⟨t,h,_coarse,done,before,_safe⟩:=IngressRepair.missing_payload_run k x w z tag gamma positive short
  have low(u : Nat)(hu:u ≤ t):((IngressRepair.machine k).run u repaired).state.val < 352:=by
    by_cases early:u < t
    · exact (before u early).trans (by decide)
    · have eq:u=t:=by omega
      rw [eq,done]
      change (328:Nat) < 352
      decide
  have tx:=liftLow k repaired (t:=t) (by intro u hu;exact (low u hu).le.trans (by decide))
  have txRun(u:Nat)(hu:u ≤ t):(BodyIngress.machine k).run u c=lowEmbed ((IngressRepair.machine k).run u repaired):=tx u hu
  have final:((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject:=by
    rw [txRun t le_rfl,done]
    rfl
  obtain ⟨_budget,_initial,T,_hS,price,whole,heads,_room,_trace,_end,_rejected,_safe,_negative⟩:=
    IngressAllocation.missing_payload k x w z tag gamma positive short
  have order:t ≤ T:=by
    by_contra no
    have bound:((IngressRepair.machine k).run T repaired).state.val < 139:=before T (by omega)
    have value:((IngressRepair.machine k).run T repaired).state.val=328:=by
      have same:=congrArg (fun cfg=>cfg.state.val) (txRun T (by omega))
      have rejected:((BodyIngress.machine k).run T c).state=(BodyIngress.machine k).reject:=by rw [whole]
      change ((BodyIngress.machine k).run T c).state.val=(lowEmbed ((IngressRepair.machine k).run T repaired)).state.val at same
      rw [rejected,lowValue] at same
      exact same.symm
    omega
  refine ⟨t,order.trans price,final,?_,?_⟩
  · intro u hu
    exact heads u (hu.trans order)
  · intro u hu
    rw [txRun u hu,lowValue]
    exact low u hu
end TotalIngressClosure
