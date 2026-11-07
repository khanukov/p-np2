import TotalIngressClosure.TableReject
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("TableReject","small_reject_lift","smallLift"),
      ("TableReject","low_value","lowValue"),("TableReject","low_reject","lowReject"),
      ("LiftLow","lift_low_prefix","liftLow"),("LiftLow","earlyEmbed","lowEmbed")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") &&
      n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique same-table literal Stream rejection {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem stream_reject_lift (k : Nat) {a m z : Nat} (x:Bitstring a) (w:Bitstring m)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (T P : Nat)
    (hit:(SmallIngress.machine.run T (initialConfig SmallIngress.machine
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.machine.reject)
    (heads:∀ u,u ≤ T → (SmallIngress.machine.run u (initialConfig SmallIngress.machine
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ P) :
    let B:=FixedRawLengthFence.allocation (pairLength a m)
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ((BodyIngress.machine k).run T c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ T → ((BodyIngress.machine k).run u c).head.val ≤ P) ∧
      (∀ u,u ≤ T → ((BodyIngress.machine k).run u c).state.val < 352):=by
  intro B c
  let repaired:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  have tx:=smallLift k (encodePair x w) T hit
  have repair(u : Nat):(IngressRepair.machine k).run u repaired=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=
    IngressRepair.supported_transport k x w z tag gamma physical u
  have low(u : Nat)(hu:u ≤ T):((IngressRepair.machine k).run u repaired).state.val < 352:=by
    rw [repair,tx u hu]
    exact (SmallIngress.machine.run u (initialConfig SmallIngress.machine B (encodePair x w))).state.isLt
  have body:=liftLow k repaired (t:=T) (by intro u hu;exact (low u hu).le.trans (by decide))
  have bodyRun(u:Nat)(hu:u ≤ T):(BodyIngress.machine k).run u c=lowEmbed ((IngressRepair.machine k).run u repaired):=body u hu
  have rejected:((IngressRepair.machine k).run T repaired).state=(IngressRepair.machine k).reject:=by
    rw [repair,tx T le_rfl]
    apply Fin.ext
    change (SmallIngress.machine.run T (initialConfig SmallIngress.machine B (encodePair x w))).state.val=328
    rw [hit]
    rfl
  refine ⟨(congrArg Config.state (bodyRun T le_rfl)).trans (lowReject _ rejected),?_,?_⟩
  · intro u hu
    rw [bodyRun u hu,repair,tx u hu]
    exact heads u hu
  · intro u hu
    rw [bodyRun u hu,lowValue]
    exact low u hu
end TotalIngressClosure
