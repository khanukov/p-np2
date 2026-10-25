import TotalIngressClosure.TableReject
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.RepairHeads","TotalIngressClosure","repair_head_origin","repairOrigin"),
      ("TotalIngressClosure.RepairHeads","TotalIngressClosure","repaired_heads","repairHeads"),
      ("TotalIngressClosure.LiftLow","TotalIngressClosure","earlyEmbed","lowEmbed"),
      ("TotalIngressClosure.LiftLow","TotalIngressClosure","lift_low_prefix","liftLow"),
      ("TotalIngressClosure.TableReject","TotalIngressClosure","low_value","lowValue"),
      ("TotalIngressClosure.TableReject","TotalIngressClosure","low_reject","lowReject")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique actual rejected producer prefix {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem producer_reject_lift (k : Nat) {a m : Nat} (x:Bitstring a) (w:Bitstring m) (T P : Nat)
    (hit:(SmallIngress.producer.run T (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.reject)
    (heads:∀ u,u ≤ T → (SmallIngress.producer.run u (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ P) :
    let B:=FixedRawLengthFence.allocation (pairLength a m)
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ((BodyIngress.machine k).run T c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ T → ((BodyIngress.machine k).run u c).head.val ≤ P) ∧
      (∀ u,u ≤ T → ((BodyIngress.machine k).run u c).state.val < 352):=by
  intro B c
  let producer:=initialConfig SmallIngress.producer B (encodePair x w)
  let old:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have noAccept(u : Nat)(hu:u ≤ T):(SmallIngress.producer.run u producer).state≠SmallIngress.producer.accept:=by
    intro bad
    have stay:=SmallIngress.producer.run_accept_of_le producer bad hu
    have wrong:(SmallIngress.producer.run T producer).state=SmallIngress.producer.accept:=(congrArg Config.state stay).trans bad
    rw [hit] at wrong
    exact SmallIngress.producer.accept_ne_reject wrong.symm
  have seqRun(u : Nat)(hu:u ≤ T):(AllArityCursor.machine k).run u old=
      SmallIngress.producer.seqEmbedRouted (Cursor.machine k) (SmallIngress.producer.run u producer):=
    SmallIngress.producer.seq_run_left (Cursor.machine k) producer (T:=T)
      (by intro u hu;exact noAccept u (Nat.le_of_lt hu)) u hu
  have oldLow(u : Nat)(hu:u ≤ T):((AllArityCursor.machine k).run u old).state.val < 352:=by
    rw [seqRun u hu]
    change (SmallIngress.producer.seqRoute (Cursor.machine k) (SmallIngress.producer.run u producer).state).val < 352
    unfold UniformTM.seqRoute
    rw [if_neg (noAccept u hu)]
    split_ifs
    · change (328:Nat) < 352;decide
    · exact (SmallIngress.producer.run u producer).state.isLt.trans (by decide)
  have repairedLow(u : Nat)(hu:u ≤ T):((IngressRepair.machine k).run u old).state.val < 352:=by
    rcases repairOrigin k old u with same | ⟨rejected,_⟩
    · rw [same];exact oldLow u hu
    · rw [rejected];change (328:Nat) < 352;decide
  have oldHeads(u : Nat)(hu:u ≤ T):((AllArityCursor.machine k).run u old).head.val ≤ P:=by
    rw [seqRun u hu];exact heads u hu
  have repairedHeads:=repairHeads k old T P oldHeads
  have tx:=liftLow k old (t:=T) (by intro u hu;exact (repairedLow u hu).le.trans (by decide))
  have txRun(u:Nat)(hu:u ≤ T):(BodyIngress.machine k).run u c=lowEmbed ((IngressRepair.machine k).run u old):=tx u hu
  have oldReject:((AllArityCursor.machine k).run T old).state=(AllArityCursor.machine k).reject:=by
    rw [seqRun T le_rfl]
    change SmallIngress.producer.seqRoute (Cursor.machine k) (SmallIngress.producer.run T producer).state=_
    rw [hit]
    rfl
  have rejected:=IngressRepair.reject_preserved k old T oldReject
  refine ⟨?_,?_,?_⟩
  · exact (congrArg Config.state (txRun T le_rfl)).trans (lowReject _ rejected)
  · intro u hu
    rw [txRun u hu]
    exact repairedHeads u hu
  · intro u hu
    rw [txRun u hu,lowValue]
    exact repairedLow u hu
end TotalIngressClosure
