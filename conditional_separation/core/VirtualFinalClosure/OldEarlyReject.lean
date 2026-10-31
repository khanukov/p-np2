import VirtualFinalClosure.OldNormal
import TotalIngressClosure.FrontPartition
import TotalIngressClosure.RejectSound
namespace VirtualFinalClosure.OldEarlyReject
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("TotalIngressClosure.RejectSound","TotalIngressClosure","reject_sound","rejectSound",(1:Nat)),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1),
      ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth",1),
      ("IngressAllocation.Geometry","IngressAllocation","old_le_new","bodyBudget",1),
      ("IngressAllocation.Geometry","IngressAllocation","twelve_fields_bound","twelveBound",1),
      ("IngressAllocation.Extension","IngressAllocation","trace_of_room","traceRoom",1),
      ("IngressAllocation.Extension","IngressAllocation","extend_unique","uniqueExtension",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_room","smallRoom",1),
      ("VirtualFinalClosure.PairPrefix","VirtualFinalClosure.PairPrefix","raw_entry","pairPrefix",1),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","high_blank","imageHigh",1),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","extended_tape","extendTape",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_room","oldRoom",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","total","totalState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","extension","extendState",1),
      ("VirtualFinalClosure.OldNormal","VirtualFinalClosure.OldNormal","state_value","stateValue",1),
      ("VirtualFinalClosure.OldNormal","VirtualFinalClosure.OldNormal","body_value","bodyValue",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","guarded","guardedHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","total","totalHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","extension","extendHead",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","guarded_old","guardedOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","total_old","totalOld",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong exact old normal raw component {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact old normal raw component {mod}/{key}"
private theorem price (k R g t : Nat) (gp:g ≤ 128*(R+1)^2) (tp:t ≤ 4096*(R+1)^2) :
    g+t ≤ CertificateGuardClosure.deadline k R:=by
  have pow : (R+1)^2 ≤ (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have total : g+t ≤ 4224*(R+1)^2:=by omega
  change g+t ≤ 137438953472*(k+1)*(R+1)^6
  exact total.trans (Nat.mul_le_mul (by omega) pow)
/-- Exhaustive front-end rejection keeps its real source tape and is moved to
both literal parsers/guard at the actual times. This is a rejected-input path,
not an accepted-resource argument. -/
private theorem early (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (canonical:m=a+1)
    (t : Nat) (tp:t ≤ 4096*(pairLength a m+1)^2)
    (hit:((BodyIngress.machine k).run t (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(BodyIngress.machine k).reject)
    (heads:∀ u,u ≤ t → ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2)
    (low:∀ u,u ≤ t → ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val < 352) :
    let R:=pairLength a m;let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k R
    let c:=initialConfig O C (encodePair x w)
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false ∧
    ∃ s,s ≤ CertificateGuardClosure.deadline k R ∧ (O.run s c).state=O.reject ∧
      (∀ u,u ≤ s → (O.run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ s → (O.run u c).state.val < 625):=by
  intro R O C c
  let B0:=FixedRawLengthFence.allocation R
  let small:=initialConfig (BodyIngress.machine k) B0 (encodePair x w)
  have semantic:=rejectSound k x w t hit (by
    intro u hu
    have lo : ((BodyIngress.machine k).run u small).state.val < 352:=low u hu.le
    constructor
    · intro b eq
      have value:=congrArg Fin.val eq
      change ((BodyIngress.machine k).run u small).state.val=288+Cursor.stateCount k+(if b then 7 else 6) at value
      unfold Cursor.stateCount at value
      cases b <;> omega
    · intro mode eq
      have value:=congrArg Fin.val eq
      have high:=bodyAbove k mode
      rw [bodyValue] at high
      change 87+(288+Cursor.stateCount k+8) ≤ 87+(BodyIngress.body k (SerializedBody.entry mode)).val at high
      unfold Cursor.stateCount at high
      change ((BodyIngress.machine k).run u small).state.val=(BodyIngress.body k (SerializedBody.entry mode)).val at value
      omega)
  have budget : B0 ≤ C:=bodyBudget k R
  have trace:=traceRoom (BodyIngress.machine k) budget (encodePair x w) t (by
    intro u hu
    exact lt_of_le_of_lt (Nat.add_le_add_right (heads u hu.le) 1) (smallRoom R))
  have ext (u:Nat)(hu:u ≤ t) : (BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k) C (encodePair x w))=
      IngressAllocation.extendConfig budget ((BodyIngress.machine k).run u small):=uniqueExtension budget (trace u hu)
  have room : 2*R+3 < tapeLength R C:=by
    have h:=oldRoom k R
    have small:2*R+3 ≤ 12*(R+1)^2+1:=by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact small.trans_lt h
  have parserRoom : FixedPairParser.clock R ≤ C:=by
    have old : FixedPairParser.clock R ≤ B0:=by
      change 2*R+1 ≤ 16*(R+1)^2
      nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact old.trans budget
  obtain ⟨g,gp,earlyLow,earlyHeads,suffix⟩:=pairPrefix k C x w canonical room parserRoom
  have state (u:Nat)(hu:u ≤ t) : (O.run (g+u) c).state.val=87+((BodyIngress.machine k).run u small).state.val:=by
    exact (congrArg (fun q=>q.state.val) (suffix u)).trans
      ((congrArg (fun q=>(CertificateGuardClosure.config k (TotalIngressClosure.config k q)).state.val) (ext u hu)).trans
        (stateValue k budget ((BodyIngress.machine k).run u small)))
  refine ⟨semantic,g+t,price k R g t gp tp,?_,?_,?_⟩
  · apply Fin.ext
    have value:=state t le_rfl
    have old : ((BodyIngress.machine k).run t small).state.val=328:=congrArg Fin.val hit
    change (O.run (g+t) c).state.val=415
    omega
  · intro u hu
    by_cases early:u ≤ g
    · exact earlyHeads u early
    · rw [show u=g+(u-g) by omega,suffix,ext (u-g) (by omega),guardedHead,totalHead,extendHead]
      exact heads _ (by omega)
  · intro u hu
    by_cases early:u < g
    · have lo : (O.run u c).state.val < 87:=earlyLow u early
      omega
    · have elapsed : u-g ≤ t:=by omega
      have value:=state (u-g) elapsed
      rw [show g+(u-g)=u by omega] at value
      have lo : ((BodyIngress.machine k).run (u-g) small).state.val < 352:=low _ elapsed
      omega
#print axioms price
#print axioms early
end VirtualFinalClosure.OldEarlyReject
