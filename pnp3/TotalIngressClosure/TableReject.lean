import TotalIngressClosure.RawTable
import TotalIngressClosure.LiftLow
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("AllArityCursor.Runtime","AllArityCursor","er","er"),
      ("AllArityCursor.Runtime","AllArityCursor","exits","exits"),
      ("AllArityCursor.Runtime","AllArityCursor","old_inert","oldInert"),
      ("AllArityCursor.Runtime","AllArityCursor","fixed_run","fixedRun"),
      ("AllArityCursor.Runtime","AllArityCursor","raw_row","rawRow"),
      ("AllArityCursor.Runtime","AllArityCursor","er_initial","erInitial"),
      ("AllArityCursor.Runtime","AllArityCursor","map_er","mapEr"),
      ("TotalIngressClosure.RawTable","TotalIngressClosure","table_prefix","tablePrefix"),
      ("TotalIngressClosure.LiftLow","TotalIngressClosure","lift_low_prefix","liftLow"),
      ("TotalIngressClosure.LiftLow","TotalIngressClosure","earlyEmbed","lowEmbed")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique genuine table-cut transport {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem small_reject_lift (k : Nat) {N B : Nat} (y:Bitstring N) (T : Nat)
    (hit:(SmallIngress.machine.run T (initialConfig SmallIngress.machine B y)).state=SmallIngress.machine.reject) :
    ∀ u,u ≤ T → (AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k) B y)=
      AllArityCursor.mapOld k (SmallIngress.machine.run u (initialConfig SmallIngress.machine B y)):=by
  let c:=initialConfig SmallIngress.machine B y
  have absent(u : Nat)(hu:u ≤ T):¬exits (SmallIngress.machine.run u c).state:=by
    intro bad
    have same:SmallIngress.machine.run T c=SmallIngress.machine.run u c:=by
      rw [show T=u+(T-u) by omega,UniformTM.run_add]
      exact fixedRun SmallIngress.machine _ (oldInert _ bad) (T-u)
    have no:¬exits SmallIngress.machine.reject:=by change ¬((328:Nat)=345 ∨ 328=346);decide
    rw [same] at hit
    exact no (hit ▸ bad)
  intro u hu
  have sim:=Cursor.Transport.avoid_changed_rows SmallIngress.machine (AllArityCursor.machine k) (er k) exits
    (fun c h=>oldInert c h) (rawRow k) c u (absent u hu)
  rw [erInitial,mapEr] at sim
  exact sim
private theorem low_value {k N B : Nat} (d:Config (IngressRepair.machine k).stateCount N B) :
    (lowEmbed d).state.val=d.state.val:=by
  dsimp only [lowEmbed,BodyIngress.config,BodyIngress.old,CarryWindow.config,CarryWindow.embed,
    VirtualLeaf.config,VirtualLeaf.embed]
set_option maxRecDepth 4000 in
private theorem low_reject {k N B : Nat} (d:Config (IngressRepair.machine k).stateCount N B)
    (hit:d.state=(IngressRepair.machine k).reject) : (lowEmbed d).state=(BodyIngress.machine k).reject:=by
  change BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k d.state))=(BodyIngress.machine k).reject
  rw [hit]
  rfl
set_option maxRecDepth 4000 in
private theorem table_reject (k : Nat) {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (short:¬2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ∃ t,t ≤ 4096*(R+1)^2 ∧ ((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).state.val < 352):=by
  intro R B c
  obtain ⟨T,_hH,price,heads,outcome⟩:=tablePrefix x w header tag gamma physical cap
  rw [if_neg short] at outcome
  have tx:=small_reject_lift k (encodePair x w) T outcome
  let repaired:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  have repair(u : Nat):(IngressRepair.machine k).run u repaired=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=
    IngressRepair.supported_transport k x w z tag gamma physical u
  have low(u : Nat)(hu:u ≤ T):((IngressRepair.machine k).run u repaired).state.val < 352:=by
    rw [repair,tx u hu]
    exact (SmallIngress.machine.run u (initialConfig SmallIngress.machine B (encodePair x w))).state.isLt
  have body:=liftLow k repaired (t:=T) (by intro u hu;exact (low u hu).le.trans (by decide))
  have atRun(u : Nat)(hu:u ≤ T):(BodyIngress.machine k).run u c=
      lowEmbed ((IngressRepair.machine k).run u repaired):=body u hu
  have rejected:((IngressRepair.machine k).run T repaired).state=(IngressRepair.machine k).reject:=by
    rw [repair,tx T le_rfl]
    apply Fin.ext
    change (SmallIngress.machine.run T (initialConfig SmallIngress.machine B (encodePair x w))).state.val=328
    rw [outcome]
    rfl
  refine ⟨T,price,?_,?_,?_⟩
  · exact (congrArg Config.state (atRun T le_rfl)).trans (low_reject _ rejected)
  · intro u hu
    rw [atRun u hu,repair,tx u hu]
    exact heads u hu
  · intro u hu
    rw [atRun u hu,low_value]
    exact low u hu
end TotalIngressClosure
