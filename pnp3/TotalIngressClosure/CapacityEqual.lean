import TotalIngressClosure.WideInclusive
import TotalIngressClosure.StreamRejectLift
import RepairedFrontier.Body
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.WideInclusive","TotalIngressClosure","wide_inclusive_first","wideFirst"),
      ("RepairedFrontier.Body","RepairedFrontier","install_reject","installReject"),
      ("TotalIngressClosure.StreamRejectLift","TotalIngressClosure","stream_reject_lift","streamLift")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique exact capacity boundary {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem capacity_equal (k : Nat) {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (wide:2 ≤ z)
    (equal:n=FixedRawLengthFence.capacity a m z) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ∃ t,t ≤ 144*(R+1)^2 ∧ ((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).state.val < 352):=by
  intro R B c
  let L:=a+m+z+2
  let F:=FixedRawLengthFence.fencePos R
  let tape:=FixedRawLengthFence.countdownTape B x w z 0 n
  let T:=Body.extend tape
  obtain ⟨tp,hL,price,arrived,first,heads⟩:=wideFirst x w header tag gamma wide (Nat.le_of_eq equal)
  have resource:=(FixedRawLengthFence.resource_bounds R).1
  have cells:=FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_eq equal)
  have geometry:L+n+1=F:=by
    have support:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    dsimp only [L,F,R,FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at *
    omega
  have hF:F < tapeLength R B:=by
    dsimp only [F,FixedRawLengthFence.fencePos,tapeLength]
    omega
  have fit:L+n+1 < tapeLength R B:=by rw [geometry];exact hF
  have read(i : Nat)(hi:i < tapeLength R B):T i=tape ⟨i,hi⟩:=Body.extend_read tape ⟨i,hi⟩
  have sep:T L=none:=by rw [read L hL];exact cells.2.2.1 _ (by dsimp only [L];omega)
  have marks(i : Nat)(lo:L < i)(hi:i < L+n+1):T i=some true:=by
    rw [read i (by omega)]
    apply cells.2.2.2.1 ⟨i,lt_trans hi fit⟩
    · change a+m+3+z ≤ i
      dsimp only [L] at lo;omega
    · change i < a+m+3+z+n
      dsimp only [L] at hi;omega
  have fence:T (L+n+1)=some false:=by
    rw [geometry,read F hF]
    dsimp only [tape,FixedRawLengthFence.countdownTape]
    rw [if_pos rfl]
  have rejected:=installReject T fit sep marks fence
  let old:=initialConfig SmallIngress.machine B (encodePair x w)
  have entry:(⟨Stream.machine.start,⟨L,hL⟩,tape⟩ : Config 64 R B)=
      ⟨Stream.machine.start,⟨L,hL⟩,fun i=>T i.val⟩:=by
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i;exact (Body.extend_read tape i).symm
  have replay(s : Nat):SmallIngress.machine.run (tp+s) old=SmallIngress.producer.seqEmbedRight Stream.machine
      (Stream.machine.run s ⟨Stream.machine.start,⟨L,hL⟩,fun i=>T i.val⟩):=by
    have hand:=SmallIngress.producer.seq_handoff Stream.machine
      (initialConfig SmallIngress.producer B (encodePair x w)) first (by rw [arrived]) s
    rw [arrived,entry] at hand
    exact hand
  have hit:(SmallIngress.machine.run (tp+(n+2)) old).state=SmallIngress.machine.reject:=by
    rw [replay]
    change SmallIngress.producer.seqRight Stream.machine _=SmallIngress.machine.reject
    rw [rejected]
    rfl
  have before(u : Nat)(hu:u ≤ tp):(SmallIngress.machine.run u old).head.val ≤ 12*(R+1)^2:=by
    have same:=SmallIngress.producer.seq_run_left Stream.machine
      (initialConfig SmallIngress.producer B (encodePair x w)) first u hu
    rw [←UniformTM.seq_initialConfig] at same
    change SmallIngress.machine.run u old=_ at same
    rw [same]
    exact heads u hu
  have allHeads(u : Nat)(hu:u ≤ tp+(n+2)):(SmallIngress.machine.run u old).head.val ≤ 12*(R+1)^2:=by
    by_cases early:u ≤ tp
    · exact before u early
    · rw [show u=tp+(u-tp) by omega,replay]
      have speed:=Stream.machine.run_head_le (steps:=u-tp)
        (⟨Stream.machine.start,⟨L,hL⟩,fun i=>T i.val⟩ : Config 64 R B)
      have bounded:L+(u-tp) ≤ 12*(R+1)^2:=by
        have lim:u-tp ≤ n+2:=by omega
        dsimp only [F,FixedRawLengthFence.fencePos] at geometry
        nlinarith only [geometry,lim,Nat.zero_le R,Nat.zero_le (R*R)]
      exact speed.trans bounded
  have total:tp+(n+2) ≤ 144*(R+1)^2:=by
    have pre:tp ≤ 128*(R+1)^2:=price
    dsimp only [F,FixedRawLengthFence.fencePos] at geometry
    nlinarith only [pre,geometry,Nat.zero_le R,Nat.zero_le (R*R),Nat.zero_le L]
  obtain ⟨done,foot,controls⟩:=streamLift k x w tag gamma physical (tp+(n+2)) (12*(R+1)^2) hit allHeads
  exact ⟨tp+(n+2),total,done,foot,controls⟩
end TotalIngressClosure
