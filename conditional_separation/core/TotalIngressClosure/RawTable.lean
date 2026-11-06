import TotalIngressClosure.StreamFrame
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.ProducerSuccess","TotalIngressClosure","producer_supported","producerFirst"),
      ("TotalIngressClosure.StreamFrame","TotalIngressClosure","source_frame","actualFrame"),
      ("TotalIngressClosure.StreamOrbitAll","TotalIngressClosure","orbit_all","orbitAll"),
      ("IngressAllocation.AllProducer","IngressAllocation","producer_seq_prefix","seqPrefix"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.room","fr_room"),
      ("SmallOrbit.Runtime","SmallOrbit","clear_extend","clearExtend")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique raw table interface {mod}/{key}: {found.map Prod.fst}"
private theorem clipped_cursor (A S Q : Nat):min (min A S+Q) S=min (A+Q) S:=by omega
private theorem table_prefix {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let S:=a+m;let F:=FixedRawLengthFence.fencePos R
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
    let c:=initialConfig SmallIngress.machine B (encodePair x w)
    ∃ (t : Nat) (_hH:S+z+n+3 < tapeLength R B),t ≤ 4096*(R+1)^2 ∧
      (∀ u,u ≤ t → (SmallIngress.machine.run u c).head.val ≤ 12*(R+1)^2) ∧
      (if 2^n ≤ F-(S+z+n+3)-1 then
         ∃ hp:min (9+2*z+2^n) S < tapeLength R B,
           SmallIngress.machine.run t c=SmallIngress.producer.seqEmbedRight Stream.machine
             ⟨Stream.q (if min (9+2*z+2^n) S=S then 57 else 58),⟨min (9+2*z+2^n) S,hp⟩,
               fun i=>Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false i.val⟩
       else (SmallIngress.machine.run t c).state=SmallIngress.machine.reject) := by
  intro R B S F U c
  obtain ⟨tp,hL,prePrice,producerRun,first,producerHeads⟩:=producerFirst x w header tag gamma physical cap
  let T0:=Body.extend (SmallIngress.prepared B x w z n)
  have frame:=actualFrame x w header gamma physical cap
  obtain ⟨_room,_scratch,hF,_fence⟩:=Stream.raw_budget_cells x w gamma cap
  have hH:S+z+n+3 < tapeLength R B:=(fr_room frame).trans hF
  obtain ⟨tb,bodyPrice,bodyHeads,finished⟩:=orbitAll T0 frame hF hL hH
  have Ueq:Body.clear T0 (S+z+3) n=U:=
    clearExtend (SmallIngress.prepared B x w z n) (S+z+2) n (by
      change S+z+2+n+1 < tapeLength R B
      omega)
  rw [Ueq] at finished
  have entry:(⟨Stream.machine.start,⟨S+z+2,hL⟩,SmallIngress.prepared B x w z n⟩ : Config 64 R B)=
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T0 i.val⟩:=by
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i;exact (Body.extend_read _ i).symm
  have replay (s : Nat):SmallIngress.machine.run (tp+s) c=SmallIngress.producer.seqEmbedRight Stream.machine
      (Stream.machine.run s ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T0 i.val⟩):=by
    have hand:=SmallIngress.producer.seq_handoff Stream.machine
      (initialConfig SmallIngress.producer B (encodePair x w)) first (by rw [producerRun]) s
    rw [producerRun,entry] at hand
    exact hand
  have price:tp+tb ≤ 4096*(R+1)^2:=by
    have pair:S ≤ R:=by dsimp only [S,R,pairLength];omega
    have gb:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    have nz:n ≤ 3*R:=by change n < (3*R+2)-(a+m+3+z) at cap;omega
    have zz:z ≤ R:=by dsimp only [S] at pair;omega
    have dist:S-min (9+2*z) S ≤ R:=(Nat.sub_le _ _).trans pair
    have square:R+1 ≤ (R+1)^2:=by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1 ≤ R+1 by omega)
    change tp ≤ 144*(R+1)^2 at prePrice
    change tb ≤ n+2+InputRead.readClock n z (S-min (9+2*z) S)+64*(F+1)^2 at bodyPrice
    dsimp only [InputRead.readClock,F,FixedRawLengthFence.fencePos] at bodyPrice
    nlinarith only [prePrice,bodyPrice,nz,zz,dist,square]
  obtain ⟨_start,oldHeads,_before⟩:=seqPrefix Stream.machine x w tp (S+z+2) _ hL producerRun first producerHeads
  refine ⟨tp+tb,hH,price,?_,?_⟩
  · intro u hu
    by_cases early:u ≤ tp
    · exact oldHeads u early
    · rw [show u=tp+(u-tp) by omega,replay]
      have bound:=bodyHeads (u-tp) (by omega)
      have envelope:F ≤ 12*(R+1)^2:=by
        dsimp only [F,FixedRawLengthFence.fencePos]
        nlinarith only [Nat.zero_le R,Nat.zero_le (R*R)]
      exact bound.trans envelope
  · by_cases rows:2^n ≤ F-(S+z+n+3)-1
    · rw [if_pos rows] at finished ⊢
      obtain ⟨hp,done⟩:=finished
      have cursor:Stream.Target.cursor (min (9+2*z) S) S (2^n)=min (9+2*z+2^n) S:=by
        exact clipped_cursor (9+2*z) S (2^n)
      have sameImage:Stream.Target.image U S z n (min (9+2*z) S) (2^n) (2^n) false=
          Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false:=by
        funext i;dsimp only [Stream.Target.image];simp only [Bool.false_eq_true,false_and,if_false]
      have hp':min (9+2*z+2^n) S < tapeLength R B:=by rw [←cursor];exact hp
      refine ⟨hp',?_⟩
      rw [replay,done]
      apply congrArg (SmallIngress.producer.seqEmbedRight Stream.machine)
      apply Config.ext_parts
      · change Stream.q (if Stream.Target.cursor (min (9+2*z) S) S (2^n)=S then 57 else 58)=_
        rw [cursor]
      · exact Fin.ext cursor
      · funext i
        exact congrFun sameImage i.val
    · rw [if_neg rows] at finished ⊢
      rw [replay,finished]
      rfl
end TotalIngressClosure
