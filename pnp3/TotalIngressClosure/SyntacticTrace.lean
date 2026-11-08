import TotalIngressClosure.RepairHeads
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("RawFrontier.Syntactic","RawFrontier","tagMap","tagMap"),
      ("RawFrontier.Syntactic","RawFrontier","gammaMap","gammaMap"),
      ("RawFrontier.Syntactic","RawFrontier","tag_rows","tag_rows"),
      ("RawFrontier.Syntactic","RawFrontier","gamma_rows","gamma_rows"),
      ("RawFrontier.Syntactic","RawFrontier","tape_update","tape_update"),
      ("RawFrontier.Syntactic","RawFrontier","syntactic_clock","syntactic_clock"),
      ("RawFrontier.Syntactic","RawFrontier","content_start","content_start"),
      ("IngressAllocation.Bootstrap","IngressAllocation","bootstrap_price","bootstrapPrice")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique syntactic literal prefix {mod}/{key}: {found.map Prod.fst}"
private theorem phase_heads {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (A : UniformTM) (map:Fin A.stateCount → Fin SmallIngress.producer.stateCount)
    (rows:∀ s,s≠A.accept → ∀ b,SmallIngress.producer.step (map s) b=(map (A.step s b).1,(A.step s b).2))
    (cf:Config A.stateCount (pairLength a m) B) (P D E : Nat)
    (prefixPrice:P ≤ E)
    (initial:SmallIngress.producer.run P (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨map cf.state,cf.head,cf.tape⟩)
    (reject:(A.run D cf).state=A.reject)
    (heads:∀ u,u ≤ D → (A.run u cf).head.val ≤ E) :
    ∀ u,u ≤ P+D → (SmallIngress.producer.run u
      (initialConfig SmallIngress.producer B (encodePair x w))).head.val ≤ E:=by
  intro u hu
  by_cases early:u ≤ P
  · exact (SmallIngress.producer.run_initialConfig_head_le (budget:=B) (steps:=u) (encodePair x w)).trans (early.trans prefixPrice)
  · let d:=u-P
    have bound:d ≤ D:=by dsimp only [d];omega
    have absent:(A.run d cf).state≠A.accept:=by
      intro bad
      have later:=A.run_accept_of_le cf bad bound
      have wrong:(A.run D cf).state=A.accept:=(congrArg Config.state later).trans bad
      rw [reject] at wrong
      exact A.accept_ne_reject wrong.symm
    have sim:=Cursor.Transport.avoid_changed_rows A SmallIngress.producer map (fun q=>q=A.accept)
      (fun c h=>A.stepConfig_accept c h) rows cf d absent
    rw [show u=P+d by dsimp only [d];omega,UniformTM.run_add,initial,sim]
    exact heads d bound
set_option maxRecDepth 4000 in
private theorem tag_reject {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (bad : FixedContentTagGate.tagMatches (Fin.append x w)=false) :
    ∃ T, T ≤ 128*(pairLength a m+1)^2 ∧
      let d := SmallIngress.producer.run T (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
      d.state=SmallIngress.producer.reject ∧
      d.tape=FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      d.head.val ≤ a+m ∧
      (∀ u,u ≤ T → (SmallIngress.producer.run u (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2) := by
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let f : Fin (tapeLength (pairLength a m) B) := ⟨FixedRawLengthFence.fencePos (pairLength a m),by
    have res := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
    dsimp only [FixedRawLengthFence.fencePos,tapeLength] at *; omega⟩
  let c := FixedContentTagGate.startConfig B x w
  let cf := {c with tape := FixedRawLengthFence.fencedContentTape B x w}
  have patch : cf={c with tape := Function.update c.tape f (some false)} :=
    Config.ext_parts rfl rfl (tape_update x w f rfl)
  have framed := FixedContentTagGate.machine.run_update_of_unvisited c f (some false)
    (FixedContentTagGate.deadline a m) (by
      intro u hu eq
      have lim := (FixedContentTagGate.phase_contract x w).1 B u (Nat.le_of_lt hu)
      have e := congrArg Fin.val eq
      dsimp only [c,f,FixedRawLengthFence.fencePos] at e
      simp only [pairLength] at e
      omega)
  rw [←patch] at framed
  have reject : (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m) cf).state=
      FixedContentTagGate.machine.reject := by
    rw [framed,FixedContentTagGate.run_deadline]
    simp [FixedContentTagGate.finalConfig,bad,FixedContentTagGate.machine]
  have sim := Cursor.Transport.avoid_changed_rows FixedContentTagGate.machine SmallIngress.producer tagMap
    (fun s => s=FixedContentTagGate.machine.accept)
    (fun c h => FixedContentTagGate.machine.stepConfig_accept c h) tag_rows cf
    (FixedContentTagGate.deadline a m) (by rw [reject]; exact FixedContentTagGate.machine.accept_ne_reject.symm)
  have initial : SmallIngress.producer.run
      (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m)
      (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨tagMap cf.state,cf.head,cf.tape⟩ := content_start x w
  let T := FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+
    FixedContentTagGate.deadline a m
  have finish : SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨tagMap (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m) cf).state,
        (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m) cf).head,
        (FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m) cf).tape⟩ := by
    rw [show T=(FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m)+
      FixedContentTagGate.deadline a m from rfl,UniformTM.run_add,initial]
    exact sim
  have allPhase (u : Nat) (hu:u ≤ FixedContentTagGate.deadline a m) :
      (FixedContentTagGate.machine.run u cf).head.val ≤ 12*(pairLength a m+1)^2:=by
    have each:=FixedContentTagGate.machine.run_update_of_unvisited c f (some false) u (by
      intro v hv eq
      have lim:=(FixedContentTagGate.phase_contract x w).1 B v (by omega)
      have e:=congrArg Fin.val eq
      dsimp only [c,f,FixedRawLengthFence.fencePos] at e
      simp only [pairLength] at e
      omega)
    rw [←patch] at each
    rw [each]
    have low:=(FixedContentTagGate.phase_contract x w).1 B u hu
    have pair:a+m ≤ pairLength a m:=by simp only [pairLength];omega
    nlinarith only [low,pair,Nat.zero_le ((pairLength a m)^2)]
  have before:FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m ≤ 12*(pairLength a m+1)^2:=by
    have h:=bootstrapPrice a m
    omega
  have fullHeads:=phase_heads x w FixedContentTagGate.machine tagMap
    tag_rows cf (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m) (FixedContentTagGate.deadline a m)
    (12*(pairLength a m+1)^2) before initial reject allPhase
  refine ⟨T,?_,?_,?_,?_,fullHeads⟩
  · exact (syntactic_clock (pairLength a m) (a+m) _ (by simp only [pairLength]; omega)
      (FixedRawLengthFence.content_prefix_resources a m).2).1
  · rw [finish,reject]
    simp only [tagMap,↓reduceIte]
  · rw [finish,framed,FixedContentTagGate.run_deadline]
    exact (tape_update x w f rfl).symm
  · rw [finish,framed]
    exact (FixedContentTagGate.phase_contract x w).1 B _ le_rfl
set_option maxRecDepth 4000 in
private theorem gamma_reject {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (bad : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none) :
    ∃ T, T ≤ 128*(pairLength a m+1)^2 ∧
      let d := SmallIngress.producer.run T (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
      d.state=SmallIngress.producer.reject ∧
      d.tape=FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      d.head.val ≤ a+m ∧
      (∀ u,u ≤ T → (SmallIngress.producer.run u (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2) := by
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let f : Fin (tapeLength (pairLength a m) B) := ⟨FixedRawLengthFence.fencePos (pairLength a m),by
    have res := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
    dsimp only [FixedRawLengthFence.fencePos,tapeLength] at *; omega⟩
  let c := FixedContentGammaTerminator.startConfig B x w
  let cf := {c with tape := FixedRawLengthFence.fencedContentTape B x w}
  have patch : cf={c with tape := Function.update c.tape f (some false)} :=
    Config.ext_parts rfl rfl (tape_update x w f rfl)
  have framed := FixedContentGammaTerminator.machine.run_update_of_unvisited c f (some false)
    (FixedContentGammaTerminator.deadline a m) (by
      intro u hu eq
      have lim := (FixedContentGammaTerminator.phase_contract x w tag).1 B u (Nat.le_of_lt hu)
      have e := congrArg Fin.val eq
      dsimp only [c,f,FixedRawLengthFence.fencePos] at e
      simp only [pairLength] at e
      omega)
  rw [←patch] at framed
  have reject : (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m) cf).state=
      FixedContentGammaTerminator.machine.reject := by
    rw [framed,FixedContentGammaTerminator.run_deadline x w tag]
    simp [FixedContentGammaTerminator.finalConfig,bad,FixedContentGammaTerminator.machine]
  have sim := Cursor.Transport.avoid_changed_rows FixedContentGammaTerminator.machine SmallIngress.producer gammaMap
    (fun s => s=FixedContentGammaTerminator.machine.accept)
    (fun c h => FixedContentGammaTerminator.machine.stepConfig_accept c h) gamma_rows cf
    (FixedContentGammaTerminator.deadline a m) (by rw [reject]; exact FixedContentGammaTerminator.machine.accept_ne_reject.symm)
  have initial : SmallIngress.producer.run
      (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨gammaMap cf.state,cf.head,cf.tape⟩ := by
    rw [SmallIngress.raw_gamma_start x w tag]
    refine Config.ext_parts ?_ ?_ ?_
    · obtain ⟨_,_,_,_,_,state,_,_⟩ := FixedContentGammaTerminator.handoff_exact (B := B) x w tag
      change SmallIngress.q 124=gammaMap (FixedContentGammaTerminator.startConfig B x w).state
      rw [state]
      rfl
    · apply Fin.ext
      obtain ⟨_,_,head,_,_,_,he,_⟩ := FixedContentGammaTerminator.handoff_exact (B := B) x w tag
      exact (congrArg Fin.val he |>.trans head).symm
    · rfl
  let T := FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+
    (3*(a+m)+7)+FixedContentGammaTerminator.deadline a m
  have finish : SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨gammaMap (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m) cf).state,
        (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m) cf).head,
        (FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m) cf).tape⟩ := by
    rw [show T=(FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)+
      FixedContentGammaTerminator.deadline a m by dsimp only [T]; omega,UniformTM.run_add,initial]
    exact sim
  have allPhase (u : Nat) (hu:u ≤ FixedContentGammaTerminator.deadline a m) :
      (FixedContentGammaTerminator.machine.run u cf).head.val ≤ 12*(pairLength a m+1)^2:=by
    have each:=FixedContentGammaTerminator.machine.run_update_of_unvisited c f (some false) u (by
      intro v hv eq
      have lim:=(FixedContentGammaTerminator.phase_contract x w tag).1 B v (by omega)
      have e:=congrArg Fin.val eq
      dsimp only [c,f,FixedRawLengthFence.fencePos] at e
      simp only [pairLength] at e
      omega)
    rw [←patch] at each
    rw [each]
    have low:=(FixedContentGammaTerminator.phase_contract x w tag).1 B u hu
    have pair:a+m ≤ pairLength a m:=by simp only [pairLength];omega
    nlinarith only [low,pair,Nat.zero_le ((pairLength a m)^2)]
  have before:FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+(3*(a+m)+7) ≤ 12*(pairLength a m+1)^2:=by
    have h:=bootstrapPrice a m
    omega
  have fullHeads:=phase_heads x w FixedContentGammaTerminator.machine gammaMap
    gamma_rows cf (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+(3*(a+m)+7)) (FixedContentGammaTerminator.deadline a m)
    (12*(pairLength a m+1)^2) before initial reject allPhase
  refine ⟨T,?_,?_,?_,?_,fullHeads⟩
  · exact (syntactic_clock (pairLength a m) (a+m) _ (by simp only [pairLength]; omega)
      (FixedRawLengthFence.content_prefix_resources a m).2).2
  · rw [finish,reject]
    simp only [gammaMap,↓reduceIte]
  · rw [finish,framed,FixedContentGammaTerminator.run_deadline x w tag]
    exact (tape_update x w f rfl).symm
  · rw [finish,framed]
    exact (FixedContentGammaTerminator.phase_contract x w tag).1 B _ le_rfl

end TotalIngressClosure
