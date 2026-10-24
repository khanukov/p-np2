import RawFrontier.Base
namespace RawFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private def tagMap (s : Fin FixedContentTagGate.stateCount) : Fin SmallIngress.producer.stateCount :=
  if s=FixedContentTagGate.machine.reject then SmallIngress.producer.reject
  else if s=FixedContentTagGate.machine.accept then SmallIngress.q 124 else SmallIngress.q (109+s.val)
private def gammaMap (s : Fin FixedContentGammaTerminator.stateCount) : Fin SmallIngress.producer.stateCount :=
  if s=FixedContentGammaTerminator.machine.reject then SmallIngress.producer.reject
  else if s=FixedContentGammaTerminator.machine.accept then SmallIngress.q 127 else SmallIngress.q (124+s.val)
private theorem tag_rows : ∀ s : Fin FixedContentTagGate.stateCount,
    s≠FixedContentTagGate.machine.accept → ∀ b,
    SmallIngress.producer.step (tagMap s) b=
      (tagMap (FixedContentTagGate.machine.step s b).1,(FixedContentTagGate.machine.step s b).2) := by
  decide
private theorem gamma_rows : ∀ s : Fin FixedContentGammaTerminator.stateCount,
    s≠FixedContentGammaTerminator.machine.accept → ∀ b,
    SmallIngress.producer.step (gammaMap s) b=
      (gammaMap (FixedContentGammaTerminator.machine.step s b).1,(FixedContentGammaTerminator.machine.step s b).2) := by
  decide
private theorem tape_update {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (f : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))))
    (hf : f.val=FixedRawLengthFence.fencePos (pairLength a m)) :
    FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w=
      Function.update (FixedPairContentMarkerErase.contentTape (FixedRawLengthFence.allocation (pairLength a m)) x w) f (some false) := by
  funext i
  by_cases hi : i.val < a+m
  · have hn : i.val≠FixedRawLengthFence.fencePos (pairLength a m) := by
      simp only [FixedRawLengthFence.fencePos,pairLength]; omega
    simp [FixedRawLengthFence.fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Fin.ext_iff,hf,hn]
  · simp [FixedRawLengthFence.fencedContentTape,FixedPairContentMarkerErase.contentTape,hi,Function.update_apply,Fin.ext_iff,hf]
private theorem syntactic_clock (R S P : Nat) (hS : S ≤ R) (hp : P ≤ 16*(R+1)^2) :
    P+(3*S+7) ≤ 128*(R+1)^2 ∧ P+(3*S+7)+(S-7) ≤ 128*(R+1)^2 := by
  have sub : S-7 ≤ S := Nat.sub_le _ _
  constructor <;> nlinarith only [hS,hp,sub,Nat.zero_le (R*R)]
private theorem content_start {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    SmallIngress.producer.run (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m)
      (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      ⟨SmallIngress.q 109,⟨a+m,by simp only [tapeLength,pairLength]; omega⟩,
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w⟩ := by
  have old := FixedRawLengthFence.raw_fenced_content_exact x w
    (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  have safe : (FixedRawLengthFence.prefixed.run
      (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m)
      (initialConfig FixedRawLengthFence.prefixed (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
      FixedRawLengthFence.prefixed.reject := by
    rw [old]
    change (⟨109,by decide⟩ : Fin 256)≠FixedRawLengthFence.prefixed.reject
    decide
  have sim := SmallIngress.preserves_nonreject _ _ safe
  change SmallIngress.producer.run _ (initialConfig SmallIngress.producer _ _)=_ at sim
  rw [old] at sim
  exact sim
private theorem tag_reject {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (bad : FixedContentTagGate.tagMatches (Fin.append x w)=false) :
    ∃ T, T ≤ 128*(pairLength a m+1)^2 ∧
      let d := SmallIngress.producer.run T (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
      d.state=SmallIngress.producer.reject ∧
      d.tape=FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      d.head.val ≤ a+m := by
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
  refine ⟨T,?_,?_,?_,?_⟩
  · exact (syntactic_clock (pairLength a m) (a+m) _ (by simp only [pairLength]; omega)
      (FixedRawLengthFence.content_prefix_resources a m).2).1
  · rw [finish,reject]
    simp only [tagMap,↓reduceIte]
  · rw [finish,framed,FixedContentTagGate.run_deadline]
    exact (tape_update x w f rfl).symm
  · rw [finish,framed]
    exact (FixedContentTagGate.phase_contract x w).1 B _ le_rfl
private theorem gamma_reject {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (bad : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none) :
    ∃ T, T ≤ 128*(pairLength a m+1)^2 ∧
      let d := SmallIngress.producer.run T (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
      d.state=SmallIngress.producer.reject ∧
      d.tape=FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      d.head.val ≤ a+m := by
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
  refine ⟨T,?_,?_,?_,?_⟩
  · exact (syntactic_clock (pairLength a m) (a+m) _ (by simp only [pairLength]; omega)
      (FixedRawLengthFence.content_prefix_resources a m).2).2
  · rw [finish,reject]
    simp only [gammaMap,↓reduceIte]
  · rw [finish,framed,FixedContentGammaTerminator.run_deadline x w tag]
    exact (tape_update x w f rfl).symm
  · rw [finish,framed]
    exact (FixedContentGammaTerminator.phase_contract x w tag).1 B _ le_rfl
/-- Every wrong/short tag or absent physical gamma terminator has an actual
FIRST raw rejection on the producer288/Cursor machine; no parsed input is assumed. -/
theorem syntactic_reject (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (bad : FixedContentTagGate.tagMatches (Fin.append x w)=false ∨
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none) :
    let c := initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false ∧
      ((AllArityCursor.machine k).run t c).tape=
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      ((AllArityCursor.machine k).run t c).head.val ≤ a+m := by
  dsimp only
  have producer : ∃ T, T ≤ 128*(pairLength a m+1)^2 ∧
      let d := SmallIngress.producer.run T (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
      d.state=SmallIngress.producer.reject ∧
      d.tape=FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      d.head.val ≤ a+m := by
    cases tag : FixedContentTagGate.tagMatches (Fin.append x w) with
    | false => exact tag_reject x w tag
    | true =>
      have none : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none := by
        rcases bad with h | h
        · rw [tag] at h; contradiction
        · exact h
      exact gamma_reject x w tag none
  obtain ⟨T,price,reject,tape,head⟩ := producer
  obtain ⟨t,ht,hit,first,safe,sound⟩ := producer_reject_frontier k x w T price reject
  have raw := SmallIngress.producer.seq_reject_handoff (Cursor.machine k) _ reject 0
  change (AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) _ _)=_ at raw
  have bound : t ≤ T := by
    by_contra no
    exact (first T (by omega)).1 (congrArg Config.state raw)
  have same := (AllArityCursor.machine k).run_reject_of_le _ hit bound
  refine ⟨t,ht,hit,first,safe,sound,?_,?_⟩
  · rw [←same,raw]; exact tape
  · rw [←same,raw]; exact head
end RawFrontier
