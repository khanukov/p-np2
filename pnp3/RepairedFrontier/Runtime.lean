import RepairedFrontier.Producer
namespace RepairedFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem values (k : Nat) :
    (IngressRepair.machine k).accept.val=327 ∧ (IngressRepair.machine k).reject.val=328 ∧
    (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57)).val=345 ∧
    (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)).val=346 ∧
    (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start).val=288 := by
  have v := AllArityCursor.control_values k
  exact ⟨v.2.2.1,v.2.2.2,v.1,v.2.1,rfl⟩
private theorem refinement (k : Nat) {N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) (t : Nat) :
    ((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∨
    (IngressRepair.machine k).run t c=(AllArityCursor.machine k).run t c := by
  run_tac do
    let env ← getEnv
    let ns := env.constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.IngressRepair.Transport." && n.toString.endsWith ".IngressRepair.refinement"
    unless ns.length==1 do throwError "Ambiguous refinement: {ns}"
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(exact OLD k c t)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent && stx.getId.toString=="OLD" then mkIdent ns.head! else stx)
/-- Literal early-rejection soundness for the repaired family, before work.
The accepted compatibility theorem is used at every relevant actual time. -/
theorem early_reject_sound (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (t : Nat)
    (reject : ((IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(IngressRepair.machine k).reject)
    (noWork : ∀ u, u<t →
      ((IngressRepair.machine k).run u (initialConfig (IngressRepair.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((IngressRepair.machine k).run u (initialConfig (IngressRepair.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  cases rel : PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false => rfl
  | true =>
    have same := IngressRepair.accepted_transport k x w rel
    have oldReject : ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(AllArityCursor.machine k).reject := by
      rw [←same t]; exact reject
    have oldNoWork : ∀ u, u<t →
        ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58) := by
      intro u hu; rw [←same u]; exact noWork u hu
    have bad := RawFrontier.early_reject_sound k x w t oldReject oldNoWork
    rw [rel] at bad
    contradiction
private theorem first_event (P : Nat → Prop) (T : Nat) (hit : P T) :
    ∃ t, t≤T ∧ P t ∧ ∀ u, u<t → ¬P u := by
  classical
  suffices aux : ∀ T, (∃ u, u≤T ∧ P u) → ∃ t, t≤T ∧ P t ∧ ∀ u, u<t → ¬P u by
    exact aux T ⟨T,le_rfl,hit⟩
  intro T
  induction T with
  | zero =>
    intro ⟨u,hu,h⟩
    have eq : u=0 := by omega
    subst u
    exact ⟨0,le_rfl,h,by intro u hu; omega⟩
  | succ T ih =>
    intro found
    by_cases earlier : ∃ u, u≤T ∧ P u
    · obtain ⟨t,ht,h,first⟩ := ih earlier
      exact ⟨t,by omega,h,first⟩
    · obtain ⟨u,hu,h⟩ := found
      have eq : u=T+1 := by by_contra ne; exact earlier ⟨u,by omega,h⟩
      subst u
      exact ⟨T+1,le_rfl,h,by intro u hu h; exact earlier ⟨u,by omega,h⟩⟩
private abbrev EntryResult (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Prop :=
  let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  ∃ t, t≤128*(pairLength a m+1)^2 ∧
    (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∨
     ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start) ∧
    (∀ u, u<t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject ∧
      ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start) ∧
    (∀ u, u≤t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
      ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
    (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject →
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false)
private theorem finish (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (T : Nat)
    (price : T≤128*(pairLength a m+1)^2)
    (hit : let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      ; ((IngressRepair.machine k).run T c).state=(IngressRepair.machine k).reject ∨
        ((IngressRepair.machine k).run T c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start)
    (safe : ∀ u, u≤T → let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      ; ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) : EntryResult k x w := by
  dsimp only at hit safe ⊢
  obtain ⟨t,ht,done,first⟩ := first_event (fun u =>
    ((IngressRepair.machine k).run u (initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(IngressRepair.machine k).reject ∨
    ((IngressRepair.machine k).run u (initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start) T hit
  refine ⟨t,ht.trans price,done,?_,fun u hu => safe u (hu.trans ht),?_⟩
  · intro u hu; exact ⟨fun h => first u hu (Or.inl h),fun h => first u hu (Or.inr h)⟩
  · intro rejected
    exact early_reject_sound k x w t rejected (fun u hu => (safe u (by omega)).2)
private theorem from_old_negative (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (T : Nat)
    (price : T≤128*(pairLength a m+1)^2)
    (hit : ((AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(AllArityCursor.machine k).reject)
    (noWork : ∀ u, u<T →
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) : EntryResult k x w := by
  let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have v := values k
  have rejected := IngressRepair.reject_preserved k c T hit
  apply finish k x w T price (Or.inl rejected)
  intro u hu
  dsimp only
  change ((AllArityCursor.machine k).run T c).state=(AllArityCursor.machine k).reject at hit
  rcases refinement k c u with yes | same
  · rw [yes]
    constructor
    · exact (IngressRepair.machine k).accept_ne_reject.symm
    · constructor <;> intro h <;> have eq := congrArg Fin.val h
      all_goals simp only [v.2.1,v.2.2.1,v.2.2.2.1] at eq; omega
  · rw [same]
    have safeAccept : ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept := by
      intro h
      have eq := (AllArityCursor.machine k).run_accept_of_le c h hu
      rw [eq,h] at hit
      exact (AllArityCursor.machine k).accept_ne_reject hit
    refine ⟨safeAccept,?_⟩
    by_cases lt : u<T
    · exact noWork u lt
    · have eq : u=T := by omega
      subst u
      rw [hit]
      constructor <;> intro h <;> have eq := congrArg Fin.val h
      all_goals change (IngressRepair.machine k).reject.val=_ at eq
                simp only [v.2.1,v.2.2.1,v.2.2.2.1] at eq; omega
private theorem route_safe (k : Nat) (s : Fin SmallIngress.producer.stateCount) :
    SmallIngress.producer.seqRoute (Cursor.machine k) s≠(IngressRepair.machine k).accept ∧
    SmallIngress.producer.seqRoute (Cursor.machine k) s≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
    SmallIngress.producer.seqRoute (Cursor.machine k) s≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58) := by
  have v := values k
  have r : (SmallIngress.producer.seqRoute (Cursor.machine k) s).val<288 ∨
      (SmallIngress.producer.seqRoute (Cursor.machine k) s).val=288 ∨
      (SmallIngress.producer.seqRoute (Cursor.machine k) s).val=328 := by
    unfold UniformTM.seqRoute
    split_ifs
    · right; left; rfl
    · right; right; exact v.2.1
    · left; exact s.isLt
  constructor
  · intro h
    have eq := congrArg Fin.val h
    rw [v.1] at eq
    omega
  · constructor <;> intro h <;> have eq := congrArg Fin.val h
    all_goals simp only [v.2.2.1,v.2.2.2.1] at eq; omega
/-- All canonical pairs reach the FIRST literal producer reject or actual
Cursor entry on the repaired raw table. No content/header premise is supplied. -/
theorem producer_entry (k : Nat) : Target.ProducerEntry k := by
  intro a m x w
  by_cases tag : FixedContentTagGate.tagMatches (Fin.append x w)=true
  · cases gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none =>
      obtain ⟨T,price,done,strict,_safe,_sound,_⟩ := RawFrontier.syntactic_reject k x w (Or.inr gamma)
      exact from_old_negative k x w T price done (fun u hu => (strict u hu).2)
    | some z =>
      have width := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
      by_cases physical : z=0 ∨ 9+z<a+m
      · obtain ⟨T,price,yes | no⟩ := supported_producer x w z tag gamma physical
        · let p := initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
          obtain ⟨t,ht,first,whole⟩ := Body.first_accept_whole SmallIngress.producer p T (SmallIngress.producer.run T p) rfl yes
          have endpoint : (SmallIngress.producer.run t p).state=SmallIngress.producer.accept := by rw [whole]; exact yes
          have path (u : Nat) (hu : u≤t) : (AllArityCursor.machine k).run u
              (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
              SmallIngress.producer.seqEmbedRouted (Cursor.machine k) (SmallIngress.producer.run u p) :=
            SmallIngress.producer.seq_run_left (Cursor.machine k) p first u hu
          have same := IngressRepair.supported_transport k x w z tag gamma physical
          have endState : ((IngressRepair.machine k).run t (initialConfig (IngressRepair.machine k)
              (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
                IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start := by
            rw [same t,path t le_rfl]
            change SmallIngress.producer.seqRoute (Cursor.machine k) (SmallIngress.producer.run t p).state=_
            rw [endpoint]
            simp only [UniformTM.seqRoute]
            rfl
          apply finish k x w t (ht.trans price) (Or.inr endState)
          intro u hu
          dsimp only
          rw [same u,path u hu]
          exact route_safe k _
        · obtain ⟨t,ht,done,strict,_safe,_sound⟩ := RawFrontier.producer_reject_frontier k x w T price no
          exact from_old_negative k x w t ht done (fun u hu => (strict u hu).2)
      · have pos : 0<z := by omega
        have short : a+m=9+z := by omega
        obtain ⟨t,_h,price,done,prior,safe⟩ := IngressRepair.missing_payload_run k x w z tag gamma pos short
        have v := values k
        apply finish k x w t price (Or.inl (congrArg Config.state done))
        intro u hu
        refine ⟨safe u hu,?_⟩
        by_cases lt : u<t
        · have low := prior u lt
          constructor <;> intro h <;> have eq := congrArg Fin.val h
          all_goals simp only [v.2.2.1,v.2.2.2.1] at eq; omega
        · have eq : u=t := by omega
          subst u
          rw [done]
          constructor <;> intro h <;> have eq := congrArg Fin.val h
          all_goals simp only [v.2.1,v.2.2.1,v.2.2.2.1] at eq; omega
  · have bad : FixedContentTagGate.tagMatches (Fin.append x w)=false := by cases h : FixedContentTagGate.tagMatches (Fin.append x w) <;> simp_all
    obtain ⟨T,price,done,strict,_safe,_sound,_⟩ := RawFrontier.syntactic_reject k x w (Or.inl bad)
    exact from_old_negative k x w T price done (fun u hu => (strict u hu).2)
end RepairedFrontier
