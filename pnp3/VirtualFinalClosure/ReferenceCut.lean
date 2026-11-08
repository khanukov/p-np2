import VirtualFinalClosure.ConfigFields
import Lean.Elab.Tactic.AsAuxLemma
namespace VirtualFinalClosure.ReferenceCut
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
set_option autoImplicit false
/-- Natural control projection only. This is not a machine state rewrite. -/
private def isFrontier (k q : Nat) : Prop :=
  q=(CertificateGuardClosure.machine k).reject.val ∨
  (∃ b : Bool,q=(CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))).val) ∨
  (∃ mode : Fin 3,q=(CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.body k (SerializedBody.entry mode)))).val)
private theorem discard_witness {P : Prop} {A B C : P → Prop} {R : Prop}
    (h : ∃ proof : P,A proof ∧ B proof ∧ C proof ∧ R) : R := by
  obtain ⟨proof,_a,_b,_c,last⟩:=h
  exact last
universe u
/-- Import-boundary factoring: opaque machines/tapes keep the logical projection
independent of the large concrete ROM and codec expressions. -/
private theorem classify_case {states N B : Nat} {α : Sort u}
    (r : Config states N B) (leaf entry : Fin states)
    (head : Fin (tapeLength N B)) (normal eof clear : Fin (tapeLength N B) → Option Bool)
    {P1 P2 P3 P4 P5 P6 P7 P8 : Prop} {A C D : α → Prop}
    (outcome :
      (P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ r=⟨entry,head,normal⟩) ∨
      (∃ witness : α,A witness ∧ C witness ∧ D witness ∧
        ((P6 ∧ r=⟨leaf,head,eof⟩) ∨ (P7 ∧ P8 ∧ r=⟨leaf,head,clear⟩)))) :
    r.state.val=leaf.val ∨ r.state.val=entry.val := by
  rcases outcome with normal|virtual
  · exact Or.inr (congrArg (fun c=>c.state.val) normal.2.2.2.2.2)
  · obtain ⟨witness,_a,_c,_d,last⟩:=virtual
    rcases last with eof|clear
    · exact Or.inl (congrArg (fun c=>c.state.val) eof.2)
    · exact Or.inl (congrArg (fun c=>c.state.val) clear.2.2)
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("total","totalState"),("extension","extendState"),("guarded","guardedState")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.VirtualFinalClosure.ConfigFields." &&
      n.toString.endsWith (".VirtualFinalClosure.ConfigFields."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique shallow configuration projection {key}"
private theorem endpoint_state (k N t d : Nat) (y : Bitstring N)
    (hBudget : FixedRawLengthFence.allocation N ≤ TotalIngressClosure.allocation k N)
    (endpoint : (TotalIngressClosure.machine k).run t
      (initialConfig (TotalIngressClosure.machine k) (TotalIngressClosure.allocation k N) y)=
        TotalIngressClosure.config k (IngressAllocation.extendConfig hBudget
          ((BodyIngress.machine k).run d (initialConfig (BodyIngress.machine k)
            (FixedRawLengthFence.allocation N) y)))) :
    ((TotalIngressClosure.machine k).run t
      (initialConfig (TotalIngressClosure.machine k) (TotalIngressClosure.allocation k N) y)).state.val=
        10+((BodyIngress.machine k).run d (initialConfig (BodyIngress.machine k)
          (FixedRawLengthFence.allocation N) y)).state.val := by
  have first:=congrArg (fun c=>c.state.val) endpoint
  have second:=totalState k (IngressAllocation.extendConfig hBudget
    ((BodyIngress.machine k).run d (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation N) y)))
  have third:=extendState hBudget ((BodyIngress.machine k).run d
    (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y))
  exact first.trans (second.trans (congrArg (fun q : Nat=>10+q) third))
private theorem total_frontier (k N t : Nat) (y : Bitstring N)
    (front : CertificateGuardClosure.Target.Frontier k N y t) :
    let O:=TotalIngressClosure.machine k
    let c:=initialConfig O (TotalIngressClosure.allocation k N) y
    (O.run t c).state.val=O.reject.val ∨
      (∃ b : Bool,(O.run t c).state.val=10+(BodyIngress.old k
        (CarryWindow.embed k (CanonicalLeaf.result k b))).val) ∨
      (∃ mode : Fin 3,(O.run t c).state.val=10+(BodyIngress.body k (SerializedBody.entry mode)).val) := by
  intro O c
  classical
  by_contra absent
  have rejectAbsent : (O.run t c).state.val ≠ O.reject.val := fun h=>absent (Or.inl h)
  have leafAbsent (b : Bool) : (O.run t c).state.val ≠
      10+(BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))).val :=
    fun h=>absent (Or.inr (Or.inl ⟨b,h⟩))
  have bodyAbsent (mode : Fin 3) : (O.run t c).state.val ≠
      10+(BodyIngress.body k (SerializedBody.entry mode)).val :=
    fun h=>absent (Or.inr (Or.inr ⟨mode,h⟩))
  obtain ⟨_price,_heads,_safe,_first,outcome⟩:=front
  rcases outcome with malformed|decoded
  · as_aux_lemma => exact rejectAbsent (congrArg (fun c=>c.state.val) malformed.2.2.1)
  · as_aux_lemma =>
      obtain ⟨a,m,x,w,hN,_parse,_source,d,_time,_suffix,hBudget,_initial,_footprint,_room,_trace,endpoint,branch⟩:=decoded
      let small:=(BodyIngress.machine k).run d (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)
      have state : (O.run t c).state.val=10+small.state.val := endpoint_state k N t d y hBudget endpoint
      have noNormal (mode : Fin 3) (h : Fin (tapeLength N (FixedRawLengthFence.allocation N)))
          (T : Fin (tapeLength N (FixedRawLengthFence.allocation N)) → Option Bool) :
          small ≠ ⟨BodyIngress.body k (SerializedBody.entry mode),h,T⟩ := by
        intro eq
        exact bodyAbsent mode (state.trans (congrArg (fun c=>10+c.state.val) eq))
      have noLeaf (b : Bool) (h : Fin (tapeLength N (FixedRawLengthFence.allocation N)))
          (T : Fin (tapeLength N (FixedRawLengthFence.allocation N)) → Option Bool) :
          small ≠ ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)),h,T⟩ := by
        intro eq
        exact leafAbsent b (state.trans (congrArg (fun c=>10+c.state.val) eq))
      rcases branch with rejected|parsed
      · as_aux_lemma => exact rejectAbsent (state.trans (congrArg (fun q:Nat=>10+q) (congrArg Fin.val rejected.1)))
      · as_aux_lemma =>
          obtain ⟨n,z,hH,_tag,_gamma,_header,_capacity,_arena,last⟩:=parsed
          rcases last with normal|virtual
          · as_aux_lemma => exact noNormal _ _ _ normal.2.2.2.2.2
          · as_aux_lemma =>
              obtain ⟨_positive,_virtual,_zero,_decode,last⟩:=virtual
              rcases last with eof|clear
              · as_aux_lemma => exact noLeaf false _ _ eof.2
              · as_aux_lemma => exact noLeaf false _ _ clear.2.2
private theorem raw_frontier (k N : Nat) (y : Bitstring N) :
    let O:=CertificateGuardClosure.machine k
    let c:=initialConfig O (CertificateGuardClosure.allocation k N) y
    ∃ t,t ≤ CertificateGuardClosure.deadline k N ∧
      (∀ u,u ≤ t → (O.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (O.run u c).state ≠ O.accept) ∧ isFrontier k (O.run t c).state.val := by
  intro O c
  obtain ⟨t,price,heads,safe,_first,outcome⟩:=CertificateGuardClosure.raw k N y
  refine ⟨t,price,heads,safe,?_⟩
  rcases outcome with malformed|wrong|canonical
  · as_aux_lemma => exact Or.inl (congrArg (fun c=>c.state.val) malformed.2.2.1)
  · obtain ⟨a,m,x,w,hN,_decode,_word,_bad,_price,done,_false⟩:=wrong
    exact Or.inl (congrArg (fun c=>c.state.val) done)
  · obtain ⟨a,m,x,w,hN,_decode,_word,_length,g,d,_time,_price,_low,_entry,_suffix,front,done⟩:=canonical
    have state : (O.run t c).state.val=77+((TotalIngressClosure.machine k).run d
        (initialConfig (TotalIngressClosure.machine k) (TotalIngressClosure.allocation k N) y)).state.val := by
      have eq : (O.run t c).state.val=10+(67+((TotalIngressClosure.machine k).run d
          (initialConfig (TotalIngressClosure.machine k) (TotalIngressClosure.allocation k N) y)).state.val) :=
        congrArg (fun c=>c.state.val) done
      omega
    rcases total_frontier k N d y front with rejected|leaf|body
    · exact Or.inl (state.trans (congrArg (fun q:Nat=>77+q) rejected))
    · right;left
      obtain ⟨b,hit⟩:=leaf
      refine ⟨b,?_⟩
      have eq:=state.trans (congrArg (fun q:Nat=>77+q) hit)
      change (O.run t c).state.val=10+(67+(10+_))
      omega
    · right;right
      obtain ⟨mode,hit⟩:=body
      refine ⟨mode,?_⟩
      have eq:=state.trans (congrArg (fun q:Nat=>77+q) hit)
      change (O.run t c).state.val=10+(67+(10+_))
      omega
/-- Proof-only first-event selection by induction on a real witnessed run time.
No least-number operation or proof-derived runtime datum occurs in the ROM. -/
private theorem first_event {M : UniformTM} {N B : Nat} (c : Config M.stateCount N B)
    (P : Config M.stateCount N B → Prop) (t : Nat) (last : P (M.run t c)) :
    ∃ s,s ≤ t ∧ P (M.run s c) ∧ ∀ u,u < s → ¬P (M.run u c) := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases earlier : ∃ u,u < t ∧ P (M.run u c)
    · obtain ⟨u,hu,event⟩:=earlier
      obtain ⟨s,st,hit,first⟩:=ih u hu event
      exact ⟨s,st.trans hu.le,hit,first⟩
    · exact ⟨t,le_rfl,last,fun u hu event=>earlier ⟨u,hu,event⟩⟩
#print axioms total_frontier
#print axioms raw_frontier
#print axioms first_event
end VirtualFinalClosure.ReferenceCut
