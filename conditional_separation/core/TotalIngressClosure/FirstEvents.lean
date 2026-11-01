import TotalIngressClosure.EventSafety
import TotalIngressClosure.RejectSound
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("EventSafety","leafState","leafState"),("EventSafety","leaf_row","leafRow"),
      ("EventSafety","leaf_stays","leafStays"),("EventSafety","leaf_val","leafVal"),
      ("EventSafety","consumer_separated","separated"),("RejectSound","reject_sound","rejectSound"),
      ("RejectSound","body_nonreject","bodyNonreject")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique exact first-consumer interface {mod}/{key}: {found.map Prod.fst}"
private def Before {k N B : Nat} (c:Config (BodyIngress.machine k).stateCount N B) (t:Nat) : Prop:=
  ∀ u,u < t → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).reject ∧
    (∀ b,((BodyIngress.machine k).run u c).state≠leafState k b) ∧
    (∀ mode:Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry mode))
private theorem earliest (P:Nat → Prop) (T:Nat) (hit:P T) :
    ∃ s,s ≤ T ∧ P s ∧ ∀ u,u < s → ¬P u:=by
  classical
  induction T using Nat.strong_induction_on with
  | h T ih=>
    by_cases earlier:∃ u,u < T ∧ P u
    · obtain ⟨u,lt,hit⟩:=earlier
      obtain ⟨s,le,yes,first⟩:=ih u lt hit
      exact ⟨s,le.trans (Nat.le_of_lt lt),yes,first⟩
    · exact ⟨T,le_rfl,hit,by intro u hu bad;exact earlier ⟨u,hu,bad⟩⟩
private theorem leaf_fixed {k N B:Nat} (v:Bool) (c:Config (BodyIngress.machine k).stateCount N B)
    (hit:c.state=leafState k v) (t:Nat) : (BodyIngress.machine k).run t c=c:=by
  have step:(BodyIngress.machine k).stepConfig c=c:=by
    unfold UniformTM.stepConfig
    rw [hit,leafRow]
    apply Config.ext_parts
    · exact hit.symm
    · rfl
    · funext i
      change (if i=c.head then c.tape c.head else c.tape i)=c.tape i
      by_cases same:i=c.head
      · subst i;rw [if_pos rfl]
      · rw [if_neg same]
  induction t with
  | zero=>rw [UniformTM.run]
  | succ t ih=>rw [UniformTM.run,ih,step]
private theorem leaf_terminal {k:Nat}(v:Bool):leafState k v≠(BodyIngress.machine k).accept ∧
    leafState k v≠(BodyIngress.machine k).reject:=by
  have acceptVal:(BodyIngress.machine k).accept.val=327:=rfl
  have rejectVal:(BodyIngress.machine k).reject.val=328:=rfl
  constructor
  · intro bad
    have eq:=congrArg Fin.val bad
    change (leafState k v).val=(BodyIngress.machine k).accept.val at eq
    rw [leafVal k v,acceptVal] at eq
    unfold Cursor.stateCount at eq
    split_ifs at eq <;> omega
  · intro bad
    have eq:=congrArg Fin.val bad
    change (leafState k v).val=(BodyIngress.machine k).reject.val at eq
    rw [leafVal k v,rejectVal] at eq
    unfold Cursor.stateCount at eq
    split_ifs at eq <;> omega
private theorem safe_through {k N B T:Nat} (c:Config (BodyIngress.machine k).stateCount N B)
    (safe:((BodyIngress.machine k).run T c).state≠(BodyIngress.machine k).accept) :
    ∀ u,u ≤ T → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept:=by
  intro u hu bad
  have keep:=(BodyIngress.machine k).run_accept_of_le c bad hu
  exact safe ((congrArg Config.state keep).trans bad)
set_option maxRecDepth 4000 in
private theorem reject_first (k : Nat) {a m:Nat} (x:Bitstring a)(w:Bitstring m)(T:Nat)
    (hit:((BodyIngress.machine k).run T (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(BodyIngress.machine k).reject)
    (other:∀ u,u < T →
      (∀ b,((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠leafState k b) ∧
      (∀ mode:Fin 3,((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          BodyIngress.body k (SerializedBody.entry mode))) :
    let c:=initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ s,s ≤ T ∧ ((BodyIngress.machine k).run s c).state=(BodyIngress.machine k).reject ∧
      (BodyIngress.machine k).run s c=(BodyIngress.machine k).run T c ∧ Before c s ∧
      (∀ u,u ≤ s → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false:=by
  intro c
  obtain ⟨s,le,yes,first⟩:=earliest (fun t=>((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject) T hit
  have noOthers(u:Nat)(hu:u < s):=
    other u (hu.trans_le le)
  refine ⟨s,le,yes,((BodyIngress.machine k).run_reject_of_le c yes le).symm,?_,?_,?_⟩
  · intro u hu;exact ⟨first u hu,(noOthers u hu).1,(noOthers u hu).2⟩
  · apply safe_through c
    rw [yes]
    exact (BodyIngress.machine k).accept_ne_reject.symm
  · exact rejectSound k x w s yes noOthers
set_option maxRecDepth 4000 in
private theorem normal_first {k N B T:Nat}(c:Config (BodyIngress.machine k).stateCount N B)(mode:Fin 3)
    (hit:((BodyIngress.machine k).run T c).state=BodyIngress.body k (SerializedBody.entry mode))
    (first:∀ u,u < T → ∀ m:Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry m)) :
    Before c T ∧ ∀ u,u ≤ T → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept:=by
  have nr:((BodyIngress.machine k).run T c).state≠(BodyIngress.machine k).reject:=by rw [hit];exact bodyNonreject k mode
  have na:((BodyIngress.machine k).run T c).state≠(BodyIngress.machine k).accept:=by
    rw [hit]
    intro bad
    have eq: (BodyIngress.machine k).accept=BodyIngress.old k (CarryWindow.machine k).accept:=
      (BodyIngress.embeddings k).2.2.1
    exact (BodyIngress.embeddings k).2.2.2.2.2.2 _ mode (eq.symm.trans bad.symm)
  refine ⟨?_,safe_through c na⟩
  intro u hu
  refine ⟨?_,?_,first u hu⟩
  · intro bad
    exact nr ((congrArg Config.state ((BodyIngress.machine k).run_reject_of_le c bad (Nat.le_of_lt hu))).trans bad)
  · intro b bad
    exact separated b c bad ⟨_,hit⟩
set_option maxRecDepth 4000 in
private theorem leaf_first {k N B T:Nat}(c:Config (BodyIngress.machine k).stateCount N B)
    (hit:((BodyIngress.machine k).run T c).state=leafState k false)
    (first:∀ u,u < T → ∀ m:Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry m)) :
    ∃ s,s ≤ T ∧ (BodyIngress.machine k).run s c=(BodyIngress.machine k).run T c ∧ Before c s ∧
      (∀ u,u ≤ s → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept):=by
  obtain ⟨s,le,yes,early⟩:=earliest (fun t=>((BodyIngress.machine k).run t c).state=leafState k false) T hit
  have whole:(BodyIngress.machine k).run s c=(BodyIngress.machine k).run T c:=by
    rw [show T=s+(T-s) by omega,UniformTM.run_add,leaf_fixed false _ yes]
  refine ⟨s,le,whole,?_,?_⟩
  · intro u hu
    refine ⟨?_,?_,first u (hu.trans_le le)⟩
    · intro bad
      have eq:=(congrArg Config.state ((BodyIngress.machine k).run_reject_of_le c bad (hu.le.trans le))).trans bad
      rw [hit] at eq
      exact (leaf_terminal false).2 eq
    · intro b bad
      have kept:=leafStays b ((BodyIngress.machine k).run u c) bad (s-u)
      rw [←UniformTM.run_add,show u+(s-u)=s by omega,yes] at kept
      cases b
      · exact early u hu bad
      · have eq:=congrArg Fin.val kept
        change (leafState k false).val=(leafState k true).val at eq
        rw [leafVal k false,leafVal k true] at eq
        norm_num at eq
  · apply safe_through c
    rw [yes];exact (leaf_terminal false).1
end TotalIngressClosure
