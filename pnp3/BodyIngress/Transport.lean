import BodyIngress.Target
namespace BodyIngress
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let names:=(← getEnv).constants.toList.map Prod.fst
  for (mod,key,localName,thm) in [
      ("BodyIngress.Machine","rows","ownRows",false),
      ("BodyIngress.Machine","extend","ownExtend",false),
      ("BodyIngress.Machine","liftOld","ownLift",false),
      ("CarryReadyCompletion.Native","ready_stays","readyStays",true)] do
    let found:=names.filter fun n => n.toString.startsWith ("_private."++mod++".") &&
      n.toString.endsWith ("."++(if mod="BodyIngress.Machine" then "BodyIngress" else "CarryReadyCompletion")++"."++key)
    match found with
    | [n] =>
      let ci ← getConstInfo n
      let isThm:=match ci with | .thmInfo _ => true | _ => false
      unless isThm=thm do throwError "Wrong declaration kind: {n}"
      logInfo m!"private-term|{mod}|{n}|{ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) n :: st.openDecls}
    | _ => throwError "Nonunique private declaration {key}: {found}"
private theorem old_inj {k : Nat} {s t : Fin (CarryWindow.machine k).stateCount}
    (h : old k s=old k t) : s=t := by
  have e:=congrArg (fun q : Fin ((CarryWindow.machine k).stateCount+7500+2035) => q.val) h
  dsimp only [old] at e
  exact Fin.ext e
private theorem ready_ne_verdicts (k : Nat) :
    CarryWindow.ready k  ≠  (CarryWindow.machine k).accept   ∧
    CarryWindow.ready k  ≠  (CarryWindow.machine k).reject := by
  constructor
  all_goals intro h; have e:=congrArg Fin.val h
  · change (CanonicalLeaf.machine k).stateCount+24=(CanonicalLeaf.machine k).accept.val at e
    have b:=(CanonicalLeaf.machine k).accept.isLt; omega
  · change (CanonicalLeaf.machine k).stateCount+24=(CanonicalLeaf.machine k).reject.val at e
    have b:=(CanonicalLeaf.machine k).reject.isLt; omega
/-- The effective old table differs at exactly the single Ready/read-none row. -/
theorem table_delta (k : Nat) (s : Fin (CarryWindow.machine k).stateCount) (b : Option Bool) :
    (machine k).step (old k s) b=
      if s=CarryWindow.ready k   ∧   b=none then (extra k ⟨0,by decide⟩,none,.stay)
      else (old k ((CarryWindow.machine k).step s b).1,((CarryWindow.machine k).step s b).2) := by
  have ne:=ready_ne_verdicts k
  by_cases a:s=(CarryWindow.machine k).accept
  · subst s
    rw [if_neg (by tauto),UniformTM.step_accept]
    exact (machine k).step_accept b
  by_cases r:s=(CarryWindow.machine k).reject
  · subst s
    rw [if_neg (by tauto),UniformTM.step_reject]
    exact (machine k).step_reject b
  have na:old k s  ≠  (machine k).accept:=fun h=>a (old_inj (k:=k) h)
  have nr:old k s  ≠  (machine k).reject:=fun h=>r (old_inj (k:=k) h)
  rw [UniformTM.step_of_ne (machine k) na nr]
  change ownRows k (old k s) b=_
  dsimp only [ownRows,old]
  rw [dif_pos s.isLt]
  rfl
/-- The frozen BODY ROM, including both literal verdicts, executes unchanged. -/
theorem body_rows (k : Nat) (s : Fin SerializedBody.machine.stateCount) (b : Option Bool) :
    (machine k).step (body k s) b=
      (body k (SerializedBody.machine.step s b).1,(SerializedBody.machine.step s b).2) := by
  by_cases a:s.val=0
  · have eqs:s=SerializedBody.machine.accept:=Fin.ext a
    subst s
    rw [UniformTM.step_accept]
    exact (machine k).step_accept b
  by_cases r:s.val=1
  · have eqs:s=SerializedBody.machine.reject:=Fin.ext r
    subst s
    rw [UniformTM.step_reject]
    exact (machine k).step_reject b
  have av:body k s  ≠  (machine k).accept:=by
    intro bad; have eqv:=congrArg Fin.val bad
    dsimp only [body] at eqv
    rw [if_neg a,if_neg r] at eqv
    have small:=(CarryWindow.machine k).accept.isLt
    change (CarryWindow.machine k).stateCount+s.val=(CarryWindow.machine k).accept.val at eqv
    omega
  have rv:body k s  ≠  (machine k).reject:=by
    intro bad; have eqv:=congrArg Fin.val bad
    dsimp only [body] at eqv
    rw [if_neg a,if_neg r] at eqv
    have small:=(CarryWindow.machine k).reject.isLt
    change (CarryWindow.machine k).stateCount+s.val=(CarryWindow.machine k).reject.val at eqv
    omega
  rw [UniformTM.step_of_ne (machine k) av rv]
  change ownRows k (body k s) b=_
  dsimp only [body]
  rw [if_neg a,if_neg r]
  dsimp only [ownRows]
  rw [dif_neg (by have h:=s.isLt; change s.val  <  7500 at h; omega),dif_pos (by have h:=s.isLt; change s.val  <  7500 at h; omega)]
  have qs:(⟨(CarryWindow.machine k).stateCount+s.val-(CarryWindow.machine k).stateCount,by omega⟩ : Fin SerializedBody.machine.stateCount)=s:=by
    apply Fin.ext; dsimp; omega
  rw [qs]
  rfl
private theorem step_lift {k N B : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (safe : c.state  ≠  CarryWindow.ready k) :
    (machine k).stepConfig (config k c)=config k ((CarryWindow.machine k).stepConfig c) := by
  unfold UniformTM.stepConfig
  dsimp only [config]
  rw [table_delta,if_neg (fun h=>safe h.1)]
/-- Every prefix up to the actual first Ready is transported with its complete Config. -/
theorem transport {k N B t : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (safe : ∀ u,u  <  t   →   ((CarryWindow.machine k).run u c).state  ≠  CarryWindow.ready k) :
    ∀ u,u  ≤  t   →   (machine k).run u (config k c)=config k ((CarryWindow.machine k).run u c) := by
  intro u hu
  induction u with
  | zero => rw [UniformTM.run,UniformTM.run]
  | succ u ih => rw [UniformTM.run,ih (by omega),step_lift _ (safe u (by omega)),UniformTM.run]
private theorem ready_step {k N B : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (ready : c.state=CarryWindow.ready k) : (CarryWindow.machine k).stepConfig c=c := by
  apply Config.ext_parts
  · dsimp only [UniformTM.stepConfig]
    rw [ready,readyStays]
  · dsimp only [UniformTM.stepConfig]
    rw [ready,readyStays]
    rfl
  · dsimp only [UniformTM.stepConfig]
    rw [ready,readyStays]
    funext i
    split_ifs with h
    · cases h; rfl
    · rfl
private theorem ready_run {k N B : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (ready : c.state=CarryWindow.ready k) (t : Nat) : (CarryWindow.machine k).run t c=c := by
  induction t with
  | zero => rw [UniformTM.run]
  | succ t ih => rw [UniformTM.run,ih,ready_step c ready]
/-- Any old run ending outside Ready excludes that cut at every earlier time. -/
theorem transport_stopped {k N B t : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (notReady : ((CarryWindow.machine k).run t c).state  ≠  CarryWindow.ready k) :
    ∀ u,u  ≤  t   →   (machine k).run u (config k c)=config k ((CarryWindow.machine k).run u c) := by
  apply transport c
  intro u hu bad
  have same:=ready_run ((CarryWindow.machine k).run u c) bad (t-u)
  rw [← UniformTM.run_add,show u+(t-u)=t by omega] at same
  exact notReady ((congrArg Config.state same).trans bad)
/-- The reviewed producer138/read-none repair is retained on this table. -/
theorem repair138 (k : Nat) :
    (machine k).step (old k (CarryWindow.embed k (VirtualLeaf.embed k
      (IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138))))) none=
      ((machine k).reject,none,.stay) := by
  rw [table_delta,if_neg (by
    intro h;have eqv:=congrArg Fin.val h.1
    change 138=(CanonicalLeaf.machine k).stateCount+24 at eqv
    have hi: (CanonicalLeaf.machine k).stateCount  ≥  139:=by change 288+Cursor.stateCount k+8  ≥  139;omega
    omega),CarryWindow.repair138]
  rfl

/-- Both component control maps are injective; all old states precede every BODY entry. -/
theorem embeddings (k : Nat) :
    (machine k).stateCount=(CarryWindow.machine k).stateCount+7500+2035  ∧
    (machine k).start=old k (CarryWindow.machine k).start  ∧
    (machine k).accept=old k (CarryWindow.machine k).accept  ∧
    (machine k).reject=old k (CarryWindow.machine k).reject  ∧
    Function.Injective (old k)  ∧  Function.Injective (body k)  ∧
    (∀ s (m:Fin 3),old k s ≠ body k (SerializedBody.entry m)) := by
  refine ⟨rfl,rfl,rfl,rfl,fun _ _ h=>old_inj (k:=k) h,?_,?_⟩
  · intro s t h
    have e:=congrArg (fun q:Fin ((CarryWindow.machine k).stateCount+7500+2035)=>q.val) h
    dsimp only [body] at e
    split_ifs at e <;> dsimp only [old] at e
    all_goals have ha:=(CarryWindow.machine k).accept.isLt
    all_goals have hr:=(CarryWindow.machine k).reject.isLt
    all_goals first
      | exact Fin.ext (by omega)
      | exact False.elim ((CarryWindow.machine k).accept_ne_reject (Fin.ext e))
      | exact False.elim ((CarryWindow.machine k).accept_ne_reject (Fin.ext e.symm))
  · intro s m bad
    have bv:(body k (SerializedBody.entry m)).val=(CarryWindow.machine k).stateCount+4+m.val:=by
      fin_cases m <;> rfl
    have e:=congrArg (fun q:Fin ((CarryWindow.machine k).stateCount+7500+2035)=>q.val) bad
    dsimp only at e
    rw [bv] at e
    dsimp only [old] at e
    have bound:=s.isLt
    omega


theorem check_table_delta (k : Nat) (s : Fin (CarryWindow.machine k).stateCount) (b : Option Bool) :
    (machine k).step (old k s) b=
      if s=CarryWindow.ready k   ∧   b=none then (extra k ⟨0,by decide⟩,none,.stay)
      else (old k ((CarryWindow.machine k).step s b).1,((CarryWindow.machine k).step s b).2) := by
  exact table_delta k s b

theorem check_body_rows (k : Nat) (s : Fin SerializedBody.machine.stateCount) (b : Option Bool) :
    (machine k).step (body k s) b=
      (body k (SerializedBody.machine.step s b).1,(SerializedBody.machine.step s b).2) := by
  exact body_rows k s b

theorem check_transport {k N B t : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (safe : ∀ u,u  <  t   →   ((CarryWindow.machine k).run u c).state  ≠  CarryWindow.ready k) :
    ∀ u,u  ≤  t   →   (machine k).run u (config k c)=config k ((CarryWindow.machine k).run u c) := by
  exact transport c safe

theorem check_transport_stopped {k N B t : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (notReady : ((CarryWindow.machine k).run t c).state  ≠  CarryWindow.ready k) :
    ∀ u,u  ≤  t   →   (machine k).run u (config k c)=config k ((CarryWindow.machine k).run u c) := by
  exact transport_stopped c notReady

theorem check_repair138 (k : Nat) :
    (machine k).step (old k (CarryWindow.embed k (VirtualLeaf.embed k
      (IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138))))) none=
      ((machine k).reject,none,.stay) := by
  exact repair138 k

theorem check_embeddings (k : Nat) :
    (machine k).stateCount=(CarryWindow.machine k).stateCount+7500+2035  ∧
    (machine k).start=old k (CarryWindow.machine k).start  ∧
    (machine k).accept=old k (CarryWindow.machine k).accept  ∧
    (machine k).reject=old k (CarryWindow.machine k).reject  ∧
    Function.Injective (old k)  ∧  Function.Injective (body k)  ∧
    (∀ s (m:Fin 3),old k s ≠ body k (SerializedBody.entry m)) := by
  exact embeddings k
end BodyIngress
