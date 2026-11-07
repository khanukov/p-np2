import VirtualFinalClosure.WorkspaceImage
import VirtualFinalClosure.LengthReplay
namespace VirtualFinalClosure.Recompute
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("IngressAllocation.WorkspaceTrace","IngressAllocation","workspace_heads","workspaceHeads",1),
      ("VirtualFinalClosure.WorkspaceImage","VirtualFinalClosure.WorkspaceImage","ready","readyImage",1),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","workspace_floor","workspaceFloor",1),
      ("VirtualFinalClosure.StrictLength","VirtualFinalClosure.StrictLength","strict_phase","strictPhase",1),
      ("VirtualFinalClosure.LengthReplay","VirtualFinalClosure.LengthReplay","range","lengthRange",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","run_lift","runLift",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual whole arithmetic replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual whole arithmetic replay interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 329) : (Cursor.q k i).val=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
private theorem price (n r E a b : Nat) (ha : a ≤ 128*(n+r+1)*(E+1))
    (hb : b ≤ 2048*(n+1)*E) : a+b ≤ 4096*(n+r+1)*(E+1) := by
  have product:=Nat.mul_le_mul (Nat.mul_le_mul_left 2048 (show n+1 ≤ n+r+1 by omega)) (show E ≤ E+1 by omega)
  nlinarith only [ha,hb,product,Nat.zero_le ((n+r+1)*(E+1))]
/-- Actual installed bank0 -> full workspace -> alternating bitLength, on the
SAME product table and allocation. Both length-overflow controls remain genuine
live endpoints. Every intermediate Config, head and control is transported. -/
private theorem prepared (k N B S L n Q F r : Nat) (G : Nat → Option Bool) (m : Fin 144)
    (positive : 0 < r) (fr : Frame G S L (L+n+1) Q F)
    (regFalse : ∀ i,S < i → i < L → G i=some false)
    (assnFalse : ∀ i,L < i → i < L+n+1 → G i=some false)
    (bank0 : ∀ i,F+1 < i → i < F+r+2 → G i=some true)
    (fresh : ∀ i,F+r+2 ≤ i → i ≤ F+5*r+n+7 → G i=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    let i:=if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304
    let h:=if bitLength n ≤ r then L else F+r+n+3
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k 98) m,⟨S,by obtain ⟨sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun j=>G j.val⟩
    ∃ (t : Nat) (hf : h < tapeLength N B),t ≤ 4096*(n+r+1)*(F+5*r+n+9) ∧
      (machine k).run t start=
        ⟨control k (tableControl k i) m,⟨h,hf⟩,
          fun j=>RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image G L n F r) L n F r j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*r+n+7) ∧
      (∀ u,u < t → ∀ (j : Nat),j=250 ∨ j=304 ∨ j=308 → ∀ flag : Fin 144,
        ((machine k).run u start).state≠control k (tableControl k j) flag) ∧
      (∀ u,u ≤ t →
        let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.rReady k,⟨S,by obtain ⟨sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun j=>G j.val⟩
        (machine k).run u start=lift k m ((Cursor.machine k).run u old) ∧
        98 ≤ ((Cursor.machine k).run u old).state.val ∧ ((Cursor.machine k).run u old).state.val ≤ 308) := by
  intro i h start
  have copyFr:=fr
  obtain ⟨sl,_lh,paid,room,eof,sep,right,d0,fence,_register,_assignment,marks,gap⟩:=copyFr
  let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.rReady k,⟨S,by omega⟩,fun j=>G j.val⟩
  let X:=CappedWorkspace.Target.image G L n F r
  let mid : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 201,⟨F+1,by omega⟩,fun j=>X j.val⟩
  obtain ⟨a,ap,wa,wb,wh⟩:=workspaceHeads k N B S L n Q F r G sl paid room eof regFalse sep assnFalse right marks gap fence d0 bank0 fresh fit
  have oldValue : old.state.val=98:=q_value k 98 (by decide)
  have wValue : ((Cursor.machine k).run a old).state.val=201:=by rw [wa];exact q_value k 201 (by decide)
  have wFloor:=workspaceFloor k N B a old oldValue wValue wb
  obtain ⟨⟨_sl,_lh,_paid,_room,_eof,xsep,xright,xd0,xfence,_reg,_assign,xmarks,xgap⟩,xassn,xb0,xd1,xb1,xd2,xb2,xd3⟩:=readyImage G S L n Q F r fr bank0 fresh
  obtain ⟨b,hf,bp,la,lh,lb,_upper⟩:=strictPhase k N B L n Q F r X positive paid room xsep xassn xright xmarks xgap xfence xd0 xb0 xd1 xb1 xd2 xb2 xd3 fit
  have ie : i=250 ∨ i=304 ∨ i=308:=by dsimp only [i];split_ifs <;> omega
  have iv : (Cursor.q k i).val=i:=q_value k i (by rcases ie with hi|hi|hi <;> omega)
  have lValue : ((Cursor.machine k).run b mid).state.val=i:=by rw [la];exact iv
  have lRange:=lengthRange k N B b mid (q_value k 201 (by decide))
    (by rw [lValue];exact ie) lb
  have band : ∀ u,u ≤ a+b → 98 ≤ ((Cursor.machine k).run u old).state.val ∧
      ((Cursor.machine k).run u old).state.val ≤ 308 := by
    intro u hu
    by_cases early : u < a
    · have low:=wFloor u early.le
      have high:=wb u early
      change ((Cursor.machine k).run u old).state.val < 201 at high
      exact ⟨low,by omega⟩
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,wa]
      have bounds:=lRange (u-a) (by omega)
      exact ⟨(by decide : 98 ≤ 201).trans bounds.1,bounds.2⟩
  have avoids : ∀ u,u < a+b → ((Cursor.machine k).run u old).state.val≠250 ∧
      ((Cursor.machine k).run u old).state.val≠304 ∧ ((Cursor.machine k).run u old).state.val≠308 := by
    intro u hu
    by_cases early : u < a
    · have high:=wb u early
      change ((Cursor.machine k).run u old).state.val < 201 at high
      exact ⟨by omega,by omega,by omega⟩
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,wa]
      exact lb (u-a) (by omega)
  have simulation:=runLift k m old (a+b) (by intro u hu;have h:=band u hu;omega)
    (by intro u hu;exact ⟨by have h:=band u hu.le;omega,(avoids u hu).1,(avoids u hu).2.1⟩)
  have initial : start=lift k m old := by
    apply Config.ext_parts
    · exact (congrArg (fun q=>control k (tableControl k q) m) oldValue).symm
    · rfl
    · rfl
  have oldDone : (Cursor.machine k).run (a+b) old=
      (⟨Cursor.q k i,⟨h,hf⟩,fun j=>RuntimeBitLength.Target.fullImage X L n F r j.val⟩ : Config (Cursor.machine k).stateCount N B) := by
    rw [UniformTM.run_add,wa,la]
  have done:=simulation (a+b) le_rfl
  rw [←initial,oldDone] at done
  refine ⟨a+b,hf,price n r (F+5*r+n+8) a b ap bp,?_,?_,?_,?_⟩
  · simpa only [lift,iv] using done
  · intro u hu
    rw [initial,simulation u hu]
    by_cases early : u ≤ a
    · exact wh u early
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,wa]
      exact lh (u-a) (by omega)
  · intro u hu j which flag equal
    have current:=simulation u hu.le
    rw [←initial] at current
    have val : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val := by
      rw [current];exact slotValue k ((Cursor.machine k).run u old).state m
    have target:=slotValue k (Cursor.q k j) flag
    rw [q_value k j (by rcases which with hj|hj|hj <;> omega)] at target
    have same:=congrArg Fin.val equal
    rw [val,target] at same
    have fm:=m.isLt
    have ff:=flag.isLt
    have num : ((Cursor.machine k).run u old).state.val=j:=by omega
    have no:=avoids u hu
    rcases which with hj|hj|hj <;> omega
  · intro u hu
    exact ⟨by rw [initial];exact simulation u hu,(band u hu).1,(band u hu).2⟩
#print axioms q_value
#print axioms price
#print axioms prepared
end VirtualFinalClosure.Recompute
