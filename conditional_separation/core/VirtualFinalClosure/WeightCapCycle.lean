import VirtualFinalClosure.WeightCapFrame
import VirtualFinalClosure.GrowthCycle
import VirtualFinalClosure.RepeatEntry
namespace VirtualFinalClosure.WeightCapCycle
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","image",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","digits","capacityDigits",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","capacityTail",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","frame","fullFrame",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","doubled_image","doubledImage",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","banks","capBanks",1),
      ("VirtualFinalClosure.GrowthCycle","VirtualFinalClosure.GrowthCycle","grow","grow",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","old_terminals",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","from_old_row","from_old_row",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.RepeatEntry","VirtualFinalClosure.RepeatEntry","from_d0","route",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual repeated-growth execution interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual repeated-growth execution interface {mod}/{key}"
private theorem weight_step (k m : Nat) (hm : m < 144) (ph : phase m=1) :
    (machine k).step (control k (tableControl k (798+93*k)) ⟨m,hm⟩) none=(nc k 4 m,none,.stay) := by
  let i:=798+93*k
  let s:=tableControl k i
  have bound : i<Cursor.stateCount k := by dsimp only [i];unfold Cursor.stateCount;omega
  have outside : s≠(CertificateGuardClosure.machine k).accept ∧ s≠(CertificateGuardClosure.machine k).reject := by
    obtain ⟨av,rv⟩:=old_terminals k
    have value:=tableValue k i bound
    constructor <;> intro bad <;> have same:=congrArg Fin.val bad
    · rw [av] at same
      change (tableControl k (798+93*k)).val=414 at same
      rw [value] at same
      dsimp only [i] at *;omega
    · rw [rv] at same
      change (tableControl k (798+93*k)).val=415 at same
      rw [value] at same
      dsimp only [i] at *;omega
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true) := by
    have noLeaf (b : Bool) : s≠leafControl k b := by
      intro bad
      have same:=congrArg Fin.val bad
      change (tableControl k (798+93*k)).val=(leafControl k b).val at same
      rw [tableValue k i bound,leafValue] at same
      unfold Cursor.stateCount at same
      dsimp only [i] at *;cases b <;> omega
    exact fun h=>h.elim (noLeaf false) (noLeaf true)
  have row : oldRow k s.val m none=((CertificateGuardClosure.machine k).stateCount+4,m,none,.stay) := by
    have hs : (⟨s.val%(CertificateGuardClosure.machine k).stateCount,
        Nat.mod_lt _ (by have h:=(CertificateGuardClosure.machine k).start.isLt;omega)⟩ :
        Fin (CertificateGuardClosure.machine k).stateCount)=s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
    dsimp only [oldRow]
    have distinct : s≠tableControl k 250 ∧ s≠tableControl k 304 := by
      constructor
      · intro equal
        have same:=congrArg Fin.val equal
        change (tableControl k i).val=(tableControl k 250).val at same
        rw [tableValue k i bound,tableValue k 250 (by unfold Cursor.stateCount;omega)] at same
        dsimp only [i] at same;omega
      · intro equal
        have same:=congrArg Fin.val equal
        change (tableControl k i).val=(tableControl k 304).val at same
        rw [tableValue k i bound,tableValue k 304 (by unfold Cursor.stateCount;omega)] at same
        dsimp only [i] at same;omega
    rw [hs,if_neg leaves,if_neg (fun h=>h.2.2.elim distinct.1 distinct.2),if_pos ⟨by omega,rfl,rfl⟩]
  exact from_old_row k s m 4 hm (by decide) outside row
/-- Every genuine W-cap residual is physically consumed, not replaced by
clean operands: execute live cap D0, reset/double all six occupied banks,
return to the actual EOF and paint the assignment before q98. -/
private theorem cycle (k N B S L n Q F C v2 v3 v4 v5 d : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C)
    (fr : Frame T S L (L+n+1) Q F)
    (assignment : ∀ j,L < j → j < L+n+1 → T j=some false)
    (fit : F+5*C+n+7 < tapeLength N B) :
    let Y:=residual T L n F C v2 v3 v4 v5 d
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k (798+93*k)) m,⟨F+1,by omega⟩,fun j=>Y j.val⟩
    ∃ (t : Nat) (hs : S < tapeLength N B),
      t ≤ 2+(C*(4*C+7)+2*n+14*C+27)+(F-S+3)+1 ∧
      (machine k).run t start=
        ⟨control k (tableControl k 98) m,⟨S,hs⟩,fun j=>image T F (2*C) j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*C+n+7) := by
  intro Y start
  let P:=F+5*C+n+7
  have copyFr:=fr
  obtain ⟨_sl,_lh,_paid,room,_eof,_sep,_right,d0,_fence,_reg,_assn,_marks,_gap⟩:=copyFr
  have below : L+n+1 < F:=by omega
  obtain ⟨blank,occupied⟩:=capBanks T L n F C v2 v3 v4 v5 d positive below d0
  have frY:=fullFrame T S L n Q F C v2 v3 v4 v5 d fr
  have yd0 : Y (F+1)=none:=blank 0 (by decide)
  have enter:=keep (M:=machine k) (P:=P) (control k (tableControl k (798+93*k)) m) (nc k 4 m.val)
    (F+1) (F+1) Y .stay (by dsimp only [P];omega) (by dsimp only [P];omega)
    (by rw [yd0];exact weight_step k m.val m.isLt ph) rfl
  have seek:=route k P F m.val Y m.isLt ph (by dsimp only [P];omega) yd0
  obtain ⟨v,vp,grown⟩:=grow k P m.val S L (L+n+1) Q F C Y m.isLt ph frY positive
    (by dsimp only [P];omega)
    (by intro j hj;simpa only [show (L+n+1)-L-1=n by omega] using blank j hj)
    (by
      intro j hj p lo hi
      exact occupied j hj p
        (by simpa only [show (L+n+1)-L-1=n by omega] using lo)
        (by simpa only [show (L+n+1)-L-1=n by omega] using hi))
  rw [show (L+n+1)-L-1=n by omega] at vp grown
  rw [doubledImage T L n F C v2 v3 v4 v5 d below assignment] at grown
  have joined:=joinPath (joinPath enter seek) grown
  have actual:=execute (N:=N) (B:=B) joined fit
  have heads:=through (N:=N) (B:=B) joined fit
  exact ⟨1+1+v,by omega,by omega,actual,heads⟩
#print axioms weight_step
#print axioms cycle
end VirtualFinalClosure.WeightCapCycle
