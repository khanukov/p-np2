import VirtualFinalClosure.WeightCapCycle
import VirtualFinalClosure.MarkerEnd
import VirtualFinalClosure.CapEntry
namespace VirtualFinalClosure.WeightMarker
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","from_d0","route",1),
      ("VirtualFinalClosure.MarkerEnd","VirtualFinalClosure.MarkerEnd","marked_source","markSource",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.scratchStart","frameD0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","old_terminals",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","from_old_row","from_old_row",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong initial W-cap source-marker term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique initial W-cap source-marker term {mod}/{key}"
private theorem weight_step (k m : Nat) (hm : m < 144) (ph : phase m≠2) :
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
/-- The PHASE0 original W-cap is consumed before cleanup, on its ACTUAL
D0 and dirty assignment/banks. Every source cell is physically scanned using
the real remaining-source unary bank0, exactly as on the elln-cap branch. -/
private theorem prepared (k P S L n Q F r : Nat) (f : Fin 4)
    (T : Nat → Option Bool) (bits : Nat → Bool)
    (fr : Frame T S L (L+n+1) Q F) (gap : L+n+1+Q+1 < F)
    (positive : 0 < r) (source : r < S) (fit : F+r+2 ≤ P)
    (bank : ∀ i,F+1 < i → i < F+r+2 → T i=some true)
    (last : T (F+r+2)=none) (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    ∃ d,d ≤ 3+r*(2*r+2*(F-S)+14)+(F-S)+r+7 ∧
      GPath (M:=machine k) P d
        (node (control k (tableControl k (798+93*k)) ⟨8+f.val,by have h:=f.isLt;omega⟩) (F+1) T)
        (C k 40 (modes (8+f.val) bits r) (S-r) (image T F r S r)) ∧
      sourceMode (modes (8+f.val) bits r)=(if bits (r-1) then 1 else 0) ∧
      (seen (modes (8+f.val) bits r)=0 ↔ ∀ i,i < r → bits i=false) := by
  have hm : 8+f.val < 144:=by have h:=f.isLt;omega
  have ph : phase (8+f.val)≠2:=by fin_cases f <;> decide
  have eof : sourceMode (8+f.val)=2:=by fin_cases f <;> decide
  have unseen : seen (8+f.val)=0:=by fin_cases f <;> decide
  have entry:=keep (M:=machine k) (P:=P) (control k (tableControl k (798+93*k)) ⟨8+f.val,hm⟩)
    (nc k 4 (8+f.val)) (F+1) (F+1) T .stay (by omega) (by omega)
    (by rw [frameD0 fr];exact weight_step k (8+f.val) hm ph) rfl
  have front:=route k P F f T (by omega) (frameD0 fr)
  obtain ⟨a,price,path,mode,zero⟩:=markSource k P (8+f.val) S L (L+n+1) Q F r T bits
    hm eof unseen fr gap positive source fit bank last cells
  exact ⟨1+2+a,by omega,joinPath (joinPath entry front) path,mode,zero⟩
#print axioms weight_step
#print axioms prepared
end VirtualFinalClosure.WeightMarker
