import VirtualFinalClosure.LeafComponent
import VirtualFinalClosure.FirstCutCore
namespace VirtualFinalClosure.BodyTrapRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","total_row","totalRow",(1:Nat)),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","certificate_row","certificateRow",1),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong immutable BODY trap interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique immutable BODY trap interface {mod}/{key}"
private def full (k : Nat) (s : Fin SerializedBody.machine.stateCount) : Fin (CertificateGuardClosure.machine k).stateCount:=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k s))
private def full_type : ∀ k,Fin SerializedBody.machine.stateCount → Fin (CertificateGuardClosure.machine k).stateCount:=full
private theorem full_value (k : Nat) (s : Fin SerializedBody.machine.stateCount) (s0 : s.val≠0) (s1 : s.val≠1) :
    (full k s).val=87+(CarryWindow.machine k).stateCount+s.val:=by
  dsimp only [full,CertificateGuardClosure.old,TotalIngressClosure.old,BodyIngress.body,UniformTM.seqRight]
  rw [if_neg s0,if_neg s1]
  change 10+(67+(10+((CarryWindow.machine k).stateCount+s.val)))=87+(CarryWindow.machine k).stateCount+s.val
  omega
private theorem carry_large (k : Nat) : Cursor.stateCount k+320 ≤ (CarryWindow.machine k).stateCount:=by
  change Cursor.stateCount k+320 ≤ 288+Cursor.stateCount k+8+25
  omega
private theorem term_pin (k : Nat) : full k SerializedBody.machine.accept=(CertificateGuardClosure.machine k).accept ∧
    full k SerializedBody.machine.reject=(CertificateGuardClosure.machine k).reject:=by
  constructor <;> apply Fin.ext
  · change 10+(67+(10+327))=414
    omega
  · change 10+(67+(10+328))=415
    omega
private theorem component (k : Nat) (s : Fin SerializedBody.machine.stateCount) (b : Option Bool) :
    (CertificateGuardClosure.machine k).step (full k s) b=
      (full k (SerializedBody.machine.step s b).1,(SerializedBody.machine.step s b).2):=by
  dsimp only [full]
  rw [certificateRow,totalRow,BodyIngress.body_rows]
/-- Every actual BODY edge remains a BODY edge under the candidate, with a
possibly normalized finite metadata word. This is a table fact, not an assumed
prepared evaluator or a claim about its source semantics. -/
private theorem old_row (k : Nat) (s : Fin SerializedBody.machine.stateCount) (m : Fin 144) (b : Option Bool)
    (s0 : s.val≠0) (s1 : s.val≠1) :
    oldRow k (full k s).val m.val b=
      ((full k (SerializedBody.machine.step s b).1).val,
        (if ∃ j,full k (SerializedBody.machine.step s b).1=bodyControl k j then 8 else m.val),
        (SerializedBody.machine.step s b).2):=by
  let O:=CertificateGuardClosure.machine k
  let q:=full k s
  have large:=carry_large k
  have hs : (⟨q.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  have noTable (i : Nat) (fit : i < Cursor.stateCount k) : q≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    change (full k s).val=(tableControl k i).val at h
    rw [full_value k s s0 s1,tableValue k i fit] at h
    omega
  have noLeaf (v : Bool) : q≠leafControl k v:=by
    intro e;have h:=congrArg Fin.val e
    change (full k s).val=(leafControl k v).val at h
    rw [full_value k s s0 s1,leafValue] at h
    cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  dsimp only [oldRow]
  rw [hs,if_neg (fun h=>h.elim (noLeaf false) (noLeaf true))]
  rw [if_neg (by intro h;rcases h.2.2 with h|h;exact noTable 250 (by unfold Cursor.stateCount;omega) h;exact noTable 304 (by unfold Cursor.stateCount;omega) h)]
  rw [if_neg (fun h=>noTable (798+93*k) (by unfold Cursor.stateCount;omega) h.2.2)]
  rw [if_neg (fun h=>noTable (430+93*k) (by unfold Cursor.stateCount;omega) h.2)]
  rw [if_neg (fun h=>noTable (613+93*k) (by unfold Cursor.stateCount;omega) h.2.2)]
  rw [component]
  dsimp only
  by_cases entry : ∃ j,full k (SerializedBody.machine.step s b).1=bodyControl k j
  · rw [if_pos entry,if_pos entry]
    rfl
  · rw [if_neg entry,if_neg entry]
    rw [if_neg (fun h=>noTable 43 (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noTable 47 (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noTable 51 (by unfold Cursor.stateCount;omega) h.2)]
private theorem effective (k : Nat) (s : Fin SerializedBody.machine.stateCount) (m : Fin 144) (b : Option Bool)
    (s0 : s.val≠0) (s1 : s.val≠1) :
    ∃ mm : Fin 144,(machine k).step (control k (full k s) m) b=
      (control k (full k (SerializedBody.machine.step s b).1) mm,(SerializedBody.machine.step s b).2) ∧
      (((full k (SerializedBody.machine.step s b).1)=(CertificateGuardClosure.machine k).accept ∨
        (full k (SerializedBody.machine.step s b).1)=(CertificateGuardClosure.machine k).reject) → mm.val=8):=by
  let O:=CertificateGuardClosure.machine k
  have large:=carry_large k
  have noTerm (v : Bool) : full k s≠(if v then O.accept else O.reject):=by
    intro e;have h:=congrArg Fin.val e
    cases v
    · rw [if_neg (by decide),full_value k s s0 s1,(oldTerminals k).2] at h
      unfold Cursor.stateCount at large
      omega
    · rw [if_pos rfl,full_value k s s0 s1,(oldTerminals k).1] at h
      unfold Cursor.stateCount at large
      omega
  rw [wire k (full k s) m.val b m.isLt (noTerm true) (noTerm false),old_row k s m b s0 s1]
  dsimp only
  let a:=full k (SerializedBody.machine.step s b).1
  by_cases terminal : a=O.accept ∨ a=O.reject
  · rw [if_pos (by rcases terminal with h|h;exact Or.inl (congrArg Fin.val h);exact Or.inr (congrArg Fin.val h))]
    exact ⟨⟨8,by decide⟩,rfl,by intro _;rfl⟩
  · rw [if_neg (by intro h;apply terminal;rcases h with h|h;exact Or.inl (Fin.ext h);exact Or.inr (Fin.ext h))]
    let mm : Fin 144:=⟨if ∃ j,a=bodyControl k j then 8 else m.val,by split_ifs <;> first | decide | exact m.isLt⟩
    exact ⟨mm,rfl,by intro h;exact (terminal h).elim⟩
#print axioms full_type
#print axioms full_value
#print axioms carry_large
#print axioms term_pin
#print axioms component
#print axioms old_row
#print axioms effective
end VirtualFinalClosure.BodyTrapRows
