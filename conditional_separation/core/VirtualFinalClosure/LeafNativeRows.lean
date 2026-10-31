import VirtualFinalClosure.LeafWideRows
namespace VirtualFinalClosure.LeafNativeRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full","full",(0:Nat)),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full_value","fullValue",1),
      ("VirtualFinalClosure.LeafWideRows","VirtualFinalClosure.LeafWideRows","effective","effective",1),
      ("VirtualFinalClosure.LeafWideRows","VirtualFinalClosure.LeafWideRows","reject_row","rejectRow",1),
      ("CanonicalLeaf.Body","CanonicalLeaf","row","canonicalRow",1),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","originalEntryValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual canonical-five native row {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual canonical-five native row {mod}/{key}"

private def E (k : Nat) (m : Fin 144) (j : Fin 8) : Fin (machine k).stateCount:=
  control k (full k (VirtualLeaf.extra k j)) m
private def ready (k : Nat) (m : Fin 144) : Fin (machine k).stateCount:=
  control k (tableControl k (936+93*k)) m
private def result (k : Nat) (m : Fin 144) (b : Bool) : Fin (machine k).stateCount:=
  control k (leafControl k b) m
private def E_type : ∀ k,Fin 144 → Fin 8 → Fin (machine k).stateCount:=E
private def ready_type : ∀ k,Fin 144 → Fin (machine k).stateCount:=ready
private def result_type : ∀ k,Fin 144 → Bool → Fin (machine k).stateCount:=result
private theorem extra_value (k : Nat) (j : Fin 8) :
    (VirtualLeaf.extra k j).val=288+Cursor.stateCount k+j.val:=rfl
private theorem entry_value (k : Nat) : (CanonicalLeaf.entry k).val=1224+93*k:=by
  dsimp only [CanonicalLeaf.entry,VirtualLeaf.embed]
  exact originalEntryValue k
private theorem entry_pin (k : Nat) : full k (CanonicalLeaf.entry k)=tableControl k (936+93*k):=by
  apply Fin.ext
  rw [fullValue,entry_value,tableValue k _ (by unfold Cursor.stateCount;omega)]
  omega
private theorem result_pin (k : Nat) (b : Bool) : full k (CanonicalLeaf.result k b)=leafControl k b:=by
  apply Fin.ext
  rw [fullValue,leafValue]
  change 87+(288+Cursor.stateCount k+(if b then 7 else 6))=375+Cursor.stateCount k+(if b=true then 7 else 6)
  cases b <;> omega
private theorem extra_fit (k : Nat) (j : Fin 8) (hj : j.val<6) :
    1224+93*k ≤ (VirtualLeaf.extra k j).val ∧ (VirtualLeaf.extra k j).val<288+Cursor.stateCount k+6:=by
  rw [extra_value]
  unfold Cursor.stateCount
  omega
private theorem entry_row (k : Nat) (m : Fin 144) :
    (machine k).step (ready k m) none=(E k m ⟨0,by decide⟩,none,.stay):=by
  have old : (CanonicalLeaf.machine k).step (CanonicalLeaf.entry k) none=
      (VirtualLeaf.extra k ⟨0,by decide⟩,none,.stay):=by
    change (CanonicalLeaf.machine k).step (VirtualLeaf.embed k (VirtualLeaf.entry k)) none=_
    rw [CanonicalLeaf.repaired_rows,if_pos ⟨rfl,rfl⟩]
  have a:=effective k (CanonicalLeaf.entry k) m none (by rw [entry_value])
    (by rw [entry_value];unfold Cursor.stateCount;omega)
    (by rw [old];exact (extra_fit k _ (by decide)).1)
  rw [old,entry_pin] at a
  exact a
private theorem work_row (k : Nat) (m : Fin 144) (j j' : Fin 8) (b w : Option Bool) (mv : Move)
    (small : j.val<6) (after : 1224+93*k ≤ (VirtualLeaf.extra k j').val)
    (old : (CanonicalLeaf.machine k).step (VirtualLeaf.extra k j) b=(VirtualLeaf.extra k j',w,mv)) :
    (machine k).step (E k m j) b=(E k m j',w,mv):=by
  have a:=effective k (VirtualLeaf.extra k j) m b (extra_fit k j small).1 (extra_fit k j small).2
    (by rw [old];exact after)
  rwa [old] at a
private theorem rows (k : Nat) (m : Fin 144) :
    (machine k).step (E k m ⟨0,by decide⟩) none=(E k m ⟨1,by decide⟩,none,.stay) ∧
    (machine k).step (E k m ⟨1,by decide⟩) none=(E k m ⟨2,by decide⟩,none,.left) ∧
    (∀ b : Bool,(machine k).step (E k m ⟨2,by decide⟩) (some b)=
      (E k m ⟨if b then 5 else 4,by cases b <;> decide⟩,some b,.right)) ∧
    (machine k).step (E k m ⟨2,by decide⟩) none=(E k m ⟨3,by decide⟩,none,.right):=by
  refine ⟨?_,?_,?_,?_⟩
  · exact work_row k m _ _ _ _ _ (by decide) (extra_fit k _ (by decide)).1 (by rw [canonicalRow])
  · exact work_row k m _ _ _ _ _ (by decide) (extra_fit k _ (by decide)).1 (by rw [canonicalRow])
  · intro b
    exact work_row k m _ _ _ _ _ (by decide) (extra_fit k _ (by cases b <;> decide)).1 (by rw [canonicalRow])
  · exact work_row k m _ _ _ _ _ (by decide) (extra_fit k _ (by decide)).1 (by rw [canonicalRow])
private theorem write_row (k : Nat) (m : Fin 144) (b : Bool) :
    (machine k).step (E k m ⟨if b then 5 else 4,by cases b <;> decide⟩) none=
      (result k m b,some b,.stay):=by
  let j : Fin 8:=⟨if b then 5 else 4,by cases b <;> decide⟩
  have old : (CanonicalLeaf.machine k).step (VirtualLeaf.extra k j) none=(CanonicalLeaf.result k b,some b,.stay):=by
    cases b <;> rw [canonicalRow] <;> rfl
  have a:=effective k (VirtualLeaf.extra k j) m none
    (extra_fit k j (by dsimp only [j];cases b <;> decide)).1
    (extra_fit k j (by dsimp only [j];cases b <;> decide)).2
    (by rw [old];change 1224+93*k ≤ 288+Cursor.stateCount k+(if b then 7 else 6);unfold Cursor.stateCount;cases b <;> omega)
  rw [old,result_pin] at a
  exact a
private theorem reject_row (k : Nat) (m : Fin 144) :
    (machine k).step (E k m ⟨3,by decide⟩) none=((machine k).reject,none,.stay):=by
  exact rejectRow k (VirtualLeaf.extra k ⟨3,by decide⟩) m none none .stay
    (extra_fit k _ (by decide)).1 (extra_fit k _ (by decide)).2 (by rw [canonicalRow])
#print axioms E_type
#print axioms ready_type
#print axioms result_type
#print axioms extra_value
#print axioms entry_value
#print axioms entry_pin
#print axioms result_pin
#print axioms extra_fit
#print axioms entry_row
#print axioms work_row
#print axioms rows
#print axioms write_row
#print axioms reject_row
end VirtualFinalClosure.LeafNativeRows
