import TotalIngressClosure.Machine
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let found:=(←getEnv).constants.toList.filter fun (n,_)=>
    n.toString.startsWith "_private.CanonicalLeaf.Body." && n.toString.endsWith ".CanonicalLeaf.row"
  match found with
  | [(n,.thmInfo ci)]=>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `canonicalRow n::st.openDecls}
  | _=>throwError "Nonunique literal work-result absorption {found.map Prod.fst}"
private def leafState (k : Nat) (v:Bool) : Fin (BodyIngress.machine k).stateCount:=
  BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k v))
private theorem leaf_val (k : Nat) (v:Bool) : (leafState k v).val=288+Cursor.stateCount k+(if v then 7 else 6):=by
  cases v <;> rfl
set_option maxRecDepth 4000 in
private theorem leaf_row (k : Nat) (v:Bool) (b : Option Bool) :
    (BodyIngress.machine k).step (leafState k v) b=(leafState k v,b,.stay):=by
  dsimp only [leafState]
  rw [BodyIngress.table_delta,if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change (CanonicalLeaf.result k v).val=(CanonicalLeaf.machine k).stateCount+24 at eq
    have hi:=(CanonicalLeaf.result k v).isLt;omega)]
  rw [CarryWindow.table_delta,if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change 288+Cursor.stateCount k+(if v then 7 else 6)=288+(430+93*k)%Cursor.stateCount k at eq
    have hi : 430+93*k < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
    rw [Nat.mod_eq_of_lt hi] at eq;unfold Cursor.stateCount at eq;omega),if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change 288+Cursor.stateCount k+(if v then 7 else 6)=288+(613+93*k)%Cursor.stateCount k at eq
    have hi : 613+93*k < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
    rw [Nat.mod_eq_of_lt hi] at eq;unfold Cursor.stateCount at eq;omega)]
  have row:(CanonicalLeaf.machine k).step (CanonicalLeaf.result k v) b=(CanonicalLeaf.result k v,b,.stay):=by
    cases v
    · exact canonicalRow k ⟨6,by decide⟩ b
    · exact canonicalRow k ⟨7,by decide⟩ b
  rw [row]
private theorem leaf_stays {k N B : Nat} (v:Bool) (c : Config (BodyIngress.machine k).stateCount N B)
    (atLeaf : c.state=leafState k v) : ∀ t,((BodyIngress.machine k).run t c).state=leafState k v:=by
  intro t
  induction t with
  | zero=>rw [UniformTM.run];exact atLeaf
  | succ t ih=>
    rw [UniformTM.run]
    change ((BodyIngress.machine k).step _ _).1=_
    rw [ih,leaf_row k v]
private theorem body_disjoint_leaf (k : Nat) (v:Bool) (s : Fin SerializedBody.machine.stateCount) :
    BodyIngress.body k s ≠ leafState k v:=by
  intro bad
  have eq:=congrArg Fin.val bad
  have small : (leafState k v).val < (CarryWindow.machine k).stateCount:=
    (CarryWindow.embed k (CanonicalLeaf.result k v)).isLt
  dsimp only [BodyIngress.body] at eq
  split_ifs at eq
  · change 327=(leafState k v).val at eq
    rw [leaf_val k v] at eq
    unfold Cursor.stateCount at eq
    omega
  · change 328=(leafState k v).val at eq
    rw [leaf_val k v] at eq
    unfold Cursor.stateCount at eq
    omega
  · change (CarryWindow.machine k).stateCount+s.val=(leafState k v).val at eq
    omega
set_option maxRecDepth 4000 in
private theorem old_entry_disjoint (k : Nat) (q:Fin (CarryWindow.machine k).stateCount) (mode:Fin 3) :
    BodyIngress.old k q≠BodyIngress.body k (SerializedBody.entry mode):=by
  exact (BodyIngress.embeddings k).2.2.2.2.2.2 q mode

private theorem body_closed {k N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (inside : ∃ q,c.state=BodyIngress.body k q) :
    ∀ t,∃ q,((BodyIngress.machine k).run t c).state=BodyIngress.body k q:=by
  intro t
  induction t with
  | zero=>rw [UniformTM.run];exact inside
  | succ t ih=>
    obtain ⟨q,eq⟩:=ih
    rw [UniformTM.run]
    change ∃ q,((BodyIngress.machine k).step _ _).1=BodyIngress.body k q
    rw [eq,BodyIngress.body_rows]
    exact ⟨_,rfl⟩
private theorem consumer_separated {k N B s t : Nat} (v:Bool) (c : Config (BodyIngress.machine k).stateCount N B)
    (leaf : ((BodyIngress.machine k).run s c).state=leafState k v)
    (body : ∃ q,((BodyIngress.machine k).run t c).state=BodyIngress.body k q) : False:=by
  by_cases early : s ≤ t
  · have keep:=leaf_stays v ((BodyIngress.machine k).run s c) leaf (t-s)
    rw [←UniformTM.run_add,show s+(t-s)=t by omega] at keep
    obtain ⟨q,eq⟩:=body
    exact body_disjoint_leaf k v q (eq.symm.trans keep)
  · have keep:=body_closed ((BodyIngress.machine k).run t c) body (s-t)
    rw [←UniformTM.run_add,show t+(s-t)=s by omega] at keep
    obtain ⟨q,eq⟩:=keep
    exact body_disjoint_leaf k v q (eq.symm.trans leaf)

end TotalIngressClosure
