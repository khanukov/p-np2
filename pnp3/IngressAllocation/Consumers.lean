import IngressAllocation.RawLift
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("CanonicalLeaf.Body","CanonicalLeaf","row","canonicalRow"),
      ("IngressAllocation.RawLift","IngressAllocation","raw_of_footprints","rawFootprints")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique concrete consumer separation {mod}/{key}: {found.map Prod.fst}"
private def leafState (k : Nat) : Fin (BodyIngress.machine k).stateCount:=
  BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false))
private theorem leaf_val (k : Nat) : (leafState k).val=288+Cursor.stateCount k+6:=by
  rfl
set_option maxRecDepth 4000 in
private theorem leaf_row (k : Nat) (b : Option Bool) :
    (BodyIngress.machine k).step (leafState k) b=(leafState k,b,.stay):=by
  dsimp only [leafState]
  rw [BodyIngress.table_delta,if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change (CanonicalLeaf.result k false).val=(CanonicalLeaf.machine k).stateCount+24 at eq
    have hi:=(CanonicalLeaf.result k false).isLt;omega)]
  rw [CarryWindow.table_delta,if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change 288+Cursor.stateCount k+6=288+(430+93*k)%Cursor.stateCount k at eq
    have hi : 430+93*k < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
    rw [Nat.mod_eq_of_lt hi] at eq;unfold Cursor.stateCount at eq;omega),if_neg (by
    intro h;have eq:=congrArg Fin.val h.1
    change 288+Cursor.stateCount k+6=288+(613+93*k)%Cursor.stateCount k at eq
    have hi : 613+93*k < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
    rw [Nat.mod_eq_of_lt hi] at eq;unfold Cursor.stateCount at eq;omega)]
  have row:=canonicalRow k ⟨6,by decide⟩ b
  change (CanonicalLeaf.machine k).step (CanonicalLeaf.result k false) b=(CanonicalLeaf.result k false,b,.stay) at row
  rw [row]
private theorem leaf_stays {k N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (atLeaf : c.state=leafState k) : ∀ t,((BodyIngress.machine k).run t c).state=leafState k:=by
  intro t
  induction t with
  | zero=>rw [UniformTM.run];exact atLeaf
  | succ t ih=>
    rw [UniformTM.run]
    change ((BodyIngress.machine k).step _ _).1=_
    rw [ih,leaf_row]
private theorem body_disjoint_leaf (k : Nat) (s : Fin SerializedBody.machine.stateCount) :
    BodyIngress.body k s ≠ leafState k:=by
  intro bad
  have eq:=congrArg Fin.val bad
  have small : (leafState k).val < (CarryWindow.machine k).stateCount:=
    (CarryWindow.embed k (CanonicalLeaf.result k false)).isLt
  dsimp only [BodyIngress.body] at eq
  split_ifs at eq
  · change 327=(leafState k).val at eq
    rw [leaf_val] at eq
    unfold Cursor.stateCount at eq
    omega
  · change 328=(leafState k).val at eq
    rw [leaf_val] at eq
    unfold Cursor.stateCount at eq
    omega
  · change (CarryWindow.machine k).stateCount+s.val=(leafState k).val at eq
    omega
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
private theorem consumer_separated {k N B s t : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (leaf : ((BodyIngress.machine k).run s c).state=leafState k)
    (body : ∃ q,((BodyIngress.machine k).run t c).state=BodyIngress.body k q) : False:=by
  by_cases early : s ≤ t
  · have keep:=leaf_stays ((BodyIngress.machine k).run s c) leaf (t-s)
    rw [←UniformTM.run_add,show s+(t-s)=t by omega] at keep
    obtain ⟨q,eq⟩:=body
    exact body_disjoint_leaf k q (eq.symm.trans keep)
  · have keep:=body_closed ((BodyIngress.machine k).run t c) body (s-t)
    rw [←UniformTM.run_add,show t+(s-t)=s by omega] at keep
    obtain ⟨q,eq⟩:=keep
    exact body_disjoint_leaf k q (eq.symm.trans leaf)
set_option maxRecDepth 4000 in
private theorem raw_of_bounded_consumers (k : Nat)
    (bounded : ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
      ∃ t,Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
        (((BodyIngress.machine k).run t
          (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
            BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) ∨
         ∃ mode:Fin 3,((BodyIngress.machine k).run t
          (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
            BodyIngress.body k (SerializedBody.entry mode))) : Target.Raw k:=by
  apply rawFootprints k
  · intro a m x w accepted t arrived first
    obtain ⟨T,heads,atConsumer⟩:=bounded x w accepted
    have bound : t ≤ T:=by
      rcases atConsumer with atLeaf|atBody
      · by_contra later
        exact first T (by omega) false atLeaf
      · exact False.elim (consumer_separated _ arrived (by obtain ⟨mode,eq⟩:=atBody;exact ⟨_,eq⟩))
    intro u hu
    exact heads u (hu.trans bound)
  · intro a m x w accepted t mode arrived first
    obtain ⟨T,heads,atConsumer⟩:=bounded x w accepted
    have bound : t ≤ T:=by
      rcases atConsumer with atLeaf|atBody
      · exact False.elim (consumer_separated _ atLeaf ⟨_,arrived⟩)
      · obtain ⟨selected,eq⟩:=atBody
        by_contra later
        exact first T (by omega) selected eq
    intro u hu
    exact heads u (hu.trans bound)
end IngressAllocation
