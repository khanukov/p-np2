import IngressAllocation.Target
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1
private theorem extend_unique {states N C B : Nat} (h : C ≤ B)
    {small : Config states N C} {large : Config states N B}
    (rel : FixedPairParser.ConfigExtension h small large) : large=extendConfig h small := by
  apply Config.ext_parts
  · exact rel.1.symm
  · exact rel.2.1
  · funext j
    change large.tape j=(if hi : j.val < tapeLength N C then small.tape ⟨j.val,hi⟩ else none)
    split_ifs with hj
    · have index : FixedPairParser.tapeEmbed h (⟨j.val,hj⟩ : Fin (tapeLength N C))=j := Fin.ext rfl
      calc
        large.tape j=large.tape (FixedPairParser.tapeEmbed h (⟨j.val,hj⟩ : Fin (tapeLength N C))) :=
          congrArg large.tape index.symm
        _=small.tape ⟨j.val,hj⟩ := rel.2.2.1 _
    · exact rel.2.2.2 j (by omega)
private theorem trace_of_room (M : UniformTM) {N C B : Nat} (h : C ≤ B) (y : Bitstring N)
    (t : Nat) (room : ∀ u,u < t → (M.run u (initialConfig M C y)).head.val+1 < tapeLength N C) :
    Trace M h y t := by
  intro u hu
  exact FixedPairParser.run_extension M h (FixedPairParser.initialConfig_extension M h y) u
    (fun v hv => room v (by omega))
private theorem append_room (M : UniformTM) {N C : Nat} (c : Config M.stateCount N C)
    (t d : Nat)
    (first : ∀ u,u < t → (M.run u c).head.val+1 < tapeLength N C)
    (tail : ∀ u,u < d → (M.run u (M.run t c)).head.val+1 < tapeLength N C) :
    ∀ u,u < t+d → (M.run u c).head.val+1 < tapeLength N C := by
  intro u hu
  by_cases before : u < t
  · exact first u before
  · rw [show u=t+(u-t) by omega,UniformTM.run_add]
    exact tail (u-t) (by omega)
private theorem move_embed_qualified {N C B : Nat} (h : C ≤ B)
    (i : Fin (tapeLength N C)) (move : Move)
    (room : move=.right → i.val+1 < tapeLength N C) :
    moveHead (FixedPairParser.tapeEmbed h i) move=
      FixedPairParser.tapeEmbed h (moveHead i move) := by
  cases move with
  | left => exact Fin.ext rfl
  | stay => rfl
  | right => exact FixedPairParser.moveHead_tapeEmbed h i .right (room rfl)
private theorem step_extension_qualified (M : UniformTM) {N C B : Nat} (h : C ≤ B)
    {small : Config M.stateCount N C} {large : Config M.stateCount N B}
    (rel : FixedPairParser.ConfigExtension h small large)
    (room : (M.step small.state (small.tape small.head)).2.2=.right → small.head.val+1 < tapeLength N C) :
    FixedPairParser.ConfigExtension h (M.stepConfig small) (M.stepConfig large) := by
  rcases rel with ⟨state,head,low,high⟩
  have read : large.tape large.head=small.tape small.head := by rw [head];exact low _
  have action : M.step large.state (large.tape large.head)=M.step small.state (small.tape small.head) := by rw [← state,read]
  refine ⟨?_,?_,?_,?_⟩
  · change (M.step small.state (small.tape small.head)).1=(M.step large.state (large.tape large.head)).1
    rw [action]
  · change moveHead large.head (M.step large.state (large.tape large.head)).2.2=
      FixedPairParser.tapeEmbed h (moveHead small.head (M.step small.state (small.tape small.head)).2.2)
    rw [action,head]
    exact move_embed_qualified h _ _ room
  · intro i
    change (if FixedPairParser.tapeEmbed h i=large.head then (M.step large.state (large.tape large.head)).2.1
      else large.tape (FixedPairParser.tapeEmbed h i))=(if i=small.head then (M.step small.state (small.tape small.head)).2.1 else small.tape i)
    rw [action]
    by_cases same : i=small.head
    · subst i;rw [if_pos head.symm,if_pos rfl]
    · rw [if_neg same,if_neg (by intro bad;exact same (FixedPairParser.tapeEmbed_injective h (bad.trans head)))]
      exact low i
  · intro j hj
    have different : j ≠ large.head := by
      intro bad
      have eq : j.val=small.head.val := (congrArg Fin.val bad).trans (congrArg Fin.val head)
      exact (Nat.not_lt_of_ge hj) (eq.trans_lt small.head.isLt)
    change (if j=large.head then (M.step large.state (large.tape large.head)).2.1 else large.tape j)=none
    rw [if_neg different]
    exact high j hj
private theorem trace_of_qualified_room (M : UniformTM) {N C B : Nat} (h : C ≤ B)
    (y : Bitstring N) (t : Nat) (room : MoveRoom M (C:=C) y t) : Trace M h y t := by
  intro u hu
  induction u with
  | zero => exact FixedPairParser.initialConfig_extension M h y
  | succ u ih =>
    change FixedPairParser.ConfigExtension h (M.stepConfig (M.run u (initialConfig M C y)))
      (M.stepConfig (M.run u (initialConfig M B y)))
    exact step_extension_qualified M h (ih (by omega)) (room u (by omega))
end IngressAllocation
