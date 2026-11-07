import CarryWindow.Raw
import PostWeight.Raw
namespace CarryReadyCompletion
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let names:=(← getEnv).constants.toList.map Prod.fst
  for (mod,ns,key,localName) in [
    ("VirtualReady.Kernel","VirtualReady","Node","Node"),
    ("VirtualReady.Kernel","VirtualReady","Node.mk","Nodemk"),
    ("VirtualReady.Kernel","VirtualReady","Node.state","Nodestate"),
    ("VirtualReady.Kernel","VirtualReady","Node.head","Nodehead"),
    ("VirtualReady.Kernel","VirtualReady","Node.tape","Nodetape"),
    ("VirtualReady.Kernel","VirtualReady","Path","Path"),
    ("VirtualReady.Kernel","VirtualReady","Path.nil","Pathnil"),
    ("VirtualReady.Kernel","VirtualReady","Path.cons","Pathcons"),
    ("VirtualReady.Kernel","VirtualReady","Edge","Edge"),
    ("VirtualReady.Kernel","VirtualReady","Edge.before","Edgebefore"),
    ("VirtualReady.Kernel","VirtualReady","Edge.after","Edgeafter"),
    ("VirtualReady.Kernel","VirtualReady","Edge.row","Edgerow"),
    ("VirtualReady.Kernel","VirtualReady","Edge.move","Edgemove"),
    ("VirtualReady.Kernel","VirtualReady","Edge.tape","Edgetape"),
    ("VirtualReady.Kernel","VirtualReady","put","put"),
    ("VirtualReady.Kernel","VirtualReady","dest","dest"),
    ("CarryWindow.Body","CarryWindow","code0","code0"),
    ("CarryWindow.Body","CarryWindow","actual_row","actual_row"),
    ("CarryWindow.Body","CarryWindow","shiftCode","shiftCode"),
    ("CarryWindow.Body","CarryWindow","shift_dest","shift_dest"),
    ("CarryWindow.Body","CarryWindow","shift_symbol","shift_symbol"),
    ("CarryWindow.Body","CarryWindow","shift_move","shift_move"),
    ("CarryWindow.Body","CarryWindow","action","action"),
    ("CarryWindow.Body","CarryWindow","checkCodes","checkCodes"),
    ("CarryWindow.Body","CarryWindow","check_get","check_get"),
    ("CarryWindow.Body","CarryWindow","got0","got0"),
    ("CarryWindow.Body","CarryWindow","tag","tag"),
    ("CarryWindow.Body","CarryWindow","tag_lt","tag_lt"),
    ("CarryWindow.Body","CarryWindow","base_dead","base_dead"),
    ("CarryWindow.Body","CarryWindow","deadBase","deadBase"),
    ("CarryWindow.Body","CarryWindow","base_bound","base_bound"),
    ("Cursor.Machine","Cursor","after","cursorAfter")] do
    let found:=names.filter fun n => n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    unless found.length=1 do throwError "Nonunique checked term {localName}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
private def mask (i : Nat) : Nat :=
  if i=613 then 1 else if 430 ≤ i  ∧  i ≤ 552 then
    ([16,96,64,384,192,64,384,256,1536,768,768,256,1536,1024,6144,3072,3072,1024,768,256,192,64,384,192,192,64,384,256,192,64,384,192,192,64,384,256,1536,768,768,256,192,0,0,0,0,0,0,0,0,64,384,256,256,1536,768,256,256,1536,1536,768,256,192,64,384,192,192,64,384,768,256,192,64,48,16,96,48,48,16,96,0,0,0,0,64,384,192,64,384,64,384,384,192,64,384,256,1536,768,768,256,192,192,64,48,16,96,48,48,16,96,64,384,0,0,0,0,256,192,64,48,16,12,4,3] : List Nat)[i-430]! else 0
private def active (i l : Nat) : Bool := (mask i / 2^l)%2==1
private def next (l m : Nat) : List Nat :=
  if m=1 then [l] else if m=0 then
    if l%2=0 then [l-1,l-2] else [l,l-1]
  else if l%2=0 then [l+1,l+2] else [l,l+1]
private def legal (i b c : Nat) : Bool := (List.range 13).all fun l =>
  !active i l || decide ((l%2=0)  ↔  b=0) == false ||
    (c/9==40 || deadBase (c/9) ||
      (decide (c/9 ≠ 430  ∧  c/9 ≠ 613  ∨  c/9=613) &&
       decide ((c/3%3=0)  ↔  b=0) &&
       decide (¬(l=0  ∧  c%3=0)  ∧  ¬(l=12  ∧  c%3=2)) &&
       (next l (c%3)).all (fun d => decide (d ≤ 12) && active (c/9) d)))
private theorem certificate : checkCodes (fun j c => legal (330+j/3) (j%3) c) 0 (cursorAfter 0 0)=true := by decide
private theorem row_certificate (i : Nat) (b : Option Bool) (lo : 330 ≤ i) (hi : i < 937) :
    legal i (tag b) (code0 i b)=true := by
  have h:=check_get (fun j c => legal (330+j/3) (j%3) c) _ 0 certificate _ _ (got0 i b lo hi)
  have small:=tag_lt b
  simpa only [Nat.zero_add,show 330+(3*(i-330)+tag b)/3=i by omega,
    show (3*(i-330)+tag b)%3=tag b by omega] using h
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def Loc (F r n h l : Nat) : Prop :=
  if l%2=0 then h=D F r n (l/2) else D F r n (l/2) < h  ∧  h < D F r n (l/2+1)
private theorem loc_move {F r n h l m : Nat} (hl : l ≤ 12) (hm : m < 3)
    (hloc : Loc F r n h l) (safe : ¬(l=0  ∧  m=0)  ∧  ¬(l=12  ∧  m=2)) :
    ∃ d ∈ next l m, Loc F r n (dest h (if m=0 then .left else if m=1 then .stay else .right)) d := by
  interval_cases l <;> interval_cases m
  all_goals first
    | (exfalso; dsimp only [Loc,D] at hloc; omega)
    | (dsimp only [next]; split_ifs <;> simp only [List.mem_cons,List.not_mem_nil,or_false])
  all_goals simp only [or_and_right,exists_or,exists_eq_left]
  all_goals dsimp [Loc,D,dest] at *
  all_goals omega
private theorem active_limits {i l : Nat} (h : active i l=true) : (430 ≤ i ∧ i ≤ 552) ∨ i=613 := by
  by_cases a : i=613
  · exact Or.inr a
  · by_cases b : 430 ≤ i ∧ i ≤ 552
    · exact Or.inl b
    · simp only [active,mask,if_neg a,if_neg b,Nat.zero_div,Nat.zero_mod] at h
      contradiction
private theorem loc_bounds {F r n h l : Nat} (hl : l ≤ 12) (atLoc : Loc F r n h l) :
    D F r n 0 ≤ h ∧ h ≤ D F r n 6 := by
  interval_cases l <;> dsimp [Loc,D] at * <;> omega
private def Shape (F r n : Nat) (T : Nat → Option Bool) : Prop :=
  ∀ l, l ≤ 12 → ∀ h, Loc F r n h l → (T h=none ↔ l%2=0)
private theorem shape_put {F r n T h w} (shape : Shape F r n T)
    (kind : w=none ↔ T h=none) : Shape F r n (put T h w) := by
  intro l hl i loc
  by_cases eq : i=h
  · subst i; simpa only [put,if_pos rfl] using kind.trans (shape l hl h loc)
  · simpa only [put,if_neg eq] using shape l hl i loc
private theorem tag_none (b : Option Bool) : tag b=0 ↔ b=none := by
  cases b with | none => decide | some v => cases v <;> decide
private theorem certified {i l : Nat} (b : Option Bool) (il : 330 ≤ i) (iu : i < 937)
    (hl : l ≤ 12) (live : active i l=true) (kind : l%2=0 ↔ b=none) :
    code0 i b/9=40 ∨ deadBase (code0 i b/9)=true ∨
      (code0 i b/9≠430 ∧ ((code0 i b/3%3=0) ↔ b=none) ∧
        (¬(l=0 ∧ code0 i b%3=0) ∧ ¬(l=12 ∧ code0 i b%3=2)) ∧
        ∀ d ∈ next l (code0 i b%3), d ≤ 12 ∧ active (code0 i b/9) d=true) := by
  have certAll:=row_certificate i b il iu
  dsimp only [legal] at certAll
  have one:=List.all_eq_true.mp certAll l (List.mem_range.mpr (by omega))
  have same : (l%2=0 ↔ tag b=0) := kind.trans (tag_none b).symm
  simp only [live,Bool.not_true,Bool.false_or,decide_eq_true same,Bool.true_eq_false,
    Bool.or_eq_true,false_or,beq_iff_eq,Bool.and_eq_true,decide_eq_true_eq] at one
  rcases one with (h | h) | ⟨⟨⟨neq,wr⟩,mv⟩,targets⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨by omega,wr.trans (tag_none b),mv,?_⟩)
    intro d hd
    have item:=List.all_eq_true.mp targets d hd
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using item
private def Dead (k : Nat) (s : Fin (Cursor.stateCount k)) : Prop :=
  s=Cursor.q k 40 ∨ ∃ i, deadBase i=true ∧ s=Cursor.q k (i+93*k)
private theorem q_inj {k i j : Nat} (hi : i < Cursor.stateCount k) (hj : j < Cursor.stateCount k)
    (eq : Cursor.q k i=Cursor.q k j) : i=j := by
  have h:=congrArg Fin.val eq
  change i%Cursor.stateCount k=j%Cursor.stateCount k at h
  simpa only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using h
private theorem dead_step {k : Nat} (s : Fin (Cursor.stateCount k)) (b : Option Bool)
    (dead : Dead k s) : Dead k ((Cursor.machine k).step s b).1 := by
  rcases dead with eq | ⟨i,di,eq⟩
  · rw [eq]; change Dead k ((Cursor.machine k).step (Cursor.machine k).reject b).1
    rw [UniformTM.step_reject]; exact Or.inl rfl
  · have limits : 330 ≤ i ∧ i < 937 := by
      dsimp only [deadBase] at di; have h:=of_decide_eq_true di; omega
    rw [eq,actual_row k i b limits.1 limits.2]
    dsimp only [action]; rw [shift_dest]
    rcases base_dead i b limits.1 limits.2 di with reject | nextDead
    · rw [if_pos reject]; exact Or.inl rfl
    · have nb:=base_bound i b limits.1 limits.2
      have ne : code0 i b/9≠40 := by
        dsimp only [deadBase] at nextDead
        have h:=of_decide_eq_true nextDead; omega
      rw [if_neg ne]; exact Or.inr ⟨_,nextDead,rfl⟩
private theorem path_dead {k P t c d} (p : Path k P t c d) (dead : Dead k (Nodestate c)) :
    Dead k (Nodestate d) := by
  induction p with
  | nil => exact dead
  | cons edge rest ih =>
    apply ih
    rw [← Edgerow edge]
    exact dead_step _ _ dead
private theorem not_dead613 (k : Nat) : ¬Dead k (Cursor.q k (613+93*k)) := by
  rintro (eq | ⟨i,di,eq⟩)
  · have :=q_inj (by unfold Cursor.stateCount; omega) (by unfold Cursor.stateCount; omega) eq
    omega
  · have li : 330 ≤ i ∧ i < 937 ∧ i≠613 := by
      dsimp only [deadBase] at di; have h:=of_decide_eq_true di; omega
    have :=q_inj (by unfold Cursor.stateCount; omega) (by unfold Cursor.stateCount; omega) eq
    omega
private def Good (k F r n : Nat) (c : Node k) : Prop :=
  ∃ i l, 330 ≤ i ∧ i < 937 ∧ Nodestate c=Cursor.q k (i+93*k) ∧
    l ≤ 12 ∧ active i l=true ∧ Loc F r n (Nodehead c) l ∧ Shape F r n (Nodetape c)
private theorem good_edge {k P F r n c d} (e : Edge k P c d) (good : Good k F r n c) :
    Dead k (Nodestate d) ∨ (Good k F r n d ∧ Nodestate d≠Cursor.q k (430+93*k)) := by
  obtain ⟨i,l,il,iu,st,hl,live,loc,shape⟩:=good
  have row:=Edgerow e
  rw [st,actual_row k i _ il iu] at row
  have kind := (shape l hl _ loc).symm
  rcases certified (Nodetape c (Nodehead c)) il iu hl live kind with reject | dead | ⟨not430,wr,mv,targets⟩
  · left; rw [← row]; dsimp only [action]; rw [shift_dest,if_pos reject]; exact Or.inl rfl
  · left; rw [← row]; dsimp only [action]; rw [shift_dest]
    have lim : code0 i (Nodetape c (Nodehead c))/9≠40 := by
      dsimp only [deadBase] at dead; have h:=of_decide_eq_true dead; omega
    rw [if_neg lim]; exact Or.inr ⟨_,dead,rfl⟩
  · obtain ⟨dloc,mem,here⟩:=loc_move hl (Nat.mod_lt _ (by decide : 0<3)) loc mv
    have target:=targets dloc mem
    have dst : code0 i (Nodetape c (Nodehead c))/9≠40 := by
      intro eq
      rw [eq] at target
      have bad:=active_limits target.2; omega
    have rwMove : (Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c)) |>.2.2 =
        if code0 i (Nodetape c (Nodehead c))%3=0 then .left else
        if code0 i (Nodetape c (Nodehead c))%3=1 then .stay else .right := by
      rw [st,actual_row k i _ il iu]; dsimp only [action]; rw [shift_move]
    have ds : Nodestate d=Cursor.q k (code0 i (Nodetape c (Nodehead c))/9+93*k) := by
      rw [← row]; dsimp only [action]; rw [shift_dest,if_neg dst]
    have newLoc : Loc F r n (Nodehead d) dloc := by
      rw [← Edgemove e,rwMove]; exact here
    have writeKind : (Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c)) |>.2.1 = none ↔
        Nodetape c (Nodehead c)=none := by
      rw [st,actual_row k i _ il iu]; dsimp only [action]; rw [shift_symbol]
      split_ifs <;> simp_all
    have shapeD : Shape F r n (Nodetape d) := by
      rw [Edgetape e]; exact shape_put shape writeKind
    refine Or.inr ⟨⟨_,dloc,?_,?_,ds,target.1,target.2,newLoc,shapeD⟩,?_⟩
    · have lim:=active_limits target.2; omega
    · exact base_bound i _ il iu
    · intro eq; rw [ds] at eq
      have eq:=q_inj (by have h:=base_bound i (Nodetape c (Nodehead c)) il iu; unfold Cursor.stateCount; omega)
        (by unfold Cursor.stateCount; omega) eq
      omega

end CarryReadyCompletion
