import CarryReadyCompletion.Surface
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
    ("Cursor.Machine","Cursor","after","cursorAfter"),
    ("VirtualLeaf.Body","VirtualLeaf","Trace","Tr"),
    ("VirtualReady.Kernel","VirtualReady","Path.bounds","pathBounds")] do
    let found:=names.filter fun n => n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    unless found.length=1 do throwError "Nonunique checked term {localName}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
run_cmd do
  let names:=(← getEnv).constants.toList.map Prod.fst
  for key in ["D","Loc","loc_move","active_limits","loc_bounds","Shape","shape_put","Dead","q_inj","dead_step","path_dead","not_dead613","Good","good_edge","active","mask"] do
    let found:=names.filter fun n => n.toString.startsWith "_private.CarryReadyCompletion.Surface." && n.toString.endsWith (".CarryReadyCompletion."++key)
    unless found.length=1 do throwError "Nonunique local foundation {key}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous key) found.head! :: st.openDecls}
private theorem good_tail {k P F r n t c d e} (edge : Edge k P c d) (path : Path k P t d e)
    (good : Good k F r n c) (last : Nodestate e=Cursor.q k (613+93*k)) :
    Good k F r n d    ∧    Nodestate d   ≠   Cursor.q k (430+93*k) := by
  rcases good_edge edge good with dead | live
  · exact False.elim (not_dead613 k (last ▸ path_dead path dead))
  · exact live
private theorem shape_of_banks {F r n T}
    (blank : ∀ j, j   ≤   6    →    T (D F r n j)=none)
    (occupied : ∀ j, j   <   6    →    ∀ i, D F r n j   <   i    →    i   <   D F r n (j+1)    →    ∃ b, T i=some b) :
    Shape F r n T := by
  intro l hl h loc
  interval_cases l
  all_goals dsimp [Loc] at loc
  all_goals first
    | (subst h; rw [blank _ (by decide)]; decide)
    | (obtain ⟨b,eq⟩:=occupied _ (by decide) h loc.1 loc.2; rw [eq]; cases b <;> decide)
private def cq (k : Nat) (s : Fin (Cursor.stateCount k)) : Fin (CanonicalLeaf.machine k).stateCount :=
  VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) s)
private def mapped (k : Nat) (s : Fin (Cursor.stateCount k)) : Fin (CarryWindow.machine k).stateCount :=
  if s=Cursor.q k (430+93*k) then CarryWindow.extra k 23 else CarryWindow.embed k (cq k s)
private theorem cq_val {k i : Nat} (hi : i   <   Cursor.stateCount k) : (cq k (Cursor.q k i)).val=288+i := by
  change 288+i%Cursor.stateCount k=288+i
  rw [Nat.mod_eq_of_lt hi]
private theorem canonical_row (k i : Nat) (b : Option Bool) (hi : i   <   Cursor.stateCount k) (ne : i   ≠   936+93*k) :
    (CanonicalLeaf.machine k).step (cq k (Cursor.q k i)) b=
      (cq k ((Cursor.machine k).step (Cursor.q k i) b).1,((Cursor.machine k).step (Cursor.q k i) b).2) := by
  dsimp only [cq]
  rw [CanonicalLeaf.repaired_rows,if_neg (by
    intro h; have e:=congrArg Fin.val h.1
    fromDonor "VirtualLeaf.Transport" "VirtualLeaf" "entry_val" => rw [OLD] at e
    change 288+i%Cursor.stateCount k=1224+93*k at e
    rw [Nat.mod_eq_of_lt hi] at e; omega)]
  change (VirtualLeaf.embed k ((IngressRepair.producer.seq (Cursor.machine k)).step
    (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i)) b).1,
    ((IngressRepair.producer.seq (Cursor.machine k)).step
    (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i)) b).2)=_
  rw [UniformTM.seq_step_right]
private theorem mapped_row {k i b} (range : 430   ≤   i    ∧    i   ≤   552) (at430 : i=430    →    b=none)
    (not430 : ((Cursor.machine k).step (Cursor.q k (i+93*k)) b).1   ≠   Cursor.q k (430+93*k)) :
    (CarryWindow.machine k).step (mapped k (Cursor.q k (i+93*k))) b=
      (mapped k ((Cursor.machine k).step (Cursor.q k (i+93*k)) b).1,
        ((Cursor.machine k).step (Cursor.q k (i+93*k)) b).2) := by
  have hi : i+93*k   <   Cursor.stateCount k := by unfold Cursor.stateCount; omega
  have neq (j : Nat) (bound : j+93*k   <   Cursor.stateCount k) (ne : i   ≠   j) :
      cq k (Cursor.q k (i+93*k))   ≠   cq k (Cursor.q k (j+93*k)) := by
    intro bad; have h:=congrArg Fin.val bad
    rw [cq_val hi,cq_val bound] at h; omega
  dsimp only [mapped]; rw [if_neg not430]
  by_cases same : i=430
  · subst i; rw [at430 rfl,if_pos rfl]
    fromDonor "CarryWindow.Rows" "CarryWindow" "native_row" => rw [OLD]
    fromDonor "CarryWindow.Machine" "CarryWindow" "native" => dsimp only [OLD]
    fromDonor "CarryWindow.Machine" "CarryWindow" "liftAction" => dsimp only [OLD]
    fromDonor "CarryWindow.Machine" "CarryWindow" "oldq" => dsimp only [OLD]
    change (CarryWindow.embed k ((CanonicalLeaf.machine k).step (cq k (Cursor.q k (430+93*k))) none).1,
      ((CanonicalLeaf.machine k).step (cq k (Cursor.q k (430+93*k))) none).2)=_
    rw [canonical_row k _ none hi (by omega)]
  · rw [if_neg (by intro h; have e:=q_inj hi (by unfold Cursor.stateCount; omega) h; omega),CarryWindow.table_delta]
    rw [if_neg (by exact fun h => neq 430 (by unfold Cursor.stateCount; omega) same h.1),
      if_neg (by exact fun h => neq 613 (by unfold Cursor.stateCount; omega) (by omega) h.1),
      canonical_row k _ b hi (by omega)]
private def splice (T U : Nat    →    Option Bool) (F : Nat) : Nat    →    Option Bool :=
  fun i => if i   <   F+1 then T i else U i
private theorem splice_put (T U : Nat    →    Option Bool) (F h : Nat) (w : Option Bool) (lo : F+1   ≤   h) :
    splice T (put U h w) F=put (splice T U F) h w := by
  funext i; dsimp only [splice,put]; split_ifs <;> first | rfl | (exfalso; omega)
private def lifted {k N B : Nat} (T : Nat    →    Option Bool) (F : Nat) (c : Node k)
    (fit : Nodehead c   <   tapeLength N B) : Config (CarryWindow.machine k).stateCount N B :=
  ⟨mapped k (Nodestate c),⟨Nodehead c,fit⟩,fun i => splice T (Nodetape c) F i.val⟩
private theorem first613_edge {k P F r n t c d e} (edge : Edge k P c d) (path : Path k P t d e)
    (_good : Good k F r n c) (last : Nodestate e=Cursor.q k (613+93*k)) :
    Nodestate c   ≠   Cursor.q k (613+93*k) := by
  intro bad
  have dead : Dead k (Nodestate d) := by
    rw [← Edgerow edge,bad,actual_row k 613 _ (by decide) (by decide)]
    have v : ∀ b, code0 613 b/9=614 := by intro b; cases b with | none => decide | some b => cases b <;> decide
    dsimp only [action]; rw [shift_dest,v,if_neg (by decide)]
    exact Or.inr ⟨614,by decide,rfl⟩
  exact not_dead613 k (last ▸ path_dead path dead)
private theorem path_lift {k P F r n t c d N B} (T : Nat    →    Option Bool)
    (path : Path k P t c d) (good : Good k F r n c) (last : Nodestate d=Cursor.q k (613+93*k))
    (fit : P   <   tapeLength N B) (pbound : P=D F r n 6) :
    Tr (CarryWindow.machine k) (D F r n 0) (D F r n 6) t
      (lifted (N:=N) (B:=B) T F c (lt_of_le_of_lt (pathBounds path).1 fit))
      (lifted (N:=N) (B:=B) T F d (lt_of_le_of_lt (pathBounds path).2 fit)) := by
  induction path with
  | nil c hp =>
    obtain ⟨i,l,_,_,_,hl,_,loc,_⟩:=good
    have bounds:=loc_bounds hl loc
    fromDonor "VirtualLeaf.Body" "VirtualLeaf" "nil" => exact OLD _ ⟨bounds.1,bounds.2⟩
  | @cons t c d e edge rest ih =>
    have nextGood:=good_tail edge rest good last
    have beforeNot:=first613_edge edge rest good last
    obtain ⟨i,l,il,iu,st,hl,live,loc,shape⟩:=good
    have range : 430   ≤   i    ∧    i   ≤   552 := by
      rcases active_limits live with h | h
      · exact h
      · exfalso; apply beforeNot; rw [st,h]
    have afterBounds : D F r n 0   ≤   Nodehead d    ∧    Nodehead d   ≤   D F r n 6 := by
      obtain ⟨_,ll,_,_,_,hll,_,lc,_⟩:=nextGood.1; exact loc_bounds hll lc
    have beforeBounds:=loc_bounds hl loc
    have row:=mapped_row range (by
      intro e; subst i
      have four : l=4 := by
        have hh : active 430 l=true := live
        interval_cases l <;> norm_num [active,mask] at live ⊢
      exact (shape l hl _ loc).mpr (by omega))
      (by rw [← st,Edgerow edge]; exact nextGood.2)
    rw [← st] at row
    have read : splice T (Nodetape c) F (Nodehead c)=Nodetape c (Nodehead c) := by
      dsimp only [splice]; rw [if_neg (by dsimp only [D] at beforeBounds; omega)]
    fromDonor "CarryWindow.Geometry" "CarryWindow" "hop" =>
      have one:=OLD (M:=CarryWindow.machine k) (N:=N) (B:=B) (lo:=D F r n 0)
        (by rw [← pbound]; exact fit) (mapped k (Nodestate c)) (mapped k (Nodestate d))
        (Nodehead c) (Nodehead d) (splice T (Nodetape c) F)
        ((Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c))).2.1
        ((Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c))).2.2
        beforeBounds afterBounds
        (by rw [read,row,Edgerow edge]) (Edgemove edge)
    have tapeEq :=splice_put T (Nodetape c) F (Nodehead c)
      ((Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c))).2.1
      (by dsimp only [D] at beforeBounds; omega)
    fromDonor "CarryWindow.Geometry" "CarryWindow" "put" =>
      have actualTape : OLD (splice T (Nodetape c) F) (Nodehead c)
          ((Cursor.machine k).step (Nodestate c) (Nodetape c (Nodehead c))).2.1=splice T (Nodetape d) F := by
        change put _ _ _=_
        rw [← tapeEq,← Edgetape edge]
    rw [actualTape] at one
    fromDonor "VirtualLeaf.Body" "VirtualLeaf" "append" =>
      simpa only [Nat.add_comm 1 t] using OLD one (ih nextGood.1 last)
private theorem splice_image (T : Nat   →   Option Bool) (L n F r g W a b c d : Nat)
    (room : L+n+1  <  F) :
    splice (CarryWindow.Target.image T F r n g 0 0 W 0)
      (CappedWeight.Target.image (CarryWindow.Target.image T F r n g 0 0 W 0) L n F r a b c d 0) F=
      CarryWindow.Target.image T F r n g a b c d := by
  funext i
  dsimp only [splice,CarryWindow.Target.image,CappedWeight.Target.image]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem native_finish (k N B L n F r g W : Nat) (T : Nat    →    Option Bool)
    (room : L+n+1   <   F) (wr : W   ≤   r)
    (blank : ∀ j, j   ≤   6    →    T (D F r n j)=none)
    (b1 : ∀ i, D F r n 1   <   i    →    i   <   D F r n 2    →    ∃ b, T i=some b)
    (fit : D F r n 6   <   tapeLength N B) :
    let U:=CarryWindow.Target.image T F r n g 0 0 W 0
    ∃ t, t   ≤   4096*(W+1)*(D F r n 6+1)^2    ∧
      (CarryWindow.machine k).run t
        (⟨CarryWindow.extra k 23,⟨D F r n 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => U i.val⟩ : Config _ N B)=
        ⟨CarryWindow.embed k (cq k (Cursor.q k (613+93*k))),⟨D F r n 0,by dsimp only [D] at fit ⊢; omega⟩,
          fun i => CarryWindow.Target.image T F r n g (bitLength W) 0 0 W i.val⟩    ∧
      (∀ u, u   ≤   t    →    D F r n 0   ≤   ((CarryWindow.machine k).run u
        (⟨CarryWindow.extra k 23,⟨D F r n 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => U i.val⟩ : Config _ N B)).head.val    ∧
        ((CarryWindow.machine k).run u
        (⟨CarryWindow.extra k 23,⟨D F r n 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => U i.val⟩ : Config _ N B)).head.val   ≤   D F r n 6) := by
  intro U
  have ub (j : Nat) (hj : j   ≤   6) : U (D F r n j)=none := by
    have old:=blank j hj
    interval_cases j <;> dsimp only [D] at old ⊢
    all_goals dsimp only [U,CarryWindow.Target.image]
    all_goals repeat' rw [if_neg (by omega)]
    all_goals exact old
  have occ (j : Nat) (hj : j   <   6) (i : Nat) (lo : D F r n j   <   i) (hi : i   <   D F r n (j+1)) : ∃ b, U i=some b := by
    by_cases eq : j=1
    · subst j; dsimp only [U,CarryWindow.Target.image]
      dsimp only [D] at lo hi
      repeat' rw [if_neg (by omega)]
      exact b1 i lo hi
    · interval_cases j <;> try contradiction
      all_goals dsimp only [D] at lo hi
      all_goals dsimp only [U,CarryWindow.Target.image]
      all_goals split_ifs <;> first | exact ⟨_,rfl⟩ | (exfalso; omega)
  have fr : (by fromDonor "PostWeight.Kernel" "PostWeight" "Banks" => exact OLD U L n F r) := by
    fromDonor "PostWeight.Kernel" "PostWeight" "Banks.mk" => exact OLD room ub
  fromDonor "PostWeight.Raw" "PostWeight" "ell_le" => have ell:=OLD W
  fromDonor "PostWeight.Length" "PostWeight" "postLength" =>
    obtain ⟨t,ht,phase⟩:=OLD (k:=k) fr (P:=D F r n 6) le_rfl 0 W wr (ell.trans wr)
  fromDonor "PostWeight.Length" "PostWeight" "seekStart" =>
    have seek:=OLD (k:=k) fr (P:=D F r n 6) le_rfl (bitLength W) W (occ 0 (by decide)) (occ 1 (by decide))
  fromDonor "PostWeight.Kernel" "PostWeight" "Path.append" => have joined:=OLD phase seek
  let A:=CappedWeight.Target.image U L n F r 0 0 W 0 0
  let Z:=CappedWeight.Target.image U L n F r (bitLength W) 0 0 W 0
  have inputShape : Shape F r n A := by
    apply shape_of_banks
    · intro j hj
      fromDonor "PostWeight.Kernel" "PostWeight" "atD" => exact OLD fr 0 0 W 0 j hj
    · intro j hj i lo hi
      by_cases small : j   <   2
      · have old : A i=U i := by
          interval_cases j <;> dsimp only [D] at lo hi
          all_goals dsimp only [A,CappedWeight.Target.image]
          all_goals repeat' rw [if_neg (by omega)]
        rw [old]; exact occ j hj i lo hi
      · fromDonor "PostWeight.Kernel" "PostWeight" "atBank" => exact ⟨_,OLD fr 0 0 W 0 j i (by omega) hj lo hi⟩
  have good : Good k F r n (Nodemk (Cursor.q k (430+93*k)) (D F r n 2) A) :=
    ⟨430,4,by decide,by decide,rfl,by decide,by decide,by dsimp [Loc],inputShape⟩
  have transfer:=path_lift (N:=N) (B:=B) U joined good rfl fit rfl
  have initEq : splice U A F=U := splice_image T L n F r g W 0 0 W 0 room
  have endEq : splice U Z F=CarryWindow.Target.image T F r n g (bitLength W) 0 0 W :=
    splice_image T L n F r g W (bitLength W) 0 0 W room
  have lastMapped : mapped k (Cursor.q k (613+93*k))=CarryWindow.embed k (cq k (Cursor.q k (613+93*k))) := by
    dsimp only [mapped]; rw [if_neg (by intro eq; have h:=q_inj (by unfold Cursor.stateCount; omega) (by unfold Cursor.stateCount; omega) eq; omega)]
  have startMapped : mapped k (Cursor.q k (430+93*k))=CarryWindow.extra k 23 := by dsimp only [mapped]; rw [if_pos rfl]
  fromDonor "VirtualLeaf.Body" "VirtualLeaf" "Trace.run" => have run:=OLD transfer
  fromDonor "VirtualLeaf.Body" "VirtualLeaf" "Trace.bound" => have bounds:=OLD transfer
  change (CarryWindow.machine k).run (t+(3*r+n+8)) (lifted U F (Nodemk (Cursor.q k (430+93*k)) (D F r n 2) A) _)=
    lifted U F (Nodemk (Cursor.q k (613+93*k)) (D F r n 0) Z) _ at run
  change ∀ v, v ≤ t+(3*r+n+8)  →  D F r n 0 ≤ ((CarryWindow.machine k).run v
    (lifted (N:=N) (B:=B) U F (Nodemk (Cursor.q k (430+93*k)) (D F r n 2) A) _)).head.val  ∧
    ((CarryWindow.machine k).run v
    (lifted (N:=N) (B:=B) U F (Nodemk (Cursor.q k (430+93*k)) (D F r n 2) A) _)).head.val ≤ D F r n 6 at bounds
  dsimp only [lifted] at run bounds
  rw [initEq,endEq,startMapped,lastMapped] at run
  rw [initEq,startMapped] at bounds
  refine ⟨t+(3*r+n+8),?_,run,bounds⟩
  fromDonor "PostWeight.Raw" "PostWeight" "join_clock" => exact OLD _ W t (3*r+n+8) ht (by dsimp only [D]; omega)

private theorem price_plain (P r n g W u : Nat) (wide : 5*r+n+7  ≤  P) (gr : g  ≤  r) (wr : W  ≤  r)
    (hu : u  ≤  4096*(W+1)*(P+1)^2) :
    g*(2*g+4*r+2*n+11)+4*r+2*n+10+u+1  ≤  8192*(r+1)*(P+2)^2 := by
  have mul:=Nat.mul_le_mul gr (show 2*g+4*r+2*n+11  ≤  2*(P+2) by omega)
  have carry : g*(2*g+4*r+2*n+11)+4*r+2*n+10  ≤  4*(r+1)*(P+2) := by nlinarith only [mul,wide]
  have tail:=Nat.mul_le_mul (Nat.mul_le_mul_left 4096 (show W+1  ≤  r+1 by omega))
    (Nat.pow_le_pow_left (show P+1  ≤  P+2 by omega) 2)
  have sq : P+2  ≤  (P+2)^2 := by nlinarith only [Nat.zero_le (P^2)]
  have lift:=Nat.mul_le_mul_left (4*(r+1)) sq
  have one : 1 ≤ (r+1)*(P+2)^2 := by
    have h : 0 < (r+1)*(P+2)^2 := by positivity
    omega
  nlinarith only [carry,hu,tail,lift,one]
private theorem finish_price (r n F g W u : Nat) (gr : g  ≤  r) (wr : W  ≤  r)
    (hu : u  ≤  4096*(W+1)*(F+5*r+n+8)^2) :
    g*(2*g+4*r+2*n+11)+4*r+2*n+10+u+1  ≤  8192*(r+1)*(F+5*r+n+9)^2 := by
  exact price_plain (F+5*r+n+7) r n g W u (by omega) gr wr hu
private theorem ready_stays (k : Nat) (b : Option Bool) :
    (CarryWindow.machine k).step (CarryWindow.ready k) b=(CarryWindow.ready k,b,.stay) := by
  dsimp only [CarryWindow.ready]
  fromDonor "CarryWindow.Rows" "CarryWindow" "native_row" => rw [OLD]
  fromDonor "CarryWindow.Machine" "CarryWindow" "native" => rfl
private theorem before_ready {k N B t} (c : Config (CarryWindow.machine k).stateCount N B)
    (last : ((CarryWindow.machine k).run t c).state   ≠   CarryWindow.ready k) :
    ∀ u, u   ≤   t    →    ((CarryWindow.machine k).run u c).state   ≠   CarryWindow.ready k := by
  have keep {c : Config (CarryWindow.machine k).stateCount N B} (hc : c.state=CarryWindow.ready k) (v : Nat) :
      ((CarryWindow.machine k).run v c).state=CarryWindow.ready k := by
    induction v with
    | zero => rw [UniformTM.run]; exact hc
    | succ v ih => rw [UniformTM.run]; change ((CarryWindow.machine k).step _ _).1=_; rw [ih,ready_stays]
  intro u hu bad
  have endState:=keep bad (t-u)
  rw [←UniformTM.run_add,show u+(t-u)=t by omega] at endState
  exact last endState
private theorem work_safe {k N B t} (c : Config (CarryWindow.machine k).stateCount N B)
    (last : ((CarryWindow.machine k).run t c).state=CarryWindow.ready k) :
    ∀ u, u   ≤   t    →    ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).accept    ∧
      ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).reject := by
  apply (CarryWindow.machine k).no_terminal_of_le c
  all_goals rw [last]
  all_goals intro bad; have e:=congrArg Fin.val bad
  all_goals change (CanonicalLeaf.machine k).stateCount+24=_ at e
  all_goals first | change _=327 at e | change _=328 at e
  all_goals have low : 1233   ≤   (CanonicalLeaf.machine k).stateCount := by change 1233   ≤   288+Cursor.stateCount k+8; unfold Cursor.stateCount; omega
  all_goals omega
private theorem complete_frame (k N B L n F r g W : Nat) (T : Nat    →    Option Bool)
    (room : L+n+1   <   F) (gr : g   ≤   r) (wr : W   ≤   r)
    (blank : ∀ j, j   ≤   6    →    T (D F r n j)=none)
    (b1 : ∀ i, D F r n 1   <   i    →    i   <   D F r n 2    →    ∃ b, T i=some b)
    (whole : T=CarryWindow.Target.image T F r n r 0 g W 0)
    (fit : D F r n 6   <   tapeLength N B) :
    let c : Config (CarryWindow.machine k).stateCount N B:=
      ⟨CarryWindow.embed k (cq k (Cursor.q k (430+93*k))),⟨D F r n 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => T i.val⟩
    ∃ t, t   ≤   8192*(r+1)*(D F r n 6+2)^2    ∧
      (CarryWindow.machine k).run t c=⟨CarryWindow.ready k,⟨D F r n 0,by dsimp only [D] at fit ⊢; omega⟩,
        fun i => CarryWindow.Target.image T F r n g (bitLength W) 0 0 W i.val⟩    ∧
      (∀ u, u   ≤   t    →    D F r n 0   ≤   ((CarryWindow.machine k).run u c).head.val    ∧
        ((CarryWindow.machine k).run u c).head.val   ≤   D F r n 6)    ∧
      (∀ u, u   ≤   t    →    ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).accept    ∧
        ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).reject)    ∧
      (∀ u, u   <   t    →    ((CarryWindow.machine k).run u c).state   ≠   CarryWindow.ready k) := by
  intro c
  have carry:=CarryWindow.prepared_carry k N B F r n g W T gr blank b1 fit
  dsimp only at carry
  rw [←whole] at carry
  obtain ⟨u,hu,native,foot⟩:=native_finish k N B L n F r g W T room wr blank b1 fit
  let d:=g*(2*g+4*r+2*n+11)+4*r+2*n+10
  have carried : (CarryWindow.machine k).run d c=
      ⟨CarryWindow.extra k 23,⟨D F r n 2,by dsimp only [D] at fit ⊢; omega⟩,
        fun i => CarryWindow.Target.image T F r n g 0 0 W 0 i.val⟩ := carry.1
  have prelast : (CarryWindow.machine k).run (d+u) c=
      ⟨CarryWindow.embed k (cq k (Cursor.q k (613+93*k))),⟨F+1,by dsimp only [D] at fit; omega⟩,
        fun i => CarryWindow.Target.image T F r n g (bitLength W) 0 0 W i.val⟩ := by
    rw [UniformTM.run_add,carried]; exact native
  have cell : CarryWindow.Target.image T F r n g (bitLength W) 0 0 W (F+1)=none := by
    dsimp only [CarryWindow.Target.image]
    repeat' rw [if_neg (by omega)]
    exact blank 0 (by decide)
  have lastRow : (CarryWindow.machine k).step (CarryWindow.embed k (cq k (Cursor.q k (613+93*k)))) none=
      (CarryWindow.ready k,none,.stay) := by
    rw [CarryWindow.table_delta,if_neg (by
      intro h; have e:=congrArg Fin.val h.1
      change 288+(613+93*k)%Cursor.stateCount k=288+(430+93*k)%Cursor.stateCount k at e
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega),Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at e
      omega),if_pos ⟨rfl,rfl⟩]
  have done : (CarryWindow.machine k).run (d+u+1) c=
      ⟨CarryWindow.ready k,⟨F+1,by dsimp only [D] at fit; omega⟩,
        fun i => CarryWindow.Target.image T F r n g (bitLength W) 0 0 W i.val⟩ := by
    rw [UniformTM.run,prelast]
    apply Config.ext_parts
    · change ((CarryWindow.machine k).step _ (CarryWindow.Target.image T F r n g (bitLength W) 0 0 W (F+1))).1=_
      rw [cell,lastRow]
    · apply Fin.ext; change (moveHead _ ((CarryWindow.machine k).step _ _).2.2).val=_
      dsimp only
      rw [cell,lastRow]; rfl
    · funext i; dsimp only [UniformTM.stepConfig]; rw [cell,lastRow]
      by_cases eq : i.val=F+1
      · have h : i=⟨F+1,by dsimp only [D] at fit; omega⟩:=Fin.ext eq
        rw [if_pos h,eq]; exact cell.symm
      · rw [if_neg (by intro h; exact eq (congrArg Fin.val h))]
  have first:=before_ready c (t:=d+u) (by
    rw [prelast]; intro bad; have e:=congrArg Fin.val bad
    change 288+(613+93*k)%Cursor.stateCount k=(CanonicalLeaf.machine k).stateCount+24 at e
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at e
    change _=288+Cursor.stateCount k+8+24 at e; unfold Cursor.stateCount at e; omega)
  refine ⟨d+u+1,finish_price r n F g W u gr wr hu,done,?_,work_safe c (congrArg Config.state done),?_⟩
  · intro v hv
    by_cases early : v   ≤   d
    · exact carry.2.1 v early
    · by_cases last : v=d+u+1
      · rw [last,done]; dsimp only [D]; omega
      · rw [show v=d+(v-d) by omega,UniformTM.run_add,carried]
        exact foot (v-d) (by omega)
  · intro v hv; exact first v (by omega)
private theorem complete_body (k : Nat) : CarryWindow.Target.Body k := by
  intro N B L n F r g W beta T D0 room gr wr sep right digits blank b0 b1 b2 b3 b4 b5 fit c
  have whole : T=CarryWindow.Target.image T F r n r 0 g W 0 := by
    funext i
    dsimp only [CarryWindow.Target.image]
    split_ifs with h0 h2 h3 h4 h5
    · rw [b0 i h0.1 h0.2,decide_eq_true (by omega)]
    · rw [b2 i h2.1 h2.2,decide_eq_false (by omega)]
    · exact b3 i h3.1 h3.2
    · exact b4 i h4.1 h4.2
    · rw [b5 i h5.1 h5.2,decide_eq_false (by omega)]
    · rfl
  exact complete_frame k N B L n F r g W T room gr wr blank b1 whole fit

end CarryReadyCompletion
