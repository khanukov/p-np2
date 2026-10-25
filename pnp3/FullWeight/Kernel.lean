import FullWeight.Rows
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
private structure Node (k : Nat) where
  state : Fin (Cursor.stateCount k)
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {k N B : Nat} (c : Node k) (h : c.head   <   tapeLength N B) : Config (Cursor.stateCount k) N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (k P : Nat) (c d : Node k) : Prop where
  safe : c.state.val   <   (430+93*k)
  before : c.head       ≤       P
  after : d.head       ≤       P
  row : ((Cursor.machine k).step c.state (c.tape c.head)).1 = d.state
  move : dest c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.1
private inductive Path (k P : Nat) : Nat → Node k → Node k → Prop
  | nil (c) (h : c.head       ≤       P) : Path k P 0 c c
  | cons {t c d e} : Edge k P c d → Path k P t d e → Path k P (t+1) c e
namespace Path
private theorem bounds {k P t c d} (h : Path k P t c d) : c.head       ≤       P ∧ d.head       ≤       P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) :
    Path k P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {k N B P t c d} (h : Path k P t c d) (hp : P   <   tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge k P c d) :
      (Cursor.machine k).stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ ((Cursor.machine k).step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : ((Cursor.machine k).step c.state (c.tape c.head)).2.2 with
      | left => simpa only [mv,moveHead,embed,dest] using hm
      | stay => simpa only [mv,moveHead,embed,dest] using hm
      | right =>
        rw [mv] at hm
        simp only [dest] at hm
        have hd := e.after
        have hr : c.head+1   <   tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head   <   tapeLength N B) (hd : d.head   <   tapeLength N B),
      (Cursor.machine k).run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; rfl
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,(Cursor.machine k).run_add]
    change (Cursor.machine k).run t ((Cursor.machine k).stepConfig (embed c hc)) = embed e he
    rw [step ed]
    exact ih _ _
end Path
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val   <   (430+93*k)) (hb : h       ≤       P) (ha : h'       ≤       P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val   <   (430+93*k)) (hb : h       ≤       P) (ha : h'       ≤       P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val   <   (430+93*k)) (fit : h+r       ≤       P) (rows : ∀ i, h       ≤       i → i   <   h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val   <   (430+93*k)) (fit : low+r       ≤       P) (rows : ∀ i, low   <   i → i       ≤       low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P   <   tapeLength N B)
    (u : Nat) (hu : u   <   t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val   <   (430+93*k) := by
  induction path generalizing u with
  | nil => omega
  | @cons t c d e edge rest ih =>
    cases u with
    | zero => exact edge.safe
    | succ u =>
      have one : Path k P 1 c d := Path.cons edge (Path.nil d edge.after)
      rw [show u+1=1+u by omega,UniformTM.run_add,one.execute hp]
      exact ih u (by omega)
private theorem small_mod (k i : Nat) (h : i     ≤     798+93*k) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (safe : s   <   (430+93*k)) (hb : h     ≤     P) (ha : h'     ≤     P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ := by
  apply keep _ _ _ _ _ _ ?_ hb ha (by rw [value]; exact row) hm
  simpa only [Cursor.q,small_mod k s (by omega)] using safe
private theorem crossR {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (hs : s  <  (430+93*k)) (hscan : scan  <  (430+93*k)) (fit : low+width+1    ≤    P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low  <  i → i  <  low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.right))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.right))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low,T⟩ ⟨Cursor.q k out,low+width+1,T⟩ := by
  have a := K (k:=k) s scan low (low+1) T none .right hs (P:=P) (by omega) (by omega) d entry rfl
  have b := sweepR (Cursor.q k scan) T (low+1) width
    (by change scan % Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; exact hscan) (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i (by omega) (by omega); rw [hb]; exact body b)
  rw [show low+1+width=low+width+1 by omega] at b
  have c := K (k:=k) scan out (low+width+1) (low+width+1) T none .stay hscan (P:=P) (by omega) (by omega) endD exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private theorem crossL {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (hs : s  <  (430+93*k)) (hscan : scan  <  (430+93*k)) (fit : low+width+1    ≤    P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low  <  i → i  <  low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.left))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.left))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low+width+1,T⟩ ⟨Cursor.q k out,low,T⟩ := by
  have a := K (k:=k) s scan (low+width+1) (low+width) T none .left hs (P:=P) (by omega) (by omega) endD entry (by simp [dest])
  have b := sweepL (Cursor.q k scan) T low width
    (by change scan % Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; exact hscan) (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i lo (by omega); rw [hb]; exact body b)
  have c := K (k:=k) scan out low low T none .stay hscan (P:=P) (by omega) (by omega) d exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private theorem inc {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (safe : s+3  <  (430+93*k)) (fit : base+w+1    ≤    P) (hv : v    ≤    w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base  <  i → i  <  base+w+1 → T i=some (decide (i    ≤    base+v)))
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (add : (Cursor.machine k).step (Cursor.q k (s+1)) (some false)=(Cursor.q k (s+2),some true,.left))
    (full : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+3),none,.left))
    (back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left))
    (ok : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k yes,none,.stay))
    (bad : (Cursor.machine k).step (Cursor.q k (s+3)) (some true)=(Cursor.q k (s+3),some true,.left))
    (over : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k no,none,.stay)) :
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v  <  w then yes else no),base,if v  <  w then put T (base+v+1) (some true) else T⟩ := by
  have first := K (k:=k) s (s+1) base (base+1) T none .right (by omega) (P:=P) (by omega) (by omega) sep entry rfl
  have fwd := sweepR (Cursor.q k (s+1)) T (base+1) v
    (by change (s+1)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
      intro i lo hi; have val:=unary i (by omega) (by omega)
      rw [show T i=some true by simpa only [decide_eq_true (by omega : i    ≤    base+v)] using val]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  by_cases fits : v  <  w
  · have val : T (base+v+1)=some false := by
      have u:=unary (base+v+1) (by omega) (by omega); simpa only [decide_eq_false (by omega : ¬base+v+1    ≤    base+v)] using u
    have changeTape := hop (P:=P) (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T (some true) .left
      (by change (s+1)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (by omega) (by omega) (by rw [val]; exact add) (by simp [dest])
    let U:=put T (base+v+1) (some true)
    have rev:=sweepL (Cursor.q k (s+2)) U base v
      (by change (s+2)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
        intro i lo hi
        have eq : U i=T i := by dsimp [U,put]; rw [if_neg (by omega)]
        rw [eq]; have u:=unary i lo (by omega); rw [u]; exact back _)
    have last:=K (k:=k) (s+2) yes base base U none .stay (by omega) (P:=P) (by omega) (by omega)
      (by dsimp [U,put]; rw [if_neg (by omega)]; exact sep) ok rfl
    simpa only [if_pos fits,show 1+v+1+v+1=2*v+3 by omega] using first.append fwd |>.append changeTape |>.append rev |>.append last
  · have eq : v=w := by omega
    have next : T (base+v+1)=none := by simpa only [eq] using endD
    have turn:=K (k:=k) (s+1) (s+3) (base+v+1) (base+v) T none .left (by omega) (P:=P) (by omega) (by omega) next full (by simp [dest])
    have rev:=sweepL (Cursor.q k (s+3)) T base v
      (by change (s+3)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
        intro i lo hi; have u:=unary i lo (by omega); rw [u,decide_eq_true hi]; exact bad)
    have last:=K (k:=k) (s+3) no base base T none .stay (by omega) (P:=P) (by omega) (by omega) sep over rfl
    simpa only [if_neg fits,show 1+v+1+v+1=2*v+3 by omega] using first.append fwd |>.append turn |>.append rev |>.append last
private theorem dec {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (safe : s+3  <  (430+93*k)) (fit : base+w+1   ≤   P) (hv : v   ≤   w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base  <  i → i  <  base+w+1 → T i=some (decide (i   ≤   base+v)))
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (tail : ∀ b, b ≠ some true → (Cursor.machine k).step (Cursor.q k (s+1)) b=(Cursor.q k (s+2),b,.left))
    (take : (Cursor.machine k).step (Cursor.q k (s+2)) (some true)=(Cursor.q k (s+3),some false,.left))
    (back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+3)) (some b)=(Cursor.q k (s+3),some b,.left))
    (ok : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k yes,none,.stay))
    (empty : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k no,none,.stay)) :
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v=0 then no else yes),base,if v=0 then T else put T (base+v) (some false)⟩ := by
  have first:=K (k:=k) s (s+1) base (base+1) T none .right (by omega) (P:=P) (by omega) (by omega) sep entry rfl
  have fwd:=sweepR (Cursor.q k (s+1)) T (base+1) v
    (by change (s+1)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
      intro i lo hi; have u:=unary i (by omega) (by omega)
      rw [u,decide_eq_true (by omega : i   ≤   base+v)]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  have next : T (base+v+1) ≠ some true := by
    by_cases full : v=w
    · rw [full,endD]; decide
    · have u:=unary (base+v+1) (by omega) (by omega)
      rw [u,decide_eq_false (by omega : ¬base+v+1   ≤   base+v)]; decide
  have turn:=keep (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T .left
    (by change (s+1)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by omega) (tail _ next) (by simp [dest])
  by_cases zero : v=0
  · subst v
    have last:=K (k:=k) (s+2) no base base T none .stay (by omega) (P:=P) (by omega) (by omega) sep empty rfl
    simpa using first.append fwd |>.append turn |>.append last
  · obtain ⟨a,rfl⟩ : ∃ a, v=a+1 := ⟨v-1,by omega⟩
    have cell : T (base+(a+1))=some true := by
      rw [unary _ (by omega) (by omega),decide_eq_true (by omega)]
    have write:=hop (P:=P) (Cursor.q k (s+2)) (Cursor.q k (s+3)) (base+(a+1)) (base+a) T (some false) .left
      (by change (s+2)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (by omega) (by omega) (by rw [cell]; exact take) (by simp [dest])
    let U:=put T (base+(a+1)) (some false)
    have rev:=sweepL (Cursor.q k (s+3)) U base a
      (by change (s+3)%Cursor.stateCount k  <  (430+93*k); rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
        intro i lo hi
        have eq : U i=T i := by dsimp [U,put]; rw [if_neg (by omega)]
        rw [eq,unary _ lo (by omega)]; exact back _)
    have last:=K (k:=k) (s+3) yes base base U none .stay (by omega) (P:=P) (by omega) (by omega)
      (by dsimp [U,put]; rw [if_neg (by omega)]; exact sep) ok rfl
    simpa only [if_neg (by omega : a+1 ≠ 0),show 1+(a+1)+1+1+a+1=2*(a+1)+3 by omega] using
      first.append fwd |>.append turn |>.append write |>.append rev |>.append last
private def D (F r n j : Nat) : Nat := match j with
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private abbrev Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop := by
  fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame" => exact OLD T L n Q F r
private def I (T : Nat → Option Bool) (L n F r : Nat) (v : Nat → Nat) : Nat → Option Bool :=
  CappedWeight.Target.image T L n F r (v 2) (v 3) (v 4) (v 5) 0
private theorem geo {T L n Q F r} (fr : Frame T L n Q F r) : L+n+1 < F := by
  fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame.room" => have h:=OLD fr
  omega
private theorem delim {T L n Q F r} (fr : Frame T L n Q F r) (j : Nat) (hj : j ≤ 6) : T (D F r n j)=none := by
  fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame.ds" => exact OLD fr j hj
private theorem atD {T L n Q F r} (fr : Frame T L n Q F r) (v : Nat → Nat) (j : Nat) (hj : j ≤ 6) : I T L n F r v (D F r n j)=none := by
  have h:=geo fr
  have d:=delim fr j hj
  interval_cases j <;> dsimp only [D] at d ⊢ <;>
    dsimp only [I,CappedWeight.Target.image] <;>
    repeat' rw [if_neg (by omega)]
  all_goals exact d
private theorem unary {T L n Q F r} (fr : Frame T L n Q F r) (v : Nat → Nat) (j : Nat) (lo : 2 ≤ j) (hi : j < 6) :
    ∀ i, D F r n j < i → i < D F r n (j+1) → I T L n F r v i=some (decide (i ≤ D F r n j+v j)) := by
  have h:=geo fr
  interval_cases j <;> intro i il iu <;> dsimp only [D] at il iu ⊢ <;>
    dsimp only [I,CappedWeight.Target.image] <;>
    split_ifs <;> first | rfl | omega
private theorem occupied {T L n Q F r} (fr : Frame T L n Q F r) (v : Nat → Nat) (j : Nat) (hj : j < 6) :
    ∀ i, D F r n j < i → i < D F r n (j+1) → ∃ b, I T L n F r v i=some b := by
  intro i il iu
  by_cases small : j < 2
  · have h:=geo fr
    fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame.banks" => have old:=OLD fr j hj i il iu
    interval_cases j <;> dsimp only [D] at il iu <;> dsimp only [I,CappedWeight.Target.image] <;>
      repeat' rw [if_neg (by omega)]
    all_goals exact ⟨_,old⟩
  · exact ⟨_,unary fr v j (by omega) hj i il iu⟩
private theorem outsideUpdate {T L n Q F r} (fr : Frame T L n Q F r) (v : Nat → Nat) (j a i : Nat)
    (jl : 2 ≤ j) (ju : j < 6) (out : ¬(D F r n j < i ∧ i < D F r n (j+1))) :
    I T L n F r (Function.update v j a) i=I T L n F r v i := by
  have h:=geo fr
  interval_cases j <;> dsimp only [D] at out <;>
    dsimp only [I,CappedWeight.Target.image] <;>
    simp only [Function.update,↓reduceDIte] <;>
    split_ifs <;> simp_all <;> omega
private theorem write {T L n Q F r} (fr : Frame T L n Q F r) (v : Nat → Nat) (j a : Nat) (jl : 2 ≤ j) (ju : j < 6)
    (ha : a < r) (bit : Bool) (value : v j=if bit then a else a+1) :
    put (I T L n F r v) (D F r n j+a+1) (some bit)=
      I T L n F r (Function.update v j (if bit then a+1 else a)) := by
  funext i
  by_cases inside : D F r n j < i ∧ i < D F r n (j+1)
  · rw [unary fr _ j jl ju i inside.1 inside.2,Function.update_self]
    dsimp only [put]
    by_cases hit : i=D F r n j+a+1
    · rw [if_pos hit]
      subst i
      cases bit with
      | false => simp only [Bool.false_eq_true,ite_false];rw [decide_eq_false (by omega)]
      | true => simp only [ite_true];rw [decide_eq_true (by omega)]
    · rw [if_neg hit,unary fr v j jl ju i inside.1 inside.2,value]
      cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
        congr 2 <;> apply propext <;> omega
  · rw [outsideUpdate fr v j _ i jl ju inside]
    dsimp only [put]
    rw [if_neg (by
      intro hit;subst i
      have bound : D F r n j+r+1=D F r n (j+1) := by interval_cases j <;> dsimp only [D] <;> omega
      exact inside ⟨by omega,by omega⟩)]
end FullWeight
