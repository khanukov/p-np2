import PhysicalCallerClosure.Rows
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
-- One shared proof-side parametric native path interface for the NEW caller table.
-- Every Edge is an actual literal row; Safe is a control-only predicate, not semantic advice.
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure Node (M : UniformTM) where
  state : Fin M.stateCount
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {N B : Nat} (c : Node M) (h : c.head  <  tapeLength N B) : Config M.stateCount N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (M : UniformTM) (Safe : Fin M.stateCount → Prop) (P : Nat) (c d : Node M) : Prop where
  nonterminal : Safe c.state
  before : c.head  ≤  P
  after : d.head  ≤  P
  row : (M.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (M.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (M.step c.state (c.tape c.head)).2.1
private inductive Path (M : UniformTM) (Safe : Fin M.stateCount → Prop) (P : Nat) : Nat → Node M → Node M → Prop
  | nil (c) (h : c.head  ≤  P) : Path M Safe P 0 c c
  | cons {t c d e} : Edge M Safe P c d → Path M Safe P t d e → Path M Safe P (t+1) c e
namespace Path
private theorem bounds {P t c d} (h : Path M Safe P t c d) : c.head  ≤  P ∧ d.head  ≤  P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {P t u c d e} (h : Path M Safe P t c d) (g : Path M Safe P u d e) :
    Path M Safe P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {N B P t c d} (h : Path M Safe P t c d) (hp : P  <  tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge M Safe P c d) :
      M.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (M.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (M.step c.state (c.tape c.head)).2.2 with
      | left => simpa only [mv,moveHead,embed,dest] using hm
      | stay => simpa only [mv,moveHead,embed,dest] using hm
      | right =>
        rw [mv] at hm
        simp only [dest] at hm
        have hd := e.after
        have hr : c.head+1  <  tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head  <  tapeLength N B) (hd : d.head  <  tapeLength N B),
      M.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; simp only [UniformTM.run]
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,M.run_add]
    rw [show M.run 1 (embed c hc)=M.stepConfig (embed c hc) by simp only [UniformTM.run]]
    rw [step ed]
    exact ih _ _
end Path
private theorem hop {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h  ≤  P) (ha : h'  ≤  P)
    (safe : Safe s)
    (row : M.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path M Safe P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨safe,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h  <;> simp [put,hi]
private theorem keep {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h  ≤  P) (ha : h'  ≤  P)
    (safe : Safe s)
    (row : M.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path M Safe P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha safe row hm
  rwa [put_same] at one
private theorem sweepR {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (h r : Nat) (fit : h+r  ≤  P) (safe : Safe s) (rows : ∀ i, h  ≤  i → i  <  h+r → M.step s (T i)=(s,T i,.right)) :
    Path M Safe P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega) safe (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (low r : Nat) (fit : low+r  ≤  P) (safe : Safe s) (rows : ∀ i, low  <  i → i  ≤  low+r → M.step s (T i)=(s,T i,.left)) :
    Path M Safe P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega) safe (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

private theorem crossR {P : Nat} (e s q : Fin M.stateCount) (T : Nat → Option Bool)
    (a w : Nat) (fit : a+w+1  ≤  P) (safeE : Safe e) (safeS : Safe s)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a  <  i → i  <  a+w+1 → ∃ b, T i=some b)
    (start : M.step e none=(s,none,.right))
    (loop : ∀ b, M.step s (some b)=(s,some b,.right))
    (stop : M.step s none=(q,none,.stay)) :
    Path M Safe P (w+2) ⟨e,a,T⟩ ⟨q,a+w+1,T⟩ := by
  have one:=keep e s a (a+1) T .right (P:=P) (by omega) (by omega) safeE (by rw [atA]; exact start) rfl
  have middle:=sweepR s T (a+1) w (P:=P) (by omega) safeS (by
    intro i lo hi
    obtain ⟨b,hb⟩:=cells i (by omega) (by omega)
    rw [hb]; exact loop b)
  rw [show a+1+w=a+w+1 by omega] at middle
  have last:=keep s q (a+w+1) (a+w+1) T .stay (P:=P) fit fit safeS (by rw [atB]; exact stop) rfl
  have path:=one.append (middle.append last)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem crossL {P : Nat} (e s q : Fin M.stateCount) (T : Nat → Option Bool)
    (a w : Nat) (fit : a+w+1  ≤  P) (safeE : Safe e) (safeS : Safe s)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a  <  i → i  <  a+w+1 → ∃ b, T i=some b)
    (start : M.step e none=(s,none,.left))
    (loop : ∀ b, M.step s (some b)=(s,some b,.left))
    (stop : M.step s none=(q,none,.stay)) :
    Path M Safe P (w+2) ⟨e,a+w+1,T⟩ ⟨q,a,T⟩ := by
  have one:=keep e s (a+w+1) (a+w) T .left (P:=P) fit (by omega) safeE (by rw [atB]; exact start) (by simp [dest])
  have middle:=sweepL s T a w (P:=P) (by omega) safeS (by
    intro i lo hi
    obtain ⟨b,hb⟩:=cells i lo (by omega)
    rw [hb]; exact loop b)
  have last:=keep s q a a T .stay (P:=P) (by omega) (by omega) safeS (by rw [atA]; exact stop) rfl
  have path:=one.append (middle.append last)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
namespace Path
private theorem split {P t a b} (p : Path M Safe P t a b) :
    ∀ u,u ≤ t → ∃ c,Path M Safe P u a c ∧ Path M Safe P (t-u) c b := by
  induction p with
  | nil c bound=>
    intro u hu
    have zero:u=0:=by omega
    subst u
    exact ⟨c,Path.nil c bound,Path.nil c bound⟩
  | @cons t a d b edge tail ih=>
    intro u hu
    cases u with
    | zero=>exact ⟨a,Path.nil a edge.before,by simpa using Path.cons edge tail⟩
    | succ u=>
      obtain ⟨c,first,last⟩:=ih u (by omega)
      exact ⟨c,Path.cons edge first,by simpa using last⟩
private theorem exterior {P t a b} (p : Path M Safe P t a b) :
    ∀ i,P < i → b.tape i=a.tape i := by
  induction p with
  | nil=>intro i _;rfl
  | @cons t a d b edge _tail ih=>
    intro i hi
    rw [ih i hi,edge.tape]
    change (if i=a.head then _ else a.tape i)=a.tape i
    exact if_neg (by have h:=edge.before;omega)
private theorem start_safe {P t a b} (p : Path M Safe P t a b) (positive : 0 < t) : Safe a.state := by
  cases p with
  | nil=>omega
  | cons edge _=>exact edge.nonterminal
private theorem safe_prefix {N B P t a b} (p : Path M Safe P t a b) (fit:P < tapeLength N B) :
    ∀ u,u < t → Safe (M.run u (embed a (lt_of_le_of_lt p.bounds.1 fit))).state := by
  intro u hu
  obtain ⟨c,first,last⟩:=p.split u (by omega)
  rw [first.execute fit]
  exact last.start_safe (by omega)
/-- Every-prefix head and exterior footprint for the same literal path.
Only right moves need right-room; last-cell left/stay edges are permitted. -/
private theorem footprint {N B P t a b} (p : Path M Safe P t a b) (fit:P < tapeLength N B) :
    ∀ u,u ≤ t → (M.run u (embed a (lt_of_le_of_lt p.bounds.1 fit))).head.val ≤ P ∧
      ∀ i:Fin (tapeLength N B),P < i.val →
        (M.run u (embed a (lt_of_le_of_lt p.bounds.1 fit))).tape i=a.tape i.val := by
  intro u hu
  obtain ⟨c,first,_last⟩:=p.split u hu
  rw [first.execute fit]
  exact ⟨first.bounds.2,fun i hi=>first.exterior i.val hi⟩
end Path

-- Generic field routes and unary operations; the actual left-moving native rows are priced below.
private inductive RouteR (M : UniformTM) (Safe : Fin M.stateCount → Prop) : Nat → Nat → Fin M.stateCount → Fin M.stateCount → Prop
  | nil (i q) : RouteR M Safe i i q q
  | next {i j e s q x} : Safe e → Safe s →
      M.step e none=(s,none,.right) →
      (∀ b, M.step s (some b)=(s,some b,.right)) →
      M.step s none=(q,none,.stay) →
      RouteR M Safe (i+1) j q x → RouteR M Safe i j e x
private inductive RouteL (M : UniformTM) (Safe : Fin M.stateCount → Prop) : Nat → Nat → Fin M.stateCount → Fin M.stateCount → Prop
  | nil (i q) : RouteL M Safe i i q q
  | next {i j e s q x} : Safe e → Safe s →
      M.step e none=(s,none,.left) →
      (∀ b, M.step s (some b)=(s,some b,.left)) →
      M.step s none=(q,none,.stay) →
      RouteL M Safe i j q x → RouteL M Safe (i+1) j e x
private theorem RouteR.span {i j e x} (h : RouteR M Safe i j e x) : i ≤ j := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteL.span {i j e x} (h : RouteL M Safe i j e x) : j ≤ i := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteR.execute {i j e x P} (h : RouteR M Safe i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (fit : D j ≤ P)
    (rise : ∀ k, i ≤ k → k < j → D k < D (k+1))
    (mono : ∀ a b, i ≤ a → a ≤ b → b ≤ j → D a ≤ D b)
    (blank : ∀ k, i ≤ k → k ≤ j → T (D k)=none)
    (cells : ∀ k u, i ≤ k → k < j → D k < u → u < D (k+1) → ∃ b,T u=some b) :
    Path M Safe P (D j-D i+(j-i)) ⟨e,D i,T⟩ ⟨x,D j,T⟩ := by
  induction h with
  | nil i q => simpa using Path.nil ⟨q,D i,T⟩ fit
  | @next i j e s q x se ss re rs rn rest ih =>
    have ij:=rest.span
    have di:=rise i le_rfl (by omega)
    have eqn : D i+(D (i+1)-D i-1)+1=D (i+1) := by omega
    have cross:=crossR e s q T (D i) (D (i+1)-D i-1) (P:=P)
      (by rw [eqn]; exact le_trans (mono _ _ (by omega) (by omega) le_rfl) fit)
      se ss (blank _ le_rfl (by omega)) (by rw [eqn]; exact blank _ (by omega) (by omega))
      (by intro u lo hi; exact cells i u le_rfl (by omega) lo (by rwa [eqn] at hi)) re rs rn
    rw [eqn] at cross
    have tail:=ih fit (by intro k lo hi; exact rise k (by omega) hi)
      (by intro a b lo ab bj; exact mono a b (by omega) ab bj)
      (by intro k lo hi; exact blank k (by omega) hi)
      (by intro k u lo hi a b; exact cells k u (by omega) hi a b)
    have r:=cross.append tail
    have order:=mono i j le_rfl (by omega) le_rfl
    have order2:=mono (i+1) j (by omega) ij le_rfl
    convert r using 1
    omega
private theorem RouteL.execute {i j e x P} (h : RouteL M Safe i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (fit : D i ≤ P)
    (rise : ∀ k, j ≤ k → k < i → D k < D (k+1))
    (mono : ∀ a b, j ≤ a → a ≤ b → b ≤ i → D a ≤ D b)
    (blank : ∀ k, j ≤ k → k ≤ i → T (D k)=none)
    (cells : ∀ k u, j ≤ k → k < i → D k < u → u < D (k+1) → ∃ b,T u=some b) :
    Path M Safe P (D i-D j+(i-j)) ⟨e,D i,T⟩ ⟨x,D j,T⟩ := by
  induction h with
  | nil i q => simpa using Path.nil ⟨q,D i,T⟩ fit
  | @next i j e s q x se ss re rs rn rest ih =>
    have ij:=rest.span
    have di:=rise i ij (by omega)
    have eqn : D i+(D (i+1)-D i-1)+1=D (i+1) := by omega
    have cross:=crossL e s q T (D i) (D (i+1)-D i-1) (P:=P)
      (by rw [eqn]; exact fit) se ss (blank _ ij (by omega))
      (by rw [eqn]; exact blank _ (by omega) le_rfl)
      (by intro u lo hi; exact cells i u ij (by omega) lo (by rwa [eqn] at hi)) re rs rn
    rw [eqn] at cross
    have tail:=ih (le_trans (mono _ _ ij (by omega) le_rfl) fit)
      (by intro k lo hi; exact rise k lo (by omega))
      (by intro a b lo ab bj; exact mono a b lo ab (by omega))
      (by intro k lo hi; exact blank k lo (by omega))
      (by intro k u lo hi a b; exact cells k u lo (by omega) a b)
    have r:=cross.append tail
    have order:=mono j i le_rfl ij (by omega)
    convert r using 1
    omega

private structure Grid (D : Nat → Nat) (T : Nat → Option Bool) : Prop where
  rise : ∀ j, j < 13 → D j < D (j+1)
  mono : ∀ a b, a ≤ b → b ≤ 13 → D a ≤ D b
  blank : ∀ j, j ≤ 13 → T (D j)=none
  cells : ∀ j i, j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b
private theorem Grid.change_some {D T} (g : Grid D T) (h : Nat) (b c : Bool)
    (old : T h=some b) : Grid D (put T h (some c)) := by
  refine ⟨g.rise,g.mono,?_,?_⟩
  · intro j hj
    have ne : D j≠h := by intro eq; have bad:=g.blank j hj; rw [eq,old] at bad; contradiction
    simp only [put,if_neg ne]; exact g.blank j hj
  · intro j i hj lo hi
    by_cases eq : i=h
    · exact ⟨c,by simp only [put,if_pos eq]⟩
    · simpa only [put,if_neg eq] using g.cells j i hj lo hi
private theorem Grid.goR {D T i j s q P} (g : Grid D T) (r : RouteR M Safe i j s q)
    (hj : j ≤ 13) (fit : D 13 ≤ P) :
    Path M Safe P (D j-D i+(j-i)) ⟨s,D i,T⟩ ⟨q,D j,T⟩ :=
  r.execute D T (le_trans (g.mono _ _ hj le_rfl) fit)
    (by intro k _ hi; exact g.rise k (by omega))
    (by intro a b _ ab bj; exact g.mono a b ab (by omega))
    (by intro k _ hi; exact g.blank k (by omega))
    (by intro k u _ hi lo up; exact g.cells k u (by omega) lo up)
private theorem Grid.goL {D T i j s q P} (g : Grid D T) (r : RouteL M Safe i j s q)
    (hi : i ≤ 13) (fit : D 13 ≤ P) :
    Path M Safe P (D i-D j+(i-j)) ⟨s,D i,T⟩ ⟨q,D j,T⟩ :=
  r.execute D T (le_trans (g.mono _ _ hi le_rfl) fit)
    (by intro k _ hk; exact g.rise k (by omega))
    (by intro a b _ ab bi; exact g.mono a b ab (by omega))
    (by intro k _ hk; exact g.blank k (by omega))
    (by intro k u _ hk lo up; exact g.cells k u (by omega) lo up)
private def paint (T : Nat → Option Bool) (h w : Nat) (b : Bool) : Nat → Option Bool :=
  fun i => if h ≤ i ∧ i < h+w then some b else T i
private theorem paint_zero (T : Nat → Option Bool) (h : Nat) (b : Bool) : paint T h 0 b=T := by
  funext i; simp [paint]
private theorem paint_next (T : Nat → Option Bool) (h w : Nat) (b : Bool) :
    paint (put T h (some b)) (h+1) w b=paint T h (w+1) b := by
  funext i
  by_cases eq : i=h
  · subst i; simp [paint,put]
  · by_cases hi : h+1 ≤ i ∧ i < h+1+w
    · have hu : h ≤ i ∧ i < h+(w+1) := by omega
      simp only [paint,if_pos hi,if_pos hu]
    · have hu : ¬(h ≤ i ∧ i < h+(w+1)) := by omega
      simp only [paint,if_neg hi,if_neg hu,put,if_neg eq]
private theorem paint_run {P : Nat} (q : Fin M.stateCount) (T : Nat → Option Bool)
    (h w : Nat) (b : Bool) (fit : h+w ≤ P) (safe : Safe q)
    (occupied : ∀ i,h ≤ i → i < h+w → ∃ c,T i=some c)
    (row : ∀ c,M.step q (some c)=(q,some b,.right)) :
    Path M Safe P w ⟨q,h,T⟩ ⟨q,h+w,paint T h w b⟩ := by
  induction w generalizing h T with
  | zero => simpa only [Nat.add_zero,paint_zero] using Path.nil ⟨q,h,T⟩ fit
  | succ w ih =>
    obtain ⟨c,hc⟩:=occupied h le_rfl (by omega)
    have first:=hop q q h (h+1) T (some b) .right (P:=P) (by omega) (by omega) safe (by rw [hc]; exact row c) rfl
    have rest:=ih (put T h (some b)) (h+1) (by omega) (by
      intro i lo hi
      have ne : i≠h := by omega
      simp only [put,if_neg ne]
      exact occupied i (by omega) (by omega))
    have whole:=first.append rest
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,paint_next] using whole
private theorem paint_outside {T h w b i} (outside : i < h ∨ h+w ≤ i) : paint T h w b i=T i := by
  have no : ¬(h ≤ i ∧ i < h+w) := by omega
  simp only [paint,if_neg no]
private theorem Grid.painted {D T} (g : Grid D T) (j : Nat) (hj : j < 13) (b : Bool) :
    Grid D (paint T (D j+1) (D (j+1)-D j-1) b) := by
  have rise:=g.rise j hj
  have len : D j+1+(D (j+1)-D j-1)=D (j+1) := by omega
  refine ⟨g.rise,g.mono,?_,?_⟩
  · intro k hk
    have out : D k < D j+1 ∨ D j+1+(D (j+1)-D j-1) ≤ D k := by
      by_cases order : k ≤ j
      · have le:=g.mono k j order (by omega); omega
      · have le:=g.mono (j+1) k (by omega) hk; omega
    rw [paint_outside out];exact g.blank k hk
  · intro k i hk lo hi
    by_cases inside : D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1)
    · exact ⟨b,by simp only [paint,if_pos inside]⟩
    · simp only [paint,if_neg inside];exact g.cells k i hk lo hi
private def ClearRows (j : Nat) (b : Bool) (start out : Fin M.stateCount) : Prop :=
  ∃ e scan back : Fin M.stateCount,Safe e ∧ Safe scan ∧
    RouteR M Safe 0 j start e ∧ RouteL M Safe (j+1) 0 back out ∧
    M.step e none=(scan,none,.right) ∧
    (∀ c,M.step scan (some c)=(scan,some b,.right)) ∧
    M.step scan none=(back,none,.stay)
private theorem clear_run {D T P j b start out} (grid : Grid D T) (hj : j < 13)
    (fit : D 13 ≤ P) (code : ClearRows (Safe:=Safe) j b start out) :
    Path M Safe P (2*(D (j+1)-D 0+j)+2) ⟨start,D 0,T⟩
      ⟨out,D 0,paint T (D j+1) (D (j+1)-D j-1) b⟩ := by
  rcases code with ⟨e,scan,back,se,ss,route,ret,re,rs,rn⟩
  have rise:=grid.rise j hj
  have endpoint : D j+1+(D (j+1)-D j-1)=D (j+1) := by omega
  have room:=le_trans (grid.mono (j+1) 13 (by omega) le_rfl) fit
  have first:=keep e scan (D j) (D j+1) T .right (P:=P) (by omega) (by omega) se (by rw [grid.blank _ (by omega)];exact re) rfl
  have middle:=paint_run scan T (D j+1) (D (j+1)-D j-1) b (P:=P) (by omega) ss (by
    intro i lo hi;exact grid.cells j i hj (by omega) (by omega)) rs
  rw [endpoint] at middle
  let U:=paint T (D j+1) (D (j+1)-D j-1) b
  have gu : Grid D U:=grid.painted j hj b
  have last:=keep scan back (D (j+1)) (D (j+1)) U .stay (P:=P) room room ss (by rw [gu.blank _ (by omega)];exact rn) rfl
  have whole:=(grid.goR route (by omega) fit).append (first.append (middle.append (last.append (gu.goL ret (by omega) fit))))
  convert whole using 1
  have order:=grid.mono 0 (j+1) (by omega) (by omega)
  have before:=grid.mono 0 j (by omega) (by omega)
  omega
private def Unary (D : Nat → Nat) (T : Nat → Option Bool) (j v : Nat) : Prop :=
  ∀ i, D j < i → i < D (j+1) → T i=some (decide (i-D j ≤ v))
private def DecRows (j : Nat) (start zero pos : Fin M.stateCount) : Prop :=
  ∃ e s t l zr pr : Fin M.stateCount, Safe e ∧ Safe s ∧ Safe t ∧ Safe l ∧
    RouteR M Safe 0 j start e ∧ RouteL M Safe j 0 zr zero ∧ RouteL M Safe j 0 pr pos ∧
    M.step e none=(s,none,.right) ∧
    M.step s (some true)=(s,some true,.right) ∧
    (∀ b, b≠some true → M.step s b=(t,b,.left)) ∧
    M.step t none=(zr,none,.stay) ∧
    M.step t (some true)=(l,some false,.left) ∧
    (∀ b, M.step l (some b)=(l,some b,.left)) ∧
    M.step l none=(pr,none,.stay)
private theorem unary_true {D T j v w} (h : Unary D T j v)
    (len : D (j+1)=D j+w+1) (hv : v ≤ w) {i : Nat}
    (lo : D j < i) (hi : i ≤ D j+v) : T i=some true := by
  rw [h i lo (by omega)]
  simp [show i-D j ≤ v by omega]
private theorem unary_boundary {D T j v w} (grid : Grid D T) (h : Unary D T j v)
    (hj : j < 13) (len : D (j+1)=D j+w+1) (hv : v ≤ w) :
    T (D j+v+1)≠some true := by
  by_cases full : v=w
  · rw [full,← len,grid.blank _ (by omega)]; simp
  · rw [h _ (by omega) (by omega)]
    simp [show ¬D j+v+1-D j ≤ v by omega]
private theorem dec_zero {D T j w P start zero pos} (grid : Grid D T)
    (hj : j < 13) (fit : D 13 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j 0) (code : DecRows (Safe:=Safe) j start zero pos) :
    Path M Safe P (2*(D j-D 0+j)+3) ⟨start,D 0,T⟩ ⟨zero,D 0,T⟩ := by
  rcases code with ⟨e,s,t,l,zr,pr,se,ss,st,sl,out,rz,rp,re,rs,rb,rt0,rt1,rl,rn⟩
  have room : D j+1 ≤ P := le_trans (show D j+1 ≤ D (j+1) by omega)
    (le_trans (grid.mono (j+1) 13 (by omega) le_rfl) fit)
  have entry:=keep e s (D j) (D j+1) T .right (P:=P) (by omega) room se (by rw [grid.blank j (by omega)]; exact re) rfl
  have back:=keep s t (D j+1) (D j) T .left (P:=P) room (by omega) ss
    (rb _ (by simpa using unary_boundary grid unary hj len (Nat.zero_le w))) (by simp [dest])
  have take:=keep t zr (D j) (D j) T .stay (P:=P) (by omega) (by omega) st (by rw [grid.blank j (by omega)]; exact rt0) rfl
  have whole:=(grid.goR out (by omega) fit).append (entry.append (back.append (take.append (grid.goL rz (by omega) fit))))
  convert whole using 1
  omega
private theorem dec_positive {D T j w v P start zero pos} (grid : Grid D T)
    (hj : j < 13) (fit : D 13 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (positive : 0 < v) (small : v ≤ w)
    (code : DecRows (Safe:=Safe) j start zero pos) :
    Path M Safe P (2*(D j-D 0+j)+2*v+3) ⟨start,D 0,T⟩
      ⟨pos,D 0,put T (D j+v) (some false)⟩ := by
  rcases code with ⟨e,s,t,l,zr,pr,se,ss,st,sl,out,rz,rp,re,rs,rb,rt0,rt1,rl,rn⟩
  have inRoom : D j+v+1 ≤ P := le_trans (by rw [len]; omega) (le_trans (grid.mono _ _ (by omega) (by omega)) fit)
  have val:=unary_true unary len small (i:=D j+v) (by omega) le_rfl
  let U:=put T (D j+v) (some false)
  have gu : Grid D U := grid.change_some _ true false val
  have entry:=keep e s (D j) (D j+1) T .right (P:=P) (by omega) (by omega) se (by rw [grid.blank j (by omega)]; exact re) rfl
  have sweep:=sweepR s T (D j+1) v (P:=P) (by omega) ss (by
    intro i lo hi
    rw [unary_true unary len small (by omega) (by omega)]
    exact rs)
  rw [show D j+1+v=D j+v+1 by omega] at sweep
  have back:=keep s t (D j+v+1) (D j+v) T .left (P:=P) inRoom (by omega) ss
    (rb _ (unary_boundary grid unary hj len small)) (by simp [dest])
  have take:=hop t l (D j+v) (D j+(v-1)) T (some false) .left (P:=P) (by omega) (by omega) st (by rw [val]; exact rt1) (by simp only [dest];omega)
  have retreat:=sweepL l U (D j) (v-1) (P:=P) (by omega) sl (by
    intro i lo hi
    obtain ⟨b,hb⟩:=gu.cells j i hj lo (by omega)
    rw [hb]; exact rl b)
  have exit:=keep l pr (D j) (D j) U .stay (P:=P) (by omega) (by omega) sl (by rw [gu.blank j (by omega)]; exact rn) rfl
  have whole:=(grid.goR out (by omega) fit).append (entry.append (sweep.append (back.append (take.append (retreat.append (exit.append (gu.goL rp (by omega) fit)))))))
  convert whole using 1
  omega

private def IncRows (j : Nat) (start out : Fin M.stateCount) : Prop :=
  ∃ e s l pr : Fin M.stateCount, Safe e ∧ Safe s ∧ Safe l ∧
    RouteR M Safe 0 j start e ∧ RouteL M Safe j 0 pr out ∧
    M.step e none=(s,none,.right) ∧
    M.step s (some true)=(s,some true,.right) ∧
    M.step s (some false)=(l,some true,.left) ∧
    (∀ b, M.step l (some b)=(l,some b,.left)) ∧
    M.step l none=(pr,none,.stay)
private theorem inc_success {D T j w v P start out} (grid : Grid D T)
    (hj : j < 13) (fit : D 13 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (small : v < w) (code : IncRows (Safe:=Safe) j start out) :
    Path M Safe P (2*(D j-D 0+j)+2*v+3) ⟨start,D 0,T⟩
      ⟨out,D 0,put T (D j+v+1) (some true)⟩ := by
  rcases code with ⟨e,s,l,pr,se,ss,sl,route,back,re,rs,rt,rl,rn⟩
  have inRoom : D j+v+1 ≤ P := le_trans (show D j+v+1 ≤ D (j+1) by omega)
    (le_trans (grid.mono (j+1) 13 (by omega) le_rfl) fit)
  have val : T (D j+v+1)=some false := by
    rw [unary _ (by omega) (by omega)]
    simp [show ¬D j+v+1-D j ≤ v by omega]
  let U:=put T (D j+v+1) (some true)
  have gu : Grid D U := grid.change_some _ false true val
  have entry:=keep e s (D j) (D j+1) T .right (P:=P) (by omega) (by omega) se (by rw [grid.blank j (by omega)]; exact re) rfl
  have sweep:=sweepR s T (D j+1) v (P:=P) (by omega) ss (by
    intro i lo hi
    rw [unary_true unary len (by omega) (by omega) (by omega)]
    exact rs)
  rw [show D j+1+v=D j+v+1 by omega] at sweep
  have take:=hop s l (D j+v+1) (D j+v) T (some true) .left (P:=P) inRoom (by omega) ss (by rw [val]; exact rt) (by simp [dest])
  have retreat:=sweepL l U (D j) v (P:=P) (by omega) sl (by
    intro i lo hi
    obtain ⟨b,hb⟩:=gu.cells j i hj lo (by omega)
    rw [hb]; exact rl b)
  have exit:=keep l pr (D j) (D j) U .stay (P:=P) (by omega) (by omega) sl (by rw [gu.blank j (by omega)]; exact rn) rfl
  have whole:=(grid.goR route (by omega) fit).append (entry.append (sweep.append (take.append (retreat.append (exit.append (gu.goL back (by omega) fit))))))
  convert whole using 1
  omega
private def FromHRows (entry out : Fin M.stateCount) : Prop :=
  ∃ paid gap : Fin M.stateCount, Safe entry ∧ Safe paid ∧ Safe gap ∧
    M.step entry none=(paid,none,.right) ∧
    M.step paid (some true)=(paid,some true,.right) ∧
    M.step paid none=(gap,none,.right) ∧
    M.step paid (some false)=(out,some false,.right) ∧
    M.step gap none=(gap,none,.right) ∧
    M.step gap (some false)=(out,some false,.right)
private theorem from_H {H Q F P T entry out} (positive : 0 < Q) (room : H+Q < F)
    (fit : F+1 ≤ P) (tf : T F=some false) (th : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none) (rows : FromHRows (Safe:=Safe) entry out) :
    Path M Safe P (F+1-H) ⟨entry,H,T⟩ ⟨out,F+1,T⟩ := by
  rcases rows with ⟨p,g,se,sp,sg,re,rp,rn,rf,rg,rt⟩
  have one:=keep entry p H (H+1) T .right (P:=P) (by omega) (by omega) se (by rw [th]; exact re) rfl
  have paid:=sweepR p T (H+1) Q (P:=P) (by omega) sp (by
    intro i lo hi; rw [marks i (by omega) (by omega)]; exact rp)
  rw [show H+1+Q=H+Q+1 by omega] at paid
  by_cases adjacent : H+Q+1=F
  · rw [adjacent] at paid
    have last:=keep p out F (F+1) T .right (P:=P) (by omega) fit sp (by rw [tf]; exact rf) rfl
    have whole:=one.append (paid.append last)
    convert whole using 1
    omega
  · have next:=keep p g (H+Q+1) (H+Q+2) T .right (P:=P) (by omega) (by omega) sp (by rw [gap _ (by omega) (by omega)]; exact rn) rfl
    have gs:=sweepR g T (H+Q+2) (F-(H+Q+2)) (P:=P) (by omega) sg (by
      intro i lo hi; rw [gap i (by omega) (by omega)]; exact rg)
    rw [show H+Q+2+(F-(H+Q+2))=F by omega] at gs
    have last:=keep g out F (F+1) T .right (P:=P) (by omega) fit sg (by rw [tf]; exact rt) rfl
    have whole:=one.append (paid.append (next.append (gs.append last)))
    convert whole using 1
    omega
-- Typed ordinary applications to the already checked single-ROM-row theorem.
open Lean Elab Tactic in
private def checkedRows (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Rows 0) "PhysicalCallerClosure") leaf
  let some ci:=e.find? n | throwError "Missing exact row-support constant {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong row-support kind {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing row-support owner"
  unless i.toNat<e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Rows do throwError "Wrong row-support owner"
  logInfo m!"reset-adapter|{actual}|{n}|{ci.type}"
  closeMainGoal `checkedRows (mkConst n (ci.levelParams.map Level.param))
private abbrev native : ∀ k,Fin 3337 → Fin (callerMachine k).stateCount := by run_tac checkedRows "native" "definition"
private abbrev instruction : Nat → Nat := by run_tac checkedRows "instruction" "definition"
private abbrev symbol : Option Bool → Nat := by run_tac checkedRows "symbol" "definition"
private abbrev interpreted : ∀ k,Nat → Fin (callerMachine k).stateCount × Option Bool × Move := by
  run_tac checkedRows "interpreted" "definition"
private theorem literalCode : ∀ (k : Nat) (q : Fin 3337) (b : Option Bool) (c : Nat),
    instruction (3*q.val+symbol b)=c → (callerMachine k).step (native k q) b=interpreted k c := by
  run_tac checkedRows "native_code" "theorem"
private def ns (k i : Nat) : Fin (callerMachine k).stateCount := native k ⟨i%3337,Nat.mod_lt _ (by decide)⟩
private def NativeSafe (k : Nat) (q : Fin (callerMachine k).stateCount) : Prop :=
  (BodyIngress.machine k).stateCount+7500 ≤ q.val ∧ q≠rowsDone k
private theorem ns_safe (k i : Nat) (hi:i<3337) (nd:i≠1432) : NativeSafe k (ns k i) := by
  dsimp only [NativeSafe,ns]
  have eq:(⟨i%3337,Nat.mod_lt _ (by decide)⟩:Fin 3337)=⟨i,hi⟩:=Fin.ext (Nat.mod_eq_of_lt hi)
  rw [eq]
  constructor
  · change (BodyIngress.machine k).stateCount+7500 ≤ (BodyIngress.machine k).stateCount+7500+i
    omega
  · intro bad
    have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+7500+i=(BodyIngress.machine k).stateCount+7500+1432 at values
    omega
-- Proof automation reads only the closed ROM constant and constructs ordinary rfl row proofs.
-- All expression arities/constructors are guarded before indexing; no tactic result is runtime data.
private def natValue? : Lean.Expr → Option Nat
  | .lit (.natVal n)=>some n
  | _=>none
open Lean Elab Tactic Meta in
private def romNumeral (i : Nat) : TacticM Nat := do
  let v←reduce (mkApp (mkConst ``instruction) (mkNatLit i))
  let some n:=natValue? v | throwError "Closed caller ROM did not reduce to a Nat: {v}"
  return n
open Lean Elab Tactic Meta in
private def nativeRow : TacticM Unit := withMainContext do
  let goal←getMainTarget
  unless goal.isAppOfArity ``Eq 3 do throwError "Expected row equality"
  let ga:=goal.getAppArgs
  unless ga.size==3 do throwError "Wrong Eq arity"
  let lhs:=ga[1]!
  unless lhs.isAppOfArity ``UniformTM.step 3 do throwError "Expected literal UniformTM.step"
  let sa:=lhs.getAppArgs
  unless sa.size==3 do throwError "Wrong step arity"
  let q:=sa[1]!
  unless q.isAppOfArity ``ns 2 do throwError "Expected the fixed native-control constructor"
  let qa:=q.getAppArgs
  unless qa.size==2 do throwError "Wrong native-control arity"
  let some i:=natValue? (←whnf qa[1]!) | throwError "Native control must be a literal"
  unless i<3337 do throwError "Native control outside the finite ROM"
  let .fvar kid:=qa[0]! | throwError "Expected the universally quantified fixed k"
  let b:=sa[2]!
  let sym←if b.isAppOfArity ``Option.none 1 then pure 0 else do
    unless b.isAppOfArity ``Option.some 2 do throwError "Expected a literal Option Bool observation"
    let ba:=b.getAppArgs
    unless ba.size==2 do throwError "Wrong some arity"
    if ba[1]!.isConstOf ``Bool.false then pure 1
    else if ba[1]!.isConstOf ``Bool.true then pure 2
    else throwError "Observation Boolean must be literal"
  let c←romNumeral (3*i+sym)
  let ks:TSyntax `term:=⟨mkIdent (←kid.getDecl).userName⟩
  let is:TSyntax `term:=⟨Syntax.mkNumLit (toString i)⟩
  let cs:TSyntax `term:=⟨Syntax.mkNumLit (toString c)⟩
  let bs←PrettyPrinter.delab b
  evalTactic (← `(tactic| exact literalCode $ks ⟨$is,by decide⟩ $bs $cs (by rfl)))
open Lean Elab Tactic Meta in
private def nativeRoute : Nat → TacticM Unit
  | 0=>throwError "Route certificate exceeds the fixed thirteen-field frame"
  | fuel+1=>withMainContext do
    let goal←getMainTarget
    let right:=goal.isAppOfArity ``RouteR 6
    unless right || goal.isAppOfArity ``RouteL 6 do throwError "Expected exact generic route proposition"
    let ga:=goal.getAppArgs
    unless ga.size==6 do throwError "Wrong route arity"
    let some i:=natValue? (←whnf ga[2]!) | throwError "Nonliteral route origin field"
    let some j:=natValue? (←whnf ga[3]!) | throwError "Nonliteral route destination field"
    if i==j then
      if right then evalTactic (← `(tactic| exact RouteR.nil _ _))
      else evalTactic (← `(tactic| exact RouteL.nil _ _))
    else
      unless (if right then i < j else j < i) do throwError "Route direction mismatch"
      let q:=ga[4]!
      unless q.isAppOfArity ``ns 2 do throwError "Expected literal native route entry"
      let qa:=q.getAppArgs
      unless qa.size==2 do throwError "Wrong route entry arity"
      let some e:=natValue? (←whnf qa[1]!) | throwError "Nonliteral route control"
      let .fvar kid:=qa[0]! | throwError "Expected universally quantified fixed k"
      let ec←romNumeral (3*e)
      let scan:=ec/9
      unless ec%9==(if right then 2 else 0) && scan < 3337 do throwError "Bad literal route entry row"
      let sc←romNumeral (3*scan)
      let next:=sc/9
      unless sc%9==1 && next < 3337 do throwError "Bad literal route delimiter row"
      let ks:TSyntax `term:=⟨mkIdent (←kid.getDecl).userName⟩
      let es:TSyntax `term:=⟨Syntax.mkNumLit (toString e)⟩
      let ss:TSyntax `term:=⟨Syntax.mkNumLit (toString scan)⟩
      let qs:TSyntax `term:=⟨Syntax.mkNumLit (toString next)⟩
      if right then
        evalTactic (← `(tactic| refine RouteR.next (s:=ns $ks $ss) (q:=ns $ks $qs)
          (ns_safe $ks $es (by decide) (by decide)) (ns_safe $ks $ss (by decide) (by decide)) ?_ ?_ ?_ ?_))
      else
        evalTactic (← `(tactic| refine RouteL.next (s:=ns $ks $ss) (q:=ns $ks $qs)
          (ns_safe $ks $es (by decide) (by decide)) (ns_safe $ks $ss (by decide) (by decide)) ?_ ?_ ?_ ?_))
      nativeRow
      evalTactic (← `(tactic| intro b; cases b))
      nativeRow
      nativeRow
      nativeRow
      nativeRoute fuel

/-- Actual finite reset entry for the retained anchor tag; no input scalar is encoded here. -/
def resetEntry (k : Nat) (a : Fin 3) : Fin (callerMachine k).stateCount := ns k (#[336,805,1282][a.val]!)
/-- Actual next native control after clearing nodes/remaining/quota/consumed. -/
def resetCopyEntry (k : Nat) (a : Fin 3) : Fin (callerMachine k).stateCount := ns k (#[132,601,1078][a.val]!)
end PhysicalCallerClosure
